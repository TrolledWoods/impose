use std::collections::{HashMap, HashSet, VecDeque};
use std::path::PathBuf;

use crate::code_loc::*;
use crate::error::*;
use crate::id::*;
use crate::parser::*;
use crate::scopes::*;
use crate::types::*;
use crate::DEBUG;

create_id!(ResourceId);

pub struct Resources {
    compute_queue: VecDeque<ResourceId>,
    uncomputed_resources: HashSet<ResourceId>,

    pub members: IdVec<Option<Resource>, ResourceId>,
    pub functions: Vec<FunctionKind>,

    pub code_cache: HashMap<ustr::Ustr, String>,
}

impl Resources {
    pub fn new() -> Self {
        Self {
            members: Default::default(),
            compute_queue: Default::default(),
            uncomputed_resources: Default::default(),

            functions: Vec::new(),

            code_cache: Default::default(),
        }
    }

    pub fn insert(&mut self, resource: Resource) -> ResourceId {
        let id = self.members.push(Some(resource));
        self.uncomputed_resources.insert(id);
        self.compute_queue.push_back(id);

        id
    }

    fn insert_function(&mut self, function: FunctionKind) -> usize {
        // TODO: Find some way to unify this function with create_function?
        let id = self.functions.len();
        self.functions.push(function);
        id
    }

    pub fn create_function(&mut self, function: FunctionKind) -> ResourceKind {
        let id = self.functions.len();
        self.functions.push(function);

        ResourceKind::Done((&id.to_le_bytes() as &[u8]).into(), vec![])
    }

    pub fn insert_done(&mut self, resource: Resource) -> ResourceId {
        self.members.push(Some(resource))
    }

    /// Tries to compute one value. Returns an error if there is an error, or if
    /// the compute_queue is empty but there are still uncomputed resources
    pub fn compute_one(&mut self, types: &mut Types, scopes: &mut Scopes) -> Result<bool, ()> {
        if let Some(member_id) = self.compute_queue.pop_front() {
            let mut member = self.use_resource(member_id);
            let resource_type = &mut member.type_;

            match member.kind {
                ResourceKind::Poison => {
                    self.return_resource(member_id, member);
                }
                ResourceKind::Function(ResourceFunction::Defined { ast, args, returns }) => {
                    let mut arg_types = Vec::new();
                    for &(scope_member_id, depending_on) in args.iter() {
                        match self.resource(depending_on) {
                            Resource {
                                type_: Some(TYPE_TYPE_ID),
                                kind: ResourceKind::Done(data, _),
                                ..
                            } => {
                                use std::convert::TryInto;
                                let type_ = TypeId::create(u64::from_le_bytes(
                                    data.as_slice().try_into().unwrap(),
                                )
                                    as u32);
                                arg_types.push(type_);
                                scopes.member_mut(scope_member_id).type_ = Some(type_);
                            }
                            Resource {
                                type_: Some(_),
                                kind: ResourceKind::Done(_, _),
                                ..
                            } => unreachable!(),
                            _ => {
                                member.kind = ResourceKind::Function(ResourceFunction::Defined {
                                    ast,
                                    args,
                                    returns,
                                });
                                let loc = member.loc;
                                member.depending_on = Some(Dependency::Value(loc, depending_on));
                                self.return_resource(member_id, member);
                                self.add_dependency(
                                    member_id,
                                    Dependency::Value(loc, depending_on),
                                    scopes,
                                );
                                return Ok(true);
                            }
                        }
                    }

                    let return_type = match returns {
                        Some(resource_id) => match self.resource(resource_id) {
                            Resource {
                                type_: Some(TYPE_TYPE_ID),
                                kind: ResourceKind::Done(data, _),
                                ..
                            } => {
                                use std::convert::TryInto;
                                TypeId::create(u64::from_le_bytes(
                                    data.as_slice().try_into().unwrap(),
                                ) as u32)
                            }
                            Resource {
                                type_: Some(_),
                                kind: ResourceKind::Done(_, _),
                                ..
                            } => unreachable!(),
                            _ => {
                                member.kind = ResourceKind::Function(ResourceFunction::Defined {
                                    ast,
                                    args,
                                    returns,
                                });
                                let loc = member.loc;
                                member.depending_on = Some(Dependency::Value(loc, resource_id));
                                self.return_resource(member_id, member);
                                self.add_dependency(
                                    member_id,
                                    Dependency::Value(loc, resource_id),
                                    scopes,
                                );
                                return Ok(true);
                            }
                        },
                        None => EMPTY_TYPE_ID,
                    };

                    member.kind = ResourceKind::Function(ResourceFunction::Typing {
                        typer: AstTyper::new(ast.locals.clone()),
                        ast,
                        args: arg_types,
                        returns: return_type,
                    });
                    self.return_resource(member_id, member);
                    self.compute_queue.push_back(member_id);
                }
                ResourceKind::Function(ResourceFunction::Typing {
                    mut ast,
                    mut typer,
                    args,
                    returns,
                }) => {
                    match typer.try_type_ast(types, &mut ast, scopes, self) {
                        Ok(Some(dependency)) => {
                            member.kind = ResourceKind::Function(ResourceFunction::Typing {
                                ast,
                                typer,
                                args,
                                returns,
                            });
                            member.depending_on = Some(dependency);
                            self.return_resource(member_id, member);
                            self.add_dependency(member_id, dependency, scopes);
                            return Ok(true);
                        }
                        Ok(None) => {}
                        Err(()) => {
                            member.kind = ResourceKind::Poison;
                            self.return_resource(member_id, member);
                            self.make_resource_poison(member_id);
                            return Ok(true);
                        }
                    }

                    let returns = match combine_types(
                        &member.loc,
                        types,
                        returns,
                        typer.ast.nodes.last().unwrap().type_,
                    ) {
                        Ok(returns) => returns,
                        Err(()) => {
                            member.kind = ResourceKind::Poison;
                            self.return_resource(member_id, member);
                            self.make_resource_poison(member_id);
                            return Ok(true);
                        }
                    };

                    member.type_ =
                        Some(types.insert(Type::new(TypeKind::FunctionPointer { args, returns })));

                    self.resolve_dependencies(&mut member.waiting_on_type);
                    member.kind = ResourceKind::Function(ResourceFunction::Typed(typer.ast));
                    self.return_resource(member_id, member);
                    self.compute_queue.push_back(member_id);
                }
                ResourceKind::Function(ResourceFunction::Typed(ast)) => {
                    if DEBUG {
                        println!(
                            "\n\n--- Resource {} (function) has finished computing! ---",
                            member_id
                        );
                        print!("Type: ");
                        types.print(resource_type.unwrap());
                    }

                    let id = self.insert_function(FunctionKind::Function(ast));
                    member.kind = ResourceKind::Done((&id.to_le_bytes() as &[u8]).into(), vec![]);

                    if let Some(mut waiting_on_value) = member.waiting_on_value.take() {
                        self.resolve_dependencies(&mut waiting_on_value);
                    }

                    self.uncomputed_resources.remove(&member_id);
                    self.return_resource(member_id, member);
                    self.compute_queue.push_back(member_id);
                }
                ResourceKind::Value(ResourceValue::File { scope, ref file }) => {
                    let module_folder = file.parent().unwrap();
                    let code = match std::fs::read_to_string(file) {
                        Ok(code) => code,
                        Err(err) => {
                            member.kind = ResourceKind::Poison;
                            error_value!(member, "Cannot load file, because: '{:?}'", err);
                            self.return_resource(member_id, member);
                            self.make_resource_poison(member_id);
                            return Ok(true);
                        }
                    };

                    let ast = match parse_code(
                        &module_folder,
                        file,
                        &code,
                        self,
                        scopes,
                        types,
                        scope,
                        true,
                    ) {
                        Ok(value) => value,
                        Err(()) => {
                            self.code_cache.insert(file.to_str().unwrap().into(), code);
                            member.kind = ResourceKind::Poison;
                            self.return_resource(member_id, member);
                            self.make_resource_poison(member_id);
                            return Ok(true);
                        }
                    };

                    self.code_cache.insert(file.to_str().unwrap().into(), code);

                    member.kind = ResourceKind::Value(ResourceValue::Defined(ast));
                    self.return_resource(member_id, member);
                    self.compute_queue.push_back(member_id);
                }
                ResourceKind::Value(ResourceValue::Defined(ast)) => {
                    let locals = ast.locals.clone();
                    member.kind =
                        ResourceKind::Value(ResourceValue::Typing(ast, AstTyper::new(locals)));
                    self.return_resource(member_id, member);
                    self.compute_queue.push_back(member_id);
                }
                ResourceKind::Value(ResourceValue::Typing(mut ast, mut typer)) => {
                    match typer.try_type_ast(types, &mut ast, scopes, self) {
                        Ok(Some(dependency)) => {
                            member.kind = ResourceKind::Value(ResourceValue::Typing(ast, typer));
                            member.depending_on = Some(dependency);
                            self.return_resource(member_id, member);
                            self.add_dependency(member_id, dependency, scopes);
                            return Ok(true);
                        }
                        Ok(None) => {}
                        Err(()) => {
                            member.kind = ResourceKind::Poison;
                            self.return_resource(member_id, member);
                            self.make_resource_poison(member_id);
                            return Ok(true);
                        }
                    }

                    member.type_ = Some(typer.ast.nodes.last().unwrap().type_);
                    // TODO: Make this taking of the ast a little more convenient maybe?
                    member.kind = ResourceKind::Value(ResourceValue::Typed(typer.ast));
                    self.resolve_dependencies(&mut member.waiting_on_type);
                    self.return_resource(member_id, member);
                    self.compute_queue.push_back(member_id);
                }
                ResourceKind::Value(ResourceValue::Typed(ast)) => {
                    use crate::backend::interp;
                    let mut interpreter = interp::Interpreter::new();
                    let value = interpreter
                        .interpret(self, types, scopes, &ast, None.into_iter())
                        .unwrap();

                    if DEBUG {
                        println!(
                            "\n\n--- Resource {} (value) has finished computing! ---",
                            member_id
                        );
                        if let Some(resource_type) = resource_type {
                            print!("Type: ");
                            types.print(*resource_type);
                        }

                        println!("\nValue: {:?}", value);
                    }

                    member.kind =
                        self.turn_value_into_resource(types, member.type_.unwrap(), &value);

                    let mut waiting_on_value = member.waiting_on_value.take().unwrap();
                    self.return_resource(member_id, member);
                    self.resolve_dependencies(&mut waiting_on_value);
                    self.uncomputed_resources.remove(&member_id);
                }
                ResourceKind::Done(_, _) => {
                    // Do nothing
                    self.return_resource(member_id, member);
                }
            }

            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Turns a value into a resource, by making pointers into resources.
    /// TODO: We may not want to do this in here. It's like putting a bit safety hole in the
    /// middle of the compiler. Maybe later we should put all the unsafe stuff in some
    /// module somewhere and thing more neatly about how to deal with it?
    fn turn_value_into_resource(
        &mut self,
        types: &Types,
        type_: TypeId,
        value: &[u8],
    ) -> ResourceKind {
        let mut pointers_in_type = Vec::new();
        types.get_pointers_in_type(type_, &mut pointers_in_type, 0);

        let type_handle = types.handle(type_);

        let mut resource_pointers = Vec::new();
        for pointer_in_type in pointers_in_type {
            let pointer_type_handle = types.handle(pointer_in_type.type_behind_pointer);

            for (index, value) in value.chunks_exact(type_handle.size).enumerate() {
                use std::convert::TryInto;

                // SAFETY: This may be uninitialized memory or garbage
                // if the person writing the impose program doesn't know what they are doing.
                // In that case, the compiler might crash! But the language we are running is not
                // safe, so I don't care in this case.
                let value_after_pointer =
                    unsafe { *(&value[pointer_in_type.offset] as *const u8 as *const *const u8) };

                let n_elements = match pointer_in_type.size_offset {
                    Some(size_offset) => usize::from_le_bytes(
                        (&value[size_offset..size_offset + 8]).try_into().unwrap(),
                    ),
                    None => 1,
                };

                // SAFETY: No safety here :/
                let slice_at_pointer = unsafe {
                    std::slice::from_raw_parts(
                        value_after_pointer.wrapping_add(index * pointer_type_handle.size),
                        pointer_type_handle.size * n_elements,
                    )
                };

                if DEBUG {
                    println!(
                        "Some resource has pointer to {:?}, so created resource",
                        slice_at_pointer
                    );
                }

                let kind = self.turn_value_into_resource(
                    types,
                    pointer_in_type.type_behind_pointer,
                    slice_at_pointer,
                );

                let id = self.insert_done(Resource {
                    depending_on: None,
                    scope_inside: None,
                    loc: CodeLoc {
                        file: ustr::ustr("no"),
                        column: 1,
                        line: 1,
                    },
                    type_: Some(pointer_in_type.type_behind_pointer),
                    waiting_on_type: Vec::new(),
                    waiting_on_value: None,
                    kind,
                });

                if DEBUG {
                    println!("Resource is {:?}", id);
                }

                resource_pointers.push((
                    pointer_in_type.offset + index * type_handle.size,
                    id,
                    pointer_type_handle,
                ));
            }
        }

        ResourceKind::Done(value.into(), resource_pointers)
    }

    pub fn check_completion(&mut self) {
        if self.uncomputed_resources.len() > 0 {
            let uncomputed_resources =
                std::mem::replace(&mut self.uncomputed_resources, HashSet::new());

            // Make all the unknown identifier poison first, because unknown identifiers
            // are not usually errors(they may appear later), so we need to make them errors
            // when the compilation process is over.
            for uncomputed_resource_id in uncomputed_resources.iter() {
                let resource = self.resource(*uncomputed_resource_id);

                match resource.depending_on {
                    Some(Dependency::Constant(_, _)) => {
                        self.make_resource_poison(*uncomputed_resource_id);
                    }
                    _ => (),
                }
            }

            for uncomputed_resource_id in uncomputed_resources {
                let resource = self.resource(uncomputed_resource_id);

                match resource.depending_on {
                    Some(Dependency::Constant(loc, _)) => {
                        error_value!(loc, "Unknown identifier");
                    }
                    Some(Dependency::Type(loc, depending_on)) => {
                        if !matches!(self.resource(depending_on).kind, ResourceKind::Poison) {
                            info!(self.resource(depending_on).loc, "Type of this is needed");
                            error_value!(loc, "Needs a type that cannot be calculated");
                        }
                    }
                    Some(Dependency::Value(loc, depending_on)) => {
                        if !matches!(self.resource(depending_on).kind, ResourceKind::Poison) {
                            info!(self.resource(depending_on).loc, "Value of this is needed");
                            error_value!(loc, "Needs a value that cannot be calculated");
                        }
                    }
                    None => {
                        if !matches!(
                            self.resource(uncomputed_resource_id).kind,
                            ResourceKind::Poison
                        ) {
                            error_value!(resource.loc, "Value cannot be computed, got forgotten for some reason(Internal compiler error)");
                        }
                    }
                }
            }
        }
    }

    /// Adds a dependency on something for a resource. Once that dependency is resolved, the
    /// dependant will be pushed onto the compute queue again to resume evaluation.
    ///
    /// This function DOES NOT set the depending_on value, because this function may be called
    /// while a resource is taken, and in that case it can't set that flag.
    fn add_dependency(
        &mut self,
        dependant: ResourceId,
        dependency: Dependency,
        scopes: &mut Scopes,
    ) {
        match dependency {
            Dependency::Constant(_, scope_member_id) => {
                if let ScopeMemberKind::UndefinedDependency(ref mut dependants) =
                    scopes.member_mut(scope_member_id).kind
                {
                    dependants.push(dependant);
                } else {
                    self.compute_queue.push_back(dependant);
                    return;
                }
            }
            Dependency::Type(_, resource_id) => {
                let depending_on = self.resource_mut(resource_id);
                if let ResourceKind::Poison = depending_on.kind {
                    // It's depending on poison, so spread the poison! Muhahaha
                    self.resource_mut(dependant).kind = ResourceKind::Poison;
                } else {
                    if depending_on.type_.is_none() {
                        depending_on.waiting_on_type.push(dependant);
                    } else {
                        self.compute_queue.push_back(dependant);
                        return;
                    }
                }
            }
            Dependency::Value(_, resource_id) => {
                let depending_on = self.resource_mut(resource_id);
                if let ResourceKind::Poison = depending_on.kind {
                    // It's depending on poison, so spread the poison! Muhahaha
                    self.resource_mut(dependant).kind = ResourceKind::Poison;
                } else {
                    if let Some(ref mut waiting_on_value) = depending_on.waiting_on_value {
                        waiting_on_value.push(dependant);
                    } else {
                        self.compute_queue.push_back(dependant);
                        return;
                    }
                }
            }
        }
    }

    pub fn make_resource_poison(&mut self, resource_id: ResourceId) {
        let resource = self.resource_mut(resource_id);
        resource.kind = ResourceKind::Poison;
        let mut dependants = std::mem::replace(&mut resource.waiting_on_type, Vec::new());
        if let Some(ref mut waiting_on_value) = resource.waiting_on_value {
            dependants.append(waiting_on_value);
        }

        for dependant in dependants {
            self.make_resource_poison(dependant);
        }
    }

    pub fn resolve_dependencies(&mut self, dependencies: &mut Vec<ResourceId>) {
        for resource_id in dependencies.drain(..) {
            self.resource_mut(resource_id).depending_on = None;
            self.compute_queue.push_back(resource_id);
        }
    }

    pub fn use_resource(&mut self, id: ResourceId) -> Resource {
        let resource = self.members.get_mut(id);
        resource.take().expect("Resource is taken")
    }

    pub fn return_resource(&mut self, id: ResourceId, resource: Resource) {
        let member = self.members.get_mut(id);
        assert!(
            member.is_none(),
            "Cannot return resource when member is not taken"
        );
        *member = Some(resource);
    }

    pub fn resource(&self, id: ResourceId) -> &Resource {
        self.members.get(id).as_ref().expect("Resource is taken")
    }

    pub fn resource_mut(&mut self, id: ResourceId) -> &mut Resource {
        self.members
            .get_mut(id)
            .as_mut()
            .expect("Resource is taken")
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Dependency {
    /// We depend on some ScopeMember that isn't defined yet, presumably a constant, but it could
    /// be a local too if all we want is the type.
    Constant(CodeLoc, ScopeMemberId),
    Type(CodeLoc, ResourceId),
    Value(CodeLoc, ResourceId),
}

#[derive(Debug)]
pub struct Resource {
    pub depending_on: Option<Dependency>,
    // TODO: Make this option
    pub loc: CodeLoc,
    pub kind: ResourceKind,
    pub type_: Option<TypeId>,
    pub scope_inside: Option<ScopeId>,
    pub waiting_on_type: Vec<ResourceId>,
    /// This is Some when the value has not been calculated yet,
    /// but None when it has been calculated, so that we cannot add more dependencies
    /// after it's been calulated and fail compilation for no reason.
    pub waiting_on_value: Option<Vec<ResourceId>>,
}

impl Location for Resource {
    fn get_location(&self) -> CodeLoc {
        self.loc.clone()
    }
}

impl Resource {
    pub fn new(loc: CodeLoc, kind: ResourceKind) -> Self {
        Self {
            depending_on: None,
            scope_inside: None,
            loc,
            kind,
            type_: None,
            waiting_on_type: vec![],
            waiting_on_value: Some(vec![]),
        }
    }

    pub fn new_with_scope(loc: CodeLoc, scope: ScopeId, kind: ResourceKind) -> Self {
        Self {
            depending_on: None,
            scope_inside: Some(scope),
            loc,
            kind,
            type_: None,
            waiting_on_type: vec![],
            waiting_on_value: Some(vec![]),
        }
    }

    pub fn new_with_type(loc: CodeLoc, kind: ResourceKind, type_: TypeId) -> Self {
        Self {
            depending_on: None,
            scope_inside: None,
            loc,
            kind,
            type_: Some(type_),
            waiting_on_type: vec![],
            waiting_on_value: Some(vec![]),
        }
    }
}

pub enum ResourceValue {
    /// Lex a file, with a folder where sub modules go.
    File {
        scope: ScopeId,
        file: PathBuf,
    },
    Defined(crate::parser::Ast),
    Typing(crate::parser::Ast, AstTyper),
    Typed(crate::types::Ast),
    // TODO: When code generation can pause, add a state for that.
    // TODO: When evaluating can pause, add a state for that.
}

pub enum ResourceFunction {
    Defined {
        ast: crate::parser::Ast,
        args: Vec<(ScopeMemberId, ResourceId)>,
        returns: Option<ResourceId>,
    },
    Typing {
        ast: crate::parser::Ast,
        typer: AstTyper,
        args: Vec<TypeId>,
        returns: TypeId,
    },
    Typed(crate::types::Ast),
    // TODO: When code generation can pause, add a state for that.
}

pub enum FunctionKind {
    ExternalFunction {
        // TODO: Make a more advanced interface to call external functions
        func: Box<dyn Fn(&Resources, &[u8], &mut [u8])>,
        n_arg_bytes: usize,
        n_return_bytes: usize,
    },
    Function(crate::types::Ast),
}

pub enum ResourceKind {
    Function(ResourceFunction),
    Value(ResourceValue),

    /// The last field is a list of offsets into the ConstBuffer that are actually pointers to other
    /// resources. These pointers should get set whenever loading the resource to appropriate
    /// pointers(may have to be done by creating local variables).
    /// It is a little unfortunate that we may have to do an almost full deep copy whenever loading
    /// a constant as a pointer, but that might be necessary. Not sure how to reliably make it work
    /// in any other way.
    // TODO: Make the value stored in a vector, so that it's always heap allocated, to make sure
    // that it doesn't move and wreck havoc.
    Done(crate::ConstBuffer, Vec<(usize, ResourceId, TypeHandle)>),

    Poison,
}

impl std::fmt::Debug for ResourceKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ResourceKind::Function { .. } => write!(f, "func"),
            ResourceKind::Value { .. } => write!(f, "value"),
            ResourceKind::Done(ref buffer, _) => write!(f, "done {:?}", buffer),
            ResourceKind::Poison => write!(f, "poison"),
        }
    }
}
