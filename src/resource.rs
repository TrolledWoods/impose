use std::collections::{ VecDeque, HashSet, HashMap };
use std::path::PathBuf;

use crate::parser::*;
use crate::types::*;
use crate::code_gen::*;
use crate::code_loc::*;
use crate::scopes::*;
use crate::id::*;
use crate::error::*;
use crate::run::*;
use crate::DEBUG;

create_id!(ResourceId);

#[derive(Debug)]
pub struct Resources {
	compute_queue: VecDeque<ResourceId>,
	uncomputed_resources: HashSet<ResourceId>,
	pub members: IdVec<Option<Resource>, ResourceId>,

	pub code_cache: HashMap<ustr::Ustr, String>,
}

impl Resources {
	pub fn new() -> Self {
		Self {
			members: Default::default(),
			compute_queue: Default::default(),
			uncomputed_resources: Default::default(),

			code_cache: Default::default(),
		}
	}

	pub fn insert(&mut self, resource: Resource) -> ResourceId {
		let id = self.members.push(Some(resource));
		self.uncomputed_resources.insert(id);
		self.compute_queue.push_back(id);

		id
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
				},
				ResourceKind::Function(ResourceFunction::Defined(ast, arguments)) => {
					// TODO: Maybe we should get rid of this state?
					member.kind = ResourceKind::Function(ResourceFunction::Typing(ast, AstTyper::new(), arguments));
					self.return_resource(member_id, member);
					self.compute_queue.push_back(member_id);
				}
				ResourceKind::Function(ResourceFunction::Typing(mut ast, mut typer, arguments)) => {
					match typer.try_type_ast(types, &mut ast, scopes, self) {
						Ok(Some(dependency)) => {
							member.kind = ResourceKind::Function(
								ResourceFunction::Typing(ast, typer, arguments)
							);
							self.add_dependency(member_id, dependency, scopes);
							member.depending_on = Some(dependency);
							self.return_resource(member_id, member);
							return Ok(true);
						}
						Ok(None) => {}
						Err(()) => {
							member.kind = ResourceKind::Poison;
							self.return_resource(member_id, member);
							return Ok(true);
						}
					}

					let arg_types = arguments.iter().map(|&arg| {
						scopes.member(arg).type_.unwrap()
					}).collect();

					member.type_ = 
						ast.nodes.last().unwrap().type_.map(|return_type| {
							types.insert(Type::new(TypeKind::FunctionPointer {
								args: arg_types,
								returns: return_type,
							}))
						});

					self.resolve_dependencies(&mut member.waiting_on_type);
					member.kind = ResourceKind::Function(ResourceFunction::Typed(ast));
					self.return_resource(member_id, member);
					self.compute_queue.push_back(member_id);
				}
				ResourceKind::Function(ResourceFunction::Typed(mut ast)) => {
					let (locals, instructions, return_value) 
						= match compile_expression(&mut ast, scopes, self, types) 
					{
						Ok(value) => value,
						Err(dependency) => {
							self.add_dependency(member_id, dependency, scopes);
							member.kind = ResourceKind::Function(ResourceFunction::Typed(ast));
							member.depending_on = Some(dependency);
							self.return_resource(member_id, member);
							return Ok(true);
						}
					};

					if let Some(mut waiting_on_value) = member.waiting_on_value.take() {
						self.resolve_dependencies(&mut waiting_on_value);
					}

					if DEBUG {
						println!("\n\n--- Resource {} (function) has finished computing! ---", member_id);
						print!("Type: ");
						types.print(resource_type.unwrap());
						println!();
						println!("Instructions: ");
						for instruction in &instructions {
							println!("{:?}", instruction);
						}
					}

					member.kind = ResourceKind::Function(
						 ResourceFunction::Value(
							 std::sync::Arc::new(locals),
							 instructions,
							 return_value
						 )
					);

					self.uncomputed_resources.remove(&member_id);
					self.return_resource(member_id, member);
					self.compute_queue.push_back(member_id);
				}
				ResourceKind::Function(ResourceFunction::Value(_, _, _)) => {
					// Do nothing here.
					self.return_resource(member_id, member);
				}
				ResourceKind::Value(ResourceValue::File { scope, module_folder, file }) => {
					// Combine the paths into one coherent path.
					let mut path = PathBuf::new();
					for sub_path in file.split('\\') {
						path.push(sub_path);
					}
					path.set_extension("im");

					let code = match std::fs::read_to_string(&path) {
						Ok(code) => code,
						Err(err) => {
							member.kind = ResourceKind::Poison;
							error_value!(member, "Cannot load file, because: '{:?}'", err);
							self.return_resource(member_id, member);
							return Ok(true);
						}
					};

					let ast = match parse_code(
						module_folder,
						file,
						&code,
						self,
						scopes,
						scope,
						true,
					) {
						Ok(value) => value,
						Err(()) => {
							self.code_cache.insert(file, code);
							member.kind = ResourceKind::Poison;
							self.return_resource(member_id, member);
							return Ok(true);
						}
					};

					self.code_cache.insert(file, code);

					member.kind = ResourceKind::Value(ResourceValue::Defined(ast));
					self.return_resource(member_id, member);
					self.compute_queue.push_back(member_id);
				}
				ResourceKind::Value(ResourceValue::Defined(ast)) => {
					member.kind = ResourceKind::Value(ResourceValue::Typing(ast, AstTyper::new()));
					self.return_resource(member_id, member);
					self.compute_queue.push_back(member_id);
				}
				ResourceKind::Value(ResourceValue::Typing(mut ast, mut typer)) => {
					match typer.try_type_ast(types, &mut ast, scopes, self) {
						Ok(Some(dependency)) => {
							self.add_dependency(member_id, dependency, scopes);
							member.kind = ResourceKind::Value(ResourceValue::Typing(ast, typer));
							member.depending_on = Some(dependency);
							self.return_resource(member_id, member);
							return Ok(true);
						}
						Ok(None) => { }
						Err(()) => {
							member.kind = ResourceKind::Poison;
							self.return_resource(member_id, member);
							return Ok(true);
						}
					}

					member.type_ = ast.nodes.last().unwrap().type_;
					member.kind = ResourceKind::Value(ResourceValue::Typed(ast));
					self.resolve_dependencies(&mut member.waiting_on_type);
					self.return_resource(member_id, member);
					self.compute_queue.push_back(member_id);
				}
				ResourceKind::Value(ResourceValue::Typed(mut ast)) => {
					let (stack_layout, instructions, return_value) 
						= match compile_expression(&mut ast, scopes, self, types) 
					{
						Ok(value) => value,
						Err(dependency) => {
							self.add_dependency(member_id, dependency, scopes);
							member.depending_on = Some(dependency);
							member.kind = ResourceKind::Value(ResourceValue::Typed(ast));
							self.return_resource(member_id, member);
							return Ok(true);
						}
					};

					// TODO: Go through the type, and change any pointers into resource pointers.
					let mut instance = std::sync::Arc::new(stack_layout).create_instance();
					let value = run_instructions(
						&instructions,
						return_value.as_ref(),
						&mut instance,
						self,
					);

					if let Some(mut waiting_on_value) = member.waiting_on_value.take() {
						self.resolve_dependencies(&mut waiting_on_value);
					}

					if DEBUG {
						println!("\n\n--- Resource {} (value) has finished computing! ---", member_id);
						if let Some(resource_type) = resource_type {
							print!("Type: ");
							types.print(*resource_type);
						}
						println!("Instructions: ");
						for instruction in &instructions {
							println!("{:?}", instruction);
						}

						println!("Value: {:?}", value);
					}

					member.kind = ResourceKind::Value(self.turn_value_into_resource(types, member.type_.unwrap(), &value));

					// We free the instance here so that we can turn the value into a resource
					// first!
					drop(instance);

					self.return_resource(member_id, member);
					self.uncomputed_resources.remove(&member_id);
				}
				ResourceKind::Value(ResourceValue::Value(_, _, _, _)) => {
					// Do nothing
					self.return_resource(member_id, member);
				}
				ResourceKind::String(ref content) => { 
					if DEBUG {
						println!("\n\n--- Resource {} (string) has finished computing! ---", member_id);
						println!("'{:?}", content);
					}

					self.return_resource(member_id, member);
					self.uncomputed_resources.remove(&member_id);
				}
				ResourceKind::ExternalFunction { .. } => {
					self.return_resource(member_id, member);
					self.uncomputed_resources.remove(&member_id);
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
		&mut self, types: &Types, type_: TypeId, value: &[u8],
	) -> ResourceValue {
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
				let value_after_pointer = unsafe {
					*(&value[pointer_in_type.offset] as *const u8 as *const *const u8)
				};

				let n_elements = match pointer_in_type.size_offset {
					Some(size_offset) =>
						usize::from_le_bytes((&value[size_offset .. size_offset+8]).try_into().unwrap()),
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
					println!("Some resource has pointer to {:?}, so created resource", slice_at_pointer);
				}

				let kind = self.turn_value_into_resource(
					types,
					pointer_in_type.type_behind_pointer,
					slice_at_pointer
				);

				let id = self.insert_done(Resource {
					depending_on: None,
					scope_inside: None,
					loc: CodeLoc { file: ustr::ustr("no"), column: 1, line: 1, },
					type_: Some(pointer_in_type.type_behind_pointer),
					waiting_on_type: Vec::new(),
					waiting_on_value: None,
					kind: ResourceKind::Value(kind),
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

		let n_sub_element = if type_handle.size > 0 { value.len() / type_handle.size } else { 0 };

		ResourceValue::Value(type_handle, n_sub_element, value.into(), resource_pointers)
	}

	pub fn check_completion(&self) {
		if self.uncomputed_resources.len() > 0 {
			for uncomputed_resource_id in self.uncomputed_resources.iter().copied() {
				let resource = self.resource(uncomputed_resource_id);

				match resource.depending_on {
					Some(Dependency::Constant(loc, _)) => {
						error_value!(loc, "Unknown identifier");
					}
					Some(Dependency::Type(loc, depending_on)) => {
						info!(self.resource(depending_on).loc, "Type of this is needed");
						error_value!(loc, "Needs a type that cannot be calculated");
					}
					Some(Dependency::Value(loc, depending_on)) => {
						info!(self.resource(depending_on).loc, "Value of this is needed");
						error_value!(loc, "Needs a value that cannot be calculated");
					}
					None => {
						error_value!(resource.loc, "Value cannot be computed, got forgotten for some reason");
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
	fn add_dependency(&mut self, dependant: ResourceId, dependency: Dependency, scopes: &mut Scopes) {
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
				if depending_on.type_.is_none() {
					depending_on.waiting_on_type.push(dependant);
				} else {
					self.compute_queue.push_back(dependant);
					return;
				}
			}
			Dependency::Value(_, resource_id) => {
				let depending_on = self.resource_mut(resource_id);
				if let Some(ref mut waiting_on_value) = depending_on.waiting_on_value {
					waiting_on_value.push(dependant);
				} else {
					self.compute_queue.push_back(dependant);
					return;
				}
			}
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
		assert!(member.is_none(), "Cannot return resource when member is not taken");
		*member = Some(resource);
	}

	pub fn resource(&self, id: ResourceId) -> &Resource {
		self.members.get(id).as_ref().expect("Resource is taken")
	}

	pub fn resource_mut(&mut self, id: ResourceId) -> &mut Resource {
		self.members.get_mut(id).as_mut().expect("Resource is taken")
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
		module_folder: ustr::Ustr, 
		file: ustr::Ustr
	},
	Defined(Ast),
	Typing(Ast, AstTyper),
	Typed(Ast),
	// TODO: When code generation can pause, add a state for that.
	// TODO: When evaluating can pause, add a state for that.
	
	/// The last field is a list of offsets into the ConstBuffer that are actually pointers to other
	/// resources. These pointers should get set whenever loading the resource to appropriate
	/// pointers(may have to be done by creating local variables).
	/// It is a little unfortunate that we may have to do an almost full deep copy whenever loading
	/// a constant as a pointer, but that might be necessary. Not sure how to reliably make it work
	/// in any other way.
	// TODO: Don't create a local variable if the value does not contain any pointers
	// on its own.
	Value(TypeHandle, usize, crate::stack_frame::ConstBuffer, Vec<(usize, ResourceId, TypeHandle)>),
}

pub enum ResourceFunction {
	Defined(Ast, Vec<ScopeMemberId>),
	Typing(Ast, AstTyper, Vec<ScopeMemberId>),
	Typed(Ast),
	Value(
		std::sync::Arc<crate::stack_frame::StackFrameLayout>,
		Vec<Instruction>, 
		Option<crate::stack_frame::Value>,
	),
}

pub enum ResourceKind {
	ExternalFunction {
		// TODO: Make a more advanced interface to call external functions
		func: Box<dyn Fn(&Resources, &[u8], &mut [u8])>,
		n_arg_bytes: usize,
		n_return_bytes: usize,
	},
	Function(ResourceFunction),
	String(String),
	Value(ResourceValue),
	Poison,
}

impl std::fmt::Debug for ResourceKind {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match self {
			ResourceKind::ExternalFunction { .. } => write!(f, "extern func"),
			ResourceKind::Function { .. } => write!(f, "func"),
			ResourceKind::String(_) => write!(f, "string"),
			ResourceKind::Value { .. } => write!(f, "value"),
			ResourceKind::Poison => write!(f, "poison"),
		}
	}
}
