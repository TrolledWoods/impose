use crate::intrinsic::*;
use std::collections::HashMap;
// We can't import the parser directly because of name clasing
use crate::align::*;
use crate::code_loc::*;
use crate::error::*;
use crate::id::*;
use crate::operator::*;
use crate::parser;
use crate::resource::*;
use crate::scopes::*;
use crate::ConstBuffer;

pub const TYPE_TYPE_ID: TypeId = TypeId::create_raw(0);
pub const U64_TYPE_ID: TypeId = TypeId::create_raw(1);
pub const U32_TYPE_ID: TypeId = TypeId::create_raw(2);
pub const U16_TYPE_ID: TypeId = TypeId::create_raw(3);
pub const U8_TYPE_ID: TypeId = TypeId::create_raw(4);
pub const S64_TYPE_ID: TypeId = TypeId::create_raw(5);
pub const S32_TYPE_ID: TypeId = TypeId::create_raw(6);
pub const S16_TYPE_ID: TypeId = TypeId::create_raw(7);
pub const S8_TYPE_ID: TypeId = TypeId::create_raw(8);
pub const F64_TYPE_ID: TypeId = TypeId::create_raw(9);
pub const F32_TYPE_ID: TypeId = TypeId::create_raw(10);
pub const BOOL_TYPE_ID: TypeId = TypeId::create_raw(11);
pub const EMPTY_TYPE_ID: TypeId = TypeId::create_raw(12);
pub const NEVER_TYPE_ID: TypeId = TypeId::create_raw(13);

create_id!(TypeId);

pub struct Types {
    types: IdVec<Type, TypeId>,
}

impl Default for Types {
    fn default() -> Self {
        Self::new()
    }
}

impl Types {
    pub fn new() -> Self {
        let mut types = IdVec::new();
        assert_eq!(types.push(Type::new(TypeKind::Type)), TYPE_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::U64)), U64_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::U32)), U32_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::U16)), U16_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::U8)), U8_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::S64)), S64_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::S32)), S32_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::S16)), S16_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::S8)), S8_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::F64)), F64_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::F32)), F32_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::Bool)), BOOL_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::EmptyType)), EMPTY_TYPE_ID);
        assert_eq!(types.push(Type::new(TypeKind::NeverType)), NEVER_TYPE_ID);
        Self { types }
    }

    pub fn handle(&self, id: TypeId) -> TypeHandle {
        let type_ = self.types.get(id);
        TypeHandle {
            id,
            size: type_.size,
            align: type_.align,
        }
    }

    pub fn create_tuple(
        &self,
        type_: impl Iterator<Item = Result<TypeId, ()>>,
    ) -> Result<Type, ()> {
        let mut full_member_data = Vec::new();
        let mut offset = 0;
        for member in type_ {
            let member_type_id = member?;
            let member_type_handle = self.handle(member_type_id);
            let aligned_off = to_aligned(member_type_handle.align, offset);
            full_member_data.push((aligned_off, member_type_handle));

            offset = aligned_off + member_type_handle.size;
        }

        Ok(Type::new(TypeKind::Tuple(full_member_data)))
    }

    pub fn create_struct(
        &self,
        type_: impl Iterator<Item = Result<(ustr::Ustr, TypeId), ()>>,
    ) -> Result<Type, ()> {
        let mut full_member_data = Vec::new();
        let mut offset = 0;
        for member in type_ {
            let (name, member_type_id) = member?;
            let member_type_handle = self.handle(member_type_id);
            let aligned_off = to_aligned(member_type_handle.align, offset);
            full_member_data.push((name, aligned_off, member_type_handle));

            offset = aligned_off + member_type_handle.size;
        }

        Ok(Type::new(TypeKind::Struct {
            members: full_member_data,
        }))
    }

    pub fn insert(&mut self, type_: Type) -> TypeId {
        // Try to find a type that is already the same.
        for (id, self_type) in self.types.iter_ids() {
            if *self_type == type_ {
                return id;
            }
        }

        self.types.push(type_)
    }

    pub fn insert_function(&mut self, args: Vec<TypeId>, returns: TypeId) -> TypeId {
        let type_ = Type::new(TypeKind::FunctionPointer { args, returns });

        // Try to find a type that is already the same.
        for (id, self_type) in self.types.iter_ids() {
            if *self_type == type_ {
                return id;
            }
        }

        self.types.push(type_)
    }

    /// Pushes to the pointer_inside buffer you passed in the pointers it found inside.
    ///
    /// The layout of the vec is like this: Vec<(
    ///     offset in bytes from type start,
    ///     id of type behind the pointer,
    ///     number of instances of the type behind the pointer(the number of bytes have to be
    ///     calculated by multiplying by the size of the type),
    /// )>
    pub fn get_pointers_in_type(
        &self,
        type_id: TypeId,
        pointers_inside: &mut Vec<PointerInType>,
        offset: usize,
    ) {
        let type_ = self.get(type_id);

        match type_.kind {
            TypeKind::Struct { ref members } => {
                for (_name, member_offset, member_type_handle) in members {
                    self.get_pointers_in_type(
                        member_type_handle.id,
                        pointers_inside,
                        offset + *member_offset,
                    );
                }
            }
            TypeKind::Pointer(type_behind_pointer) => {
                pointers_inside.push(PointerInType {
                    offset,
                    type_behind_pointer,
                    size_offset: None,
                });
            }
            TypeKind::BufferPointer(type_behind_pointer) => {
                pointers_inside.push(PointerInType {
                    offset,
                    type_behind_pointer,
                    size_offset: Some(offset + 8),
                });
            }
            _ => (),
        }
    }

    pub fn get(&self, type_: TypeId) -> &Type {
        self.types.get(type_)
    }

    pub fn get_if(&self, type_: Option<TypeId>) -> Option<&Type> {
        type_.map(|type_| self.types.get(type_))
    }

    pub fn print_types(&self) {
        for (id, _) in self.types.iter_ids() {
            print!("{}: ", id.into_index());
            self.print(id);
            println!();
        }
    }

    pub fn print(&self, type_: TypeId) {
        let mut buffer = Vec::new();
        self.write_type_to_buffer(type_, &mut buffer);
        print!("{}", String::from_utf8(buffer).unwrap());
    }

    pub fn type_to_string(&self, type_: TypeId) -> String {
        let mut buffer = Vec::new();
        self.write_type_to_buffer(type_, &mut buffer);
        String::from_utf8(buffer).unwrap()
    }

    pub fn write_type_to_buffer(&self, type_: TypeId, buffer: &mut impl std::io::Write) {
        match self.types.get(type_).kind {
            TypeKind::NeverType => write!(buffer, "Never").unwrap(),
            TypeKind::EmptyType => write!(buffer, "Empty").unwrap(),
            TypeKind::Type => write!(buffer, "Type").unwrap(),
            TypeKind::BufferPointer(sub_type) => {
                write!(buffer, "&-").unwrap();
                self.write_type_to_buffer(sub_type, buffer);
            }
            TypeKind::Struct { ref members } => {
                write!(buffer, "struct{{ ").unwrap();
                for (i, (name, offset, member)) in members.iter().enumerate() {
                    if i > 0 {
                        write!(buffer, ", ").unwrap();
                    }

                    write!(buffer, "{}[{}]: ", name, offset).unwrap();
                    self.write_type_to_buffer(member.id, buffer);
                }
                write!(buffer, "}}").unwrap();
            }
            TypeKind::Tuple(ref members) => {
                write!(buffer, "(").unwrap();
                for (i, (_, member)) in members.iter().enumerate() {
                    if i > 0 {
                        write!(buffer, ", ").unwrap();
                    }

                    self.write_type_to_buffer(member.id, buffer);
                }
                write!(buffer, ")").unwrap();
            }
            TypeKind::Pointer(sub_type) => {
                write!(buffer, "&").unwrap();
                self.write_type_to_buffer(sub_type, buffer);
            }
            TypeKind::FunctionPointer { ref args, returns } => {
                write!(buffer, "(").unwrap();
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(buffer, ", ").unwrap();
                    }
                    self.write_type_to_buffer(*arg, buffer);
                }
                write!(buffer, ") -> ").unwrap();
                self.write_type_to_buffer(returns, buffer);
            }
            TypeKind::U8 => write!(buffer, "U8").unwrap(),
            TypeKind::U16 => write!(buffer, "U16").unwrap(),
            TypeKind::U32 => write!(buffer, "U32").unwrap(),
            TypeKind::U64 => write!(buffer, "U64").unwrap(),
            TypeKind::S8 => write!(buffer, "S8").unwrap(),
            TypeKind::S16 => write!(buffer, "S16").unwrap(),
            TypeKind::S32 => write!(buffer, "S32").unwrap(),
            TypeKind::S64 => write!(buffer, "S64").unwrap(),
            TypeKind::F32 => write!(buffer, "F32").unwrap(),
            TypeKind::F64 => write!(buffer, "F64").unwrap(),
            TypeKind::Bool => write!(buffer, "Bool").unwrap(),
        }
    }
}

impl Drop for Types {
    fn drop(&mut self) {
        if crate::DEBUG {
            self.print_types();
        }
    }
}

/// Some pointer that is in a type. This is used for deep cloning pointers in values into
/// resources.
pub struct PointerInType {
    pub offset: usize,
    pub type_behind_pointer: TypeId,
    pub size_offset: Option<usize>,
}

/// Contains common info about a type, to avoid having to look too many things up
/// all the time. This handle alone is enough to compare two different types, pass
/// a type to a function, e.t.c.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeHandle {
    pub size: usize,
    pub align: usize,
    pub id: TypeId,
}

#[derive(Debug, PartialEq)]
pub struct Type {
    pub loc: Option<CodeLoc>,
    pub kind: TypeKind,
    pub size: usize,
    pub align: usize,
}

impl Type {
    pub fn new(kind: TypeKind) -> Self {
        let (mut size, align) = match kind {
            TypeKind::Struct { ref members } => {
                let mut align = 1;
                let mut size = 0;
                for &(_, offset, handle) in members {
                    align = align.max(handle.align);
                    size = to_aligned(align, size.max(offset + handle.size));
                }
                (size, align)
            }
            TypeKind::Tuple(ref members) => {
                let mut align = 1;
                let mut size = 0;
                for &(offset, handle) in members {
                    align = align.max(handle.align);
                    size = to_aligned(align, size.max(offset + handle.size));
                }
                (size, align)
            }
            TypeKind::Pointer(_) => (8, 8),
            TypeKind::NeverType => (0, 1),
            TypeKind::BufferPointer(_) => (16, 8),
            TypeKind::EmptyType => (0, 1),
            TypeKind::U64 | TypeKind::S64 | TypeKind::F64 | TypeKind::Type => (8, 8),
            TypeKind::U32 | TypeKind::S32 | TypeKind::F32 => (4, 4),
            TypeKind::U16 | TypeKind::S16 => (2, 2),
            TypeKind::Bool | TypeKind::U8 | TypeKind::S8 => (1, 1),
            TypeKind::FunctionPointer { .. } => (8, 8),
        };

        // Make sure its size is aligned as it should be
        if size & (align - 1) != 0 {
            size = align + (size & !(align - 1));
        }

        Type {
            loc: None,
            kind,
            size,
            align,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
    Struct {
        members: Vec<(ustr::Ustr, usize, TypeHandle)>,
    },
    Tuple(Vec<(usize, TypeHandle)>),
    EmptyType,
    NeverType,
    Pointer(TypeId),
    BufferPointer(TypeId),
    FunctionPointer {
        args: Vec<TypeId>,
        returns: TypeId,
    },
    Type,

    U8,
    U16,
    U32,
    U64,

    S8,
    S16,
    S32,
    S64,

    F64,
    F32,

    Bool,
}

#[derive(Debug)]
pub struct LabelMapValue {
    pub node_id: usize,
    pub stack_len: usize,
}

#[derive(Debug)]
pub struct Ast {
    pub nodes: Vec<Node>,
    pub locals: LocalVariables,
    pub label_map: HashMap<LabelId, LabelMapValue>,
}

impl Ast {
    pub fn new(locals: LocalVariables) -> Self {
        Ast {
            nodes: Vec::new(),
            locals,
            label_map: HashMap::new(),
        }
    }
}

pub type AstNodeId = u32;

#[derive(Debug)]
pub struct Node {
    pub loc: CodeLoc,
    // TODO: Only nodes that need the scope should have it, so put this into the NodeKind enum
    // later.
    pub scope: ScopeId,
    pub kind: NodeKind,
    pub type_: TypeId,
    pub is_lvalue: bool,
    pub stack_len: usize,
}

impl Node {
    fn new(old_node: &parser::Node, new_kind: NodeKind, type_: TypeId, stack_len: usize) -> Self {
        Node {
            loc: old_node.loc,
            kind: new_kind,
            scope: old_node.scope,
            is_lvalue: old_node.is_lvalue,
            // TODO: Remove the option here
            type_,
            stack_len,
        }
    }
}

impl Location for Node {
    fn get_location(&self) -> CodeLoc {
        self.loc
    }
}

#[derive(Debug)]
pub enum NodeKind {
    Marker(parser::MarkerKind),
    MemberAccess {
        offset: usize,
        size: usize,
    },
    Constant(ConstBuffer),

    IntrinsicTwo(IntrinsicKindTwo),

    ScopeMemberReference(ScopeMemberId),
    Identifier(ScopeMemberId),

    BitCast,

    Assign,

    Resource(ResourceId),
    FunctionCall(TypeId),

    Dereference,

    /// # Members
    /// 0: Condition member
    /// 1: Body
    If(LabelId),
    /// # Members
    /// 0: Condition member
    /// 1: True body
    /// 2: False body
    IfWithElse {
        end_label: LabelId,
    },

    Loop(LabelId, LabelId),

    Tuple(usize),
    Struct(usize),

    Declaration {
        variable_name: ScopeMemberId,
    },
    Block {
        contents: Vec<AstNodeId>,
        label: LabelId,
    },
    Skip {
        label: LabelId,
    },
}

#[derive(Debug, Clone, Copy)]
pub struct TypeStackElement {
    type_: TypeId,
    loc: CodeLoc,
    node_id: usize,
}

pub struct AstTyper {
    /// Each element in this corresponds to an ast node.
    /// Once done, this list should be the same length as the ast.
    node_id: usize,
    type_stack: Vec<TypeStackElement>,
    stack_len: usize,

    pub ast: Ast,
}

impl AstTyper {
    pub fn new(local_variables: LocalVariables) -> AstTyper {
        AstTyper {
            node_id: 0,
            type_stack: Vec::new(),
            ast: Ast::new(local_variables),
            stack_len: 0,
        }
    }

    pub fn try_type_ast(
        &mut self,
        types: &mut Types,
        ast: &mut parser::Ast,
        scopes: &mut Scopes,
        resources: &Resources,
    ) -> Result<Option<Dependency>, ()> {
        while self.node_id < ast.nodes.len() {
            let node = &ast.nodes[self.node_id];

            let new_node: Node = match node.kind {
                parser::NodeKind::Assign => {
                    return error!(node, "Assign is generated by typer, cannot be found here")
                }
                parser::NodeKind::IntrinsicTwo(_) => {
                    return error!(node, "For now, the parser cannot output any intrinsics. This will be allowed in the future, however, but for now intrinsics can only be generated by the typer");
                }
                parser::NodeKind::Tuple { n_members } => {
                    let stack_len = self.type_stack.len() - n_members;
                    let member_types = &self.type_stack[stack_len..];
                    let type_ = types.create_tuple(member_types.iter().map(|v| Ok(v.type_)))?;
                    let type_ = types.insert(type_);
                    self.type_stack.truncate(stack_len);
                    self.stack_len -= n_members;
                    self.stack_len += 1;
                    Node::new(node, NodeKind::Tuple(n_members), type_, self.stack_len)
                }
                parser::NodeKind::Struct { ref members } => {
                    let stack_len = self.type_stack.len() - members.len();
                    let member_types = &self.type_stack[stack_len..];
                    let type_ = types.create_struct(
                        members
                            .iter()
                            .zip(member_types)
                            .map(|((name, _), type_)| Ok((*name, type_.type_))),
                    )?;
                    let type_ = types.insert(type_);
                    self.type_stack.truncate(stack_len);

                    self.stack_len -= members.len();
                    self.stack_len += 1;
                    Node::new(node, NodeKind::Struct(members.len()), type_, self.stack_len)
                }
                parser::NodeKind::Marker(parser::MarkerKind::IfElseMiddle {
                    middle_label,
                    end_label,
                }) => {
                    self.stack_len -= 1;
                    self.ast.label_map.insert(
                        middle_label,
                        LabelMapValue {
                            node_id: self.ast.nodes.len() + 1,
                            stack_len: self.stack_len,
                        },
                    );
                    Node::new(
                        node,
                        NodeKind::Marker(parser::MarkerKind::IfElseMiddle {
                            middle_label,
                            end_label,
                        }),
                        self.type_stack.pop().unwrap().type_,
                        self.stack_len + 1,
                    )
                }
                parser::NodeKind::Marker(marker_kind @ parser::MarkerKind::IfElseCondition(_)) => {
                    self.stack_len -= 1;
                    Node::new(
                        node,
                        NodeKind::Marker(marker_kind),
                        self.type_stack.pop().unwrap().type_,
                        self.stack_len,
                    )
                }
                parser::NodeKind::Marker(marker_kind @ parser::MarkerKind::IfCondition(_)) => {
                    self.stack_len -= 1;
                    Node::new(
                        node,
                        NodeKind::Marker(marker_kind),
                        self.type_stack.pop().unwrap().type_,
                        self.stack_len,
                    )
                }
                parser::NodeKind::Marker(parser::MarkerKind::LoopHead(label)) => {
                    self.stack_len += 0;
                    self.ast.label_map.insert(
                        label,
                        LabelMapValue {
                            node_id: self.ast.nodes.len() + 1,
                            stack_len: self.stack_len,
                        },
                    );
                    Node::new(
                        node,
                        NodeKind::Marker(parser::MarkerKind::LoopHead(label)),
                        EMPTY_TYPE_ID,
                        self.stack_len,
                    )
                }
                parser::NodeKind::Number(number) => {
                    self.stack_len += 1;
                    Node::new(
                        node,
                        NodeKind::Constant((number as u64).to_le_bytes().as_slice().into()),
                        U64_TYPE_ID,
                        self.stack_len,
                    )
                }
                parser::NodeKind::Float(number) => {
                    self.stack_len += 1;
                    Node::new(
                        node,
                        NodeKind::Constant(number.to_bits().to_le_bytes().as_slice().into()),
                        F64_TYPE_ID,
                        self.stack_len,
                    )
                }
                parser::NodeKind::MemberAccess(_, sub_name) => {
                    let type_id = self.type_stack.pop().unwrap();
                    let type_kind = &types.get(type_id.type_).kind;
                    let type_kind = match (type_kind, node.is_lvalue) {
						(TypeKind::Pointer(type_id), true) => &types.get(*type_id).kind,
						(ref kind, false) => kind,
						(_, _) => return error!(node, "lvalue cannot contain this type(internal compiler error, should have been caught in parsing step)"),
					};

                    let (type_, offset, size) = match *type_kind {
                        TypeKind::U64 => {
                            if sub_name == "low" {
                                (U32_TYPE_ID, 0, 4)
                            } else if sub_name == "high" {
                                (U32_TYPE_ID, 4, 4)
                            } else {
                                return error!(node, "This member does not exist on U64");
                            }
                        }
                        TypeKind::BufferPointer(sub_type) => {
                            if sub_name == "pointer" {
                                (types.insert(Type::new(TypeKind::Pointer(sub_type))), 0, 8)
                            } else if sub_name == "length" {
                                (U64_TYPE_ID, 8, 8)
                            } else {
                                return error!(node, "This member does not exist on BufferPointer");
                            }
                        }
                        TypeKind::Tuple(ref members) => {
                            if let Some(stripped) = sub_name.strip_prefix("_") {
                                if let Ok(index) = stripped.parse::<usize>() {
                                    if let Some(&(offset, handle)) = members.get(index) {
                                        (handle.id, offset, handle.size)
                                    } else {
                                        return error!(
                                            node,
                                            "The tuple {} only has {} members(tuple members start counting from 0)",
                                            types.type_to_string(type_id.type_),
                                            members.len()
                                        );
                                    }
                                } else {
                                    return error!(
                                        node,
                                        "Tuple members are called '_0', '_1', '_2', e.t.c"
                                    );
                                }
                            } else {
                                return error!(
                                    node,
                                    "Tuple members are called '_0', '_1', '_2', e.t.c"
                                );
                            }
                        }
                        TypeKind::Struct { ref members } => {
                            let mut value = None;
                            for &(name, offset, handle) in members {
                                if name == sub_name {
                                    value = Some((handle.id, offset, handle.size));
                                    break;
                                }
                            }

                            if let Some(value) = value {
                                value
                            } else {
                                return error!(node, "This member does not exist in struct");
                            }
                        }
                        _ => {
                            return error!(
                                node,
                                "Type {} does not have members",
                                types.type_to_string(type_id.type_)
                            )
                        }
                    };

                    if node.is_lvalue {
                        self.stack_len += 1;
                        self.ast.nodes.push(Node::new(
                            node,
                            NodeKind::Constant(offset.to_le_bytes().as_slice().into()),
                            U64_TYPE_ID,
                            self.stack_len,
                        ));
                        self.stack_len -= 1;
                        Node::new(
                            node,
                            NodeKind::IntrinsicTwo(IntrinsicKindTwo::AddI),
                            types.insert(Type::new(TypeKind::Pointer(type_))),
                            self.stack_len,
                        )
                    } else {
                        self.stack_len += 0;
                        Node::new(
                            node,
                            NodeKind::MemberAccess { offset, size },
                            type_,
                            self.stack_len,
                        )
                    }
                }
                parser::NodeKind::Loop(_, body, break_label) => {
                    let _ = self.type_stack.pop().unwrap();
                    // This is 0 and not -1 because the loop pretends to return a value.
                    // This is useful because in some cases it DOES return a value, and if
                    // it doesn't return a value, well, what it says it returns doesn't
                    // actually matter, so it's handy to make it consistant.
                    self.stack_len += 0;
                    self.ast.label_map.insert(
                        break_label,
                        LabelMapValue {
                            node_id: self.ast.nodes.len() + 1,
                            stack_len: self.stack_len - 1,
                        },
                    );
                    Node::new(
                        node,
                        NodeKind::Loop(body, break_label),
                        *self.ast.locals.labels.get(break_label),
                        // Since the loop jumps, this is not the stack length at the end of the
                        // loop, but rather the length at the beginning.
                        self.stack_len - 1,
                    )
                }
                parser::NodeKind::If {
                    condition: _,
                    body: _,
                    end_label,
                } => {
                    let _body = self.type_stack.pop().unwrap();
                    let condition = self.type_stack.pop().unwrap();
                    if condition.type_ != BOOL_TYPE_ID {
                        return error!(
                            condition.loc,
                            "If condition has to be Bool, got {}",
                            types.type_to_string(condition.type_)
                        );
                    }

                    self.stack_len += 0;
                    self.ast.label_map.insert(
                        end_label,
                        LabelMapValue {
                            node_id: self.ast.nodes.len() + 1,
                            stack_len: self.stack_len,
                        },
                    );
                    // If on its own never returns a type
                    Node::new(node, NodeKind::If(end_label), EMPTY_TYPE_ID, self.stack_len)
                }
                parser::NodeKind::IfWithElse { end_label, .. } => {
                    let false_body = self.type_stack.pop().unwrap();
                    let true_body = self.type_stack.pop().unwrap();
                    let condition = self.type_stack.pop().unwrap();

                    if condition.type_ != BOOL_TYPE_ID {
                        return error!(
                            condition.loc,
                            "If condition has to be Bool, got {}",
                            types.type_to_string(condition.type_)
                        );
                    }

                    let return_type =
                        combine_types(node, types, true_body.type_, false_body.type_)?;

                    self.stack_len -= 0;
                    self.ast.label_map.insert(
                        end_label,
                        LabelMapValue {
                            node_id: self.ast.nodes.len(),
                            stack_len: self.stack_len,
                        },
                    );
                    Node::new(
                        node,
                        NodeKind::IfWithElse { end_label },
                        return_type,
                        self.stack_len,
                    )
                }
                parser::NodeKind::Resource(id) => {
                    let resource = resources.resource(id);
                    if let Some(type_) = resource.type_ {
                        self.stack_len += 1;
                        Node::new(node, NodeKind::Resource(id), type_, self.stack_len)
                    } else {
                        return Ok(Some(Dependency::Type(node.loc, id)));
                    }
                }
                parser::NodeKind::EmptyLiteral => {
                    self.stack_len += 1;
                    Node::new(
                        node,
                        NodeKind::Constant(smallvec![]),
                        EMPTY_TYPE_ID,
                        self.stack_len,
                    )
                }
                parser::NodeKind::BitCast {
                    into_type: _,
                    value: _,
                } => {
                    let value = self.type_stack.pop().unwrap();
                    let value_type_handle = types.handle(value.type_);
                    let into = self.type_stack.pop().unwrap();
                    let into_type_handle = types.handle(get_type(types, &self.ast, into)?);

                    if into_type_handle.size != value_type_handle.size {
                        info!(
                            value.loc,
                            "This is {}",
                            types.type_to_string(value_type_handle.id)
                        );
                        info!(
                            into.loc,
                            "This is {}",
                            types.type_to_string(into_type_handle.id)
                        );
                        return error!(node, "You can only bitcast types with the same size");
                    }

                    self.stack_len -= 1;
                    Node::new(node, NodeKind::BitCast, into_type_handle.id, self.stack_len)
                }
                parser::NodeKind::Identifier {
                    source: mut id,
                    const_members: ref sub_members,
                    is_type,
                } => {
                    for sub_member_name in sub_members {
                        let member = scopes.member(id);
                        match member.kind {
                            ScopeMemberKind::Constant(constant_id) => {
                                if let Some(scope_inside) =
                                    resources.resource(constant_id).scope_inside
                                {
                                    id = scopes
                                        .find_or_create_temp(scope_inside, *sub_member_name)?;
                                } else {
                                    return error!(node, "This value does not contain a scope");
                                }
                            }
                            ScopeMemberKind::UndefinedDependency(_) => {
                                return Ok(Some(Dependency::Constant(node.loc, id)));
                            }
                            _ => {
                                return error!(node, "Can only do a constant member on a constant");
                            }
                        }
                    }

                    let member = scopes.member(id);
                    if !is_type {
                        match member.kind {
                            ScopeMemberKind::LocalVariable => {
                                if let Some(type_) = member.type_ {
                                    if !node.is_lvalue {
                                        self.stack_len += 1;
                                        Node::new(
                                            node,
                                            NodeKind::Identifier(id),
                                            type_,
                                            self.stack_len,
                                        )
                                    } else {
                                        self.stack_len += 1;
                                        Node::new(
                                            node,
                                            NodeKind::ScopeMemberReference(id),
                                            types.insert(Type::new(TypeKind::Pointer(type_))),
                                            self.stack_len,
                                        )
                                    }
                                } else {
                                    return error!(node, "Type is not assigned, is the variable not declared? (This is probably a compiler problem)");
                                }
                            }
                            ScopeMemberKind::Constant(resource_id) => {
                                if let Some(type_) = resources.resource(resource_id).type_ {
                                    self.stack_len += 1;
                                    Node::new(
                                        node,
                                        NodeKind::Resource(resource_id),
                                        type_,
                                        self.stack_len,
                                    )
                                } else {
                                    return Ok(Some(Dependency::Type(node.loc, resource_id)));
                                }
                            }
                            ScopeMemberKind::UndefinedDependency(_) => {
                                return Ok(Some(Dependency::Constant(node.loc, id)));
                            }
                            ScopeMemberKind::Label => {
                                return error!(node, "This is not a variable, it is a label!");
                            }
                            ScopeMemberKind::Indirect(_) => {
                                unreachable!("scope.member function should never return Indirect");
                            }
                        }
                    } else {
                        match member.kind {
                            ScopeMemberKind::Constant(id) => {
                                if let Some(type_) = resources.resource(id).type_ {
                                    if type_ != TYPE_TYPE_ID {
                                        return error!(
                                            node,
                                            "A Type identifier has to contain a type!"
                                        );
                                    }
                                } else {
                                    return Ok(Some(Dependency::Type(node.loc, id)));
                                }

                                match resources.resource(id).kind {
                                    ResourceKind::Done(ref value, _) => {
                                        self.stack_len += 1;
                                        Node::new(
                                            node,
                                            NodeKind::Constant(value.clone()),
                                            TYPE_TYPE_ID,
                                            self.stack_len,
                                        )
                                    }
                                    ResourceKind::Value(_) => {
                                        return Ok(Some(Dependency::Value(node.loc, id)));
                                    }
                                    _ => {
                                        return error!(
                                            node,
                                            "A Type identifier has to contain a type!"
                                        )
                                    }
                                }
                            }
                            ScopeMemberKind::UndefinedDependency(_) => {
                                return Ok(Some(Dependency::Constant(node.loc, id)));
                            }
                            _ => return error!(node, "A Type identifier has to be constant"),
                        }
                    }
                }
                parser::NodeKind::FunctionCall { ref arg_list, .. } => {
                    let stack_loc = self.type_stack.len() - arg_list.len();
                    let arg_list_len = arg_list.len();
                    let arg_list = &self.type_stack[stack_loc..];

                    // TODO: Check if the types in the arg_list are the same as the function
                    // pointer type
                    let func_type = self.type_stack[stack_loc - 1];
                    if let Type {
                        kind: TypeKind::FunctionPointer { ref args, returns },
                        ..
                    } = types.get(func_type.type_)
                    {
                        if arg_list.len() != args.len() {
                            return error!(
                                node.loc,
                                "Expected {} arguments, got {}",
                                args.len(),
                                arg_list.len()
                            );
                        }

                        for (&wanted, got) in args.iter().zip(arg_list) {
                            if wanted != got.type_ {
                                return error!(
                                    node,
                                    "Expected '{}', got '{}'",
                                    types.type_to_string(wanted),
                                    types.type_to_string(got.type_),
                                );
                            }
                        }

                        self.type_stack.truncate(stack_loc - 1);

                        // Removing the function pointer and pushing the return value
                        // cancel out.
                        self.stack_len -= arg_list_len;
                        Node::new(
                            node,
                            NodeKind::FunctionCall(func_type.type_),
                            *returns,
                            self.stack_len,
                        )
                    } else {
                        return error!(node, "This is not a function pointer, yet a function call was attemted on it");
                    }
                }
                parser::NodeKind::BinaryOperator { operator, .. } => {
                    let right = self.type_stack.pop().unwrap();
                    let left = self.type_stack.pop().unwrap();

                    if let Operator::Assign = operator {
                        if let TypeKind::Pointer(left_internal) = types.get(left.type_).kind {
                            if left_internal != right.type_ {
                                return error!(
                                    node,
                                    "Cannot assign {} to {}",
                                    types.type_to_string(right.type_),
                                    types.type_to_string(left_internal),
                                );
                            }

                            self.stack_len -= 1;
                            Node::new(node, NodeKind::Assign, right.type_, self.stack_len)
                        } else {
                            return error!(node, "Internal compiler error; Assign can only assign to lvalues(i.e pointers)");
                        }
                    } else {
                        let (intrinsic, return_type) = match get_binary_operator_intrinsic(
                            operator,
                            types,
                            left.type_,
                            right.type_,
                        ) {
                            Some(value) => value,
                            None => {
                                // TODO: Make this error message less strange
                                return error!(
                                    node,
                                    "This combination of operator and types does not exist"
                                );
                            }
                        };

                        match (
                            &self.ast.nodes[left.node_id].kind,
                            &self.ast.nodes[right.node_id].kind,
                        ) {
                            // Constant folding
                            (NodeKind::Constant(ref left), NodeKind::Constant(ref right)) => {
                                let mut buffer = 0;
                                run_intrinsic_two(intrinsic, &mut buffer, left, right);

                                self.ast.nodes.pop();
                                self.ast.nodes.pop();

                                self.stack_len -= 1;
                                Node::new(
                                    node,
                                    NodeKind::Constant(
                                        buffer.to_le_bytes().as_slice()
                                            [..types.handle(return_type).size]
                                            .into(),
                                    ),
                                    return_type,
                                    self.stack_len,
                                )
                            }
                            _ => {
                                self.stack_len -= 1;
                                Node::new(
                                    node,
                                    NodeKind::IntrinsicTwo(intrinsic),
                                    return_type,
                                    self.stack_len,
                                )
                            }
                        }
                    }
                }
                parser::NodeKind::UnaryOperator {
                    operand: _,
                    operator,
                } => {
                    match operator {
                        Operator::BitAndOrPointer => {
                            let operand = self.ast.nodes.pop().unwrap();
                            self.type_stack.pop();

                            if !operand.is_lvalue {
                                return error!(node, "You can only take a pointer to an lvalue(internal compiler error, this should have been caught in parser)");
                            }

                            operand
                        }
                        Operator::MulOrDeref => {
                            if let TypeKind::Pointer(sub_type) =
                                types.get(self.type_stack.pop().unwrap().type_).kind
                            {
                                if node.is_lvalue {
                                    // lvalue deref is a noop. It's like a boundary between
                                    // normal stuff and an lvalue.
                                    self.ast.nodes.pop().unwrap()
                                } else {
                                    self.stack_len += 0;
                                    Node::new(node, NodeKind::Dereference, sub_type, self.stack_len)
                                }
                            } else {
                                return error!(node, "Can only dereference pointers");
                            }
                        }
                        _ => return error!(node, "Unhandled operator (compiler error)"),
                    }
                }
                parser::NodeKind::Declaration { variable_name, .. } => {
                    scopes.member_mut(variable_name).type_ =
                        Some(self.type_stack.pop().unwrap().type_);

                    self.stack_len += 0;
                    Node::new(
                        node,
                        NodeKind::Declaration { variable_name },
                        EMPTY_TYPE_ID,
                        self.stack_len,
                    )
                }
                parser::NodeKind::Block {
                    ref contents,
                    label,
                } => {
                    let stack_bottom = self.type_stack.len() - contents.len();
                    let content_types = &self.type_stack[stack_bottom..];
                    let is_never_type = content_types.iter().any(|v| v.type_ == NEVER_TYPE_ID);

                    let type_ = if is_never_type {
                        NEVER_TYPE_ID
                    } else {
                        content_types.last().unwrap().type_
                    };

                    self.type_stack.truncate(stack_bottom);

                    let label_val = self.ast.locals.labels.get_mut(label);
                    *label_val = combine_types(node, types, *label_val, type_)?;

                    self.stack_len -= contents.len();
                    self.stack_len += 1;

                    self.ast.label_map.insert(
                        label,
                        LabelMapValue {
                            node_id: self.ast.nodes.len() + 1,
                            stack_len: self.stack_len - 1,
                        },
                    );
                    Node::new(
                        node,
                        NodeKind::Block {
                            contents: contents.clone(),
                            label,
                        },
                        *self.ast.locals.labels.get(label),
                        self.stack_len,
                    )
                }
                parser::NodeKind::Skip { label, value: _ } => {
                    let type_ = self.type_stack.pop().unwrap().type_;

                    let label_val = self.ast.locals.labels.get_mut(label);
                    *label_val = combine_types(node, types, *label_val, type_)?;

                    self.stack_len += 0;
                    Node::new(node, NodeKind::Skip { label }, NEVER_TYPE_ID, 0)
                }

                // --- Type expressions ---
                parser::NodeKind::GetType(_) => {
                    let type_ = get_type(types, &self.ast, self.type_stack.pop().unwrap())?;
                    self.ast.nodes.pop();
                    self.stack_len += 0;
                    Node::new(node, type_to_const(type_), TYPE_TYPE_ID, self.stack_len)
                }
                parser::NodeKind::TypeFunctionPointer {
                    ref arg_list,
                    return_type: _,
                } => {
                    let returns = get_type(types, &self.ast, self.type_stack.pop().unwrap())?;
                    let kind = TypeKind::FunctionPointer {
                        args: arg_list
                            .iter()
                            .map(|_| get_type(types, &self.ast, self.type_stack.pop().unwrap()))
                            .rev()
                            .collect::<Result<_, ()>>()?,
                        returns,
                    };

                    let new_len = self.ast.nodes.len() - arg_list.len() - 1;
                    self.ast.nodes.truncate(new_len);

                    let type_ = types.insert(Type::new(kind));

                    // Remove the arguments and the return type
                    self.stack_len -= arg_list.len() + 1;
                    self.stack_len += 1;
                    Node::new(node, type_to_const(type_), TYPE_TYPE_ID, self.stack_len)
                }
                parser::NodeKind::TypeTuple(n_members) => {
                    // Figure out the wanted offsets of the arguments.
                    let stack_len = self.type_stack.len() - n_members;
                    let args = &self.type_stack[stack_len..];
                    let type_ = types.create_tuple(
                        (0..n_members).map(|i| Ok(get_type(types, &self.ast, args[i])?)),
                    )?;
                    let type_ = types.insert(type_);
                    self.ast.nodes.truncate(args[0].node_id);
                    self.type_stack.truncate(stack_len);
                    self.stack_len -= n_members;
                    self.stack_len += 1;
                    Node::new(node, type_to_const(type_), TYPE_TYPE_ID, self.stack_len)
                }
                parser::NodeKind::TypeStruct { ref args } => {
                    // Figure out the wanted offsets of the arguments.
                    let stack_len = self.type_stack.len() - args.len();
                    let struct_args = &self.type_stack[stack_len..];
                    let type_ =
                        types.create_struct(args.iter().enumerate().map(|(i, (name, _))| {
                            Ok((*name, get_type(types, &self.ast, struct_args[i])?))
                        }))?;
                    let type_ = types.insert(type_);
                    self.ast.nodes.truncate(struct_args[0].node_id);
                    self.type_stack.truncate(stack_len);
                    self.stack_len -= args.len();
                    self.stack_len += 1;
                    Node::new(node, type_to_const(type_), TYPE_TYPE_ID, self.stack_len)
                }
                parser::NodeKind::TypePointer(_) => {
                    let pointing_to_type =
                        get_type(types, &self.ast, self.type_stack.pop().unwrap())?;
                    let type_ = types.insert(Type::new(TypeKind::Pointer(pointing_to_type)));
                    self.ast.nodes.pop();

                    self.stack_len += 0;
                    Node::new(node, type_to_const(type_), TYPE_TYPE_ID, self.stack_len)
                }
                parser::NodeKind::TypeBufferPointer(_) => {
                    let pointing_to_type =
                        get_type(types, &self.ast, self.type_stack.pop().unwrap())?;
                    let type_ = types.insert(Type::new(TypeKind::BufferPointer(pointing_to_type)));
                    self.ast.nodes.pop();

                    self.stack_len += 0;
                    Node::new(node, type_to_const(type_), TYPE_TYPE_ID, self.stack_len)
                }
            };

            self.type_stack.push(TypeStackElement {
                type_: new_node.type_,
                loc: new_node.loc,
                node_id: self.ast.nodes.len(),
            });
            self.ast.nodes.push(new_node);

            self.node_id += 1;

            // for &type_ in self.type_stack.iter() {
            // 	print!("(");
            // 	types.print(type_.type_);
            // 	print!(")");
            // }
            // println!();
        }

        // println!("");
        // for node in &self.ast.nodes {
        // 	println!("{}: {:?}", types.type_to_string(node.type_), node.kind);
        // }

        Ok(None)
    }
}

fn type_to_const(id: TypeId) -> NodeKind {
    NodeKind::Constant(id.into_index().to_le_bytes().as_slice().into())
}

fn get_type(types: &Types, ast: &Ast, element: TypeStackElement) -> Result<TypeId, ()> {
    if element.type_ != TYPE_TYPE_ID {
        return error!(
            element.loc,
            "This needs to be a type(internal compiler error)"
        );
    }

    match &ast.nodes[element.node_id].kind {
        NodeKind::Constant(ref buffer) => {
            use std::convert::TryInto;
            match buffer.as_slice().try_into() {
                Ok(buffer) => {
                    let id = usize::from_le_bytes(buffer);
                    if id >= types.types.len() {
                        return error!(element.loc, "Invalid type id");
                    }

                    Ok(TypeId::create(id as u32))
                }
                Err(_) => {
                    return error!(element.loc, "Not a 64 bit value");
                }
            }
        }
        _ => {
            return error!(element.loc, "Types have to be constant");
        }
    }
}

#[inline]
pub fn combine_types(
    loc: &impl Location,
    types: &Types,
    a: TypeId,
    b: TypeId,
) -> Result<TypeId, ()> {
    if a == NEVER_TYPE_ID {
        Ok(b)
    } else if b == NEVER_TYPE_ID || a == b {
        Ok(a)
    } else {
        error!(
            loc,
            "Types '{}' and '{}' do not match",
            types.type_to_string(a),
            types.type_to_string(b)
        )
    }
}
