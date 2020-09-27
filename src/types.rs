use crate::intrinsic::*;
// We can't import the parser directly because of name clasing
use crate::parser;
use crate::scopes::*;
use crate::resource::*;
use crate::id::*;
use crate::align::*;
use crate::code_loc::*;
use crate::operator::*;
use crate::error::*;
use crate::stack_frame::*;

pub const TYPE_TYPE_ID:   TypeId = TypeId::create_raw(0);
pub const U64_TYPE_ID:    TypeId = TypeId::create_raw(1);
pub const U32_TYPE_ID:    TypeId = TypeId::create_raw(2);
pub const U16_TYPE_ID:    TypeId = TypeId::create_raw(3);
pub const U8_TYPE_ID:     TypeId = TypeId::create_raw(4);
pub const S64_TYPE_ID:    TypeId = TypeId::create_raw(5);
pub const S32_TYPE_ID:    TypeId = TypeId::create_raw(6);
pub const S16_TYPE_ID:    TypeId = TypeId::create_raw(7);
pub const S8_TYPE_ID:     TypeId = TypeId::create_raw(8);
pub const F64_TYPE_ID:    TypeId = TypeId::create_raw(9);
pub const F32_TYPE_ID:    TypeId = TypeId::create_raw(10);
pub const BOOL_TYPE_ID:   TypeId = TypeId::create_raw(11);
pub const EMPTY_TYPE_ID:  TypeId = TypeId::create_raw(12);
pub const NEVER_TYPE_ID:  TypeId = TypeId::create_raw(13);

create_id!(TypeId);

pub struct Types {
	types: IdVec<Type, TypeId>,
}

impl Types {
	pub fn new() -> Self {
		let mut types = IdVec::new();
		assert_eq!(types.push(Type::new(TypeKind::Type)), TYPE_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::U64)), U64_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::U32)), U32_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::U16)), U16_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::U8 )), U8_TYPE_ID );
		assert_eq!(types.push(Type::new(TypeKind::S64)), S64_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::S32)), S32_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::S16)), S16_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::S8 )), S8_TYPE_ID );
		assert_eq!(types.push(Type::new(TypeKind::F64)), F64_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::F32)), F32_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::Bool)), BOOL_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::EmptyType)), EMPTY_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::NeverType)), NEVER_TYPE_ID);
		Self { types }
	}

	pub fn handle(&self, id: TypeId) -> TypeHandle {
		let type_ = self.types.get(id);
		TypeHandle { id, size: type_.size, align: type_.align }
	}

	pub fn create_struct(&self, type_: impl Iterator<Item = Result<(ustr::Ustr, TypeId), ()>>) -> Result<Type, ()> {
		let mut full_member_data = Vec::new();
		let mut offset = 0;
		for member in type_ {
			let (name, member_type_id) = member?;
			let member_type_handle = self.handle(member_type_id);
			let aligned_off = to_aligned(member_type_handle.align, offset);
			full_member_data.push((name, aligned_off, member_type_handle));

			offset = aligned_off + member_type_handle.size;
		}

		Ok(Type::new(TypeKind::Struct { members: full_member_data }))
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
	/// 	offset in bytes from type start,
	/// 	id of type behind the pointer,
	/// 	number of instances of the type behind the pointer(the number of bytes have to be
	/// 	calculated by multiplying by the size of the type),
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
					size_offset: None
				});
			},
			TypeKind::BufferPointer(type_behind_pointer) => {
				pointers_inside.push(PointerInType { 
					offset,
					type_behind_pointer,
					size_offset: Some(offset + 8)
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
					if i > 0 { write!(buffer, ", ").unwrap(); }

					write!(buffer, "{}[{}]: ", name, offset).unwrap();
					self.write_type_to_buffer(member.id, buffer);
				}
				write!(buffer, "}}").unwrap();
			}
			TypeKind::Pointer(sub_type) => {
				write!(buffer, "&").unwrap();
				self.write_type_to_buffer(sub_type, buffer);
			}
			TypeKind::FunctionPointer { ref args, returns } => {
				write!(buffer, "(").unwrap();
				for (i, arg) in args.iter().enumerate() {
					if i > 0 { write!(buffer, ", ").unwrap(); }
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
					size  = to_aligned(align, size.max(offset + handle.size));
				}
				(size, align)
			}
			TypeKind::Pointer(_) => (8, 8),
			TypeKind::NeverType => (0, 1),
			TypeKind::BufferPointer(_) => (16, 8),
			TypeKind::EmptyType => (0, 1),
			TypeKind::U64 |
			TypeKind::S64 |
			TypeKind::F64 |
			TypeKind::Type => (8, 8),
			TypeKind::U32 |
			TypeKind::S32 |
			TypeKind::F32 => (4, 4),
			TypeKind::U16 |
			TypeKind::S16 => (2, 2),
			TypeKind::Bool |
			TypeKind::U8 |
			TypeKind::S8 => (1, 1),
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
pub struct Ast {
	pub nodes: Vec<Node>,
	pub locals: LocalVariables,
}

impl Ast {
	pub fn new(locals: LocalVariables) -> Self {
		Ast { 
			nodes: Vec::new(),
			locals,
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
	/// Meta data is for typing and other things to use, and shouldn't be included
	/// in the actual code output.
	pub is_meta_data: bool,
}

impl Node {
	fn new(old_node: &parser::Node, new_kind: NodeKind, type_: TypeId) -> Self {
		Node { 
			loc: old_node.loc,
			kind: new_kind, 
			scope: old_node.scope,
			is_lvalue: old_node.is_lvalue, 
			is_meta_data: old_node.is_meta_data,
			// TODO: Remove the option here
			type_,
		}
	}
}

impl Location for Node {
	fn get_location(&self) -> CodeLoc {
		self.loc.clone()
	}
}

#[derive(Debug)]
pub enum NodeKind {
	Marker(parser::MarkerKind),
	MemberAccess(TypeId, ustr::Ustr),
	Constant(ConstBuffer),

	IntrinsicTwo(IntrinsicKindTwo),
	Identifier(ScopeMemberId),

	BitCast,

	Assign,

	Resource(ResourceId),
	FunctionCall(TypeId),
	BinaryOperator {
		operator: Operator,
	},
	UnaryOperator {
		operator: Operator,
	},
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

	Struct {
		members: Vec<(ustr::Ustr, AstNodeId)>,
	},

	DeclareFunctionArgument(ScopeMemberId),
	Declaration { variable_name: ScopeMemberId, },
	Block {
		contents: Vec<AstNodeId>,
		label: LabelId,
	},
	Skip {
		label: LabelId,
	},

	/// Returns the type of a type expression as a value instead of a type.
	GetType(TypeId),

	// Type expressions
	// Type expressions have all their data in their types, and are never turned into bytecode.
	// The 'type' that they have is not the type of the value, but the value itself. I.e.,
	// the type of a TypeIdentifier produced from U64 is U64, as opposed to
	// Identifier from U64 which would be of type Type.
	//
	// GetType makes the type of a typeexpression node into a constant value, to make it
	// usable for other nodes.
	/// Exactly the same as an identifier but it is a type expression.
	TypeFunctionPointer,
	TypeStruct,
	TypePointer,
	TypeBufferPointer,
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

	pub ast: Ast,
}

impl AstTyper {
	pub fn new(local_variables: LocalVariables) -> AstTyper {
		AstTyper {
			node_id: 0,
			type_stack: Vec::new(),
			ast: Ast::new(local_variables),
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
				parser::NodeKind::Assign => return error!(node, "Assign is generated by typer, cannot be found here"),
				parser::NodeKind::IntrinsicTwo(_) => {
					return error!(node, "For now, the parser cannot output any intrinsics. This will be allowed in the future, however, but for now intrinsics can only be generated by the typer");
				}
				parser::NodeKind::Struct { ref members } => {
					let stack_len = self.type_stack.len() - members.len();
					let member_types = &self.type_stack[stack_len..];
					let type_ = types.create_struct(
						members.iter().zip(member_types).map(|((name, _), type_)|
							Ok((*name, type_.type_))
						))?;
					let type_ = types.insert(type_);
					self.type_stack.truncate(stack_len);
					Node::new(
						node,
						NodeKind::Struct { members: members.clone() },
						type_,
					)
				}
				parser::NodeKind::HeapClone(_) => { todo!("Heap clone"); }
				parser::NodeKind::StackClone(_) => { todo!("Stack clone"); }
				parser::NodeKind::Marker(marker_kind @ parser::MarkerKind::IfElseTrueBody { .. }) => {
					Node::new(
						node,
						NodeKind::Marker(marker_kind),
						self.type_stack.pop().unwrap().type_,
					)
				}
				parser::NodeKind::Marker(marker_kind @ parser::MarkerKind::IfCondition(_, _)) => {
					Node::new(
						node,
						NodeKind::Marker(marker_kind),
						self.type_stack.pop().unwrap().type_,
					)
				}
				parser::NodeKind::Marker(kind) => {
					Node::new(
						node,
						NodeKind::Marker(kind),
						EMPTY_TYPE_ID,
					)
				}
				parser::NodeKind::Number(number) => {
					Node::new(
						node,
						NodeKind::Constant((number as u64).to_le_bytes().as_slice().into()),
						U64_TYPE_ID,
					)
				}
				parser::NodeKind::Float(number) => {
					Node::new(
						node,
						NodeKind::Constant(number.to_bits().to_le_bytes().as_slice().into()),
						F64_TYPE_ID,
					)
				}
				parser::NodeKind::DeclareFunctionArgument { variable_name, .. } => {
					scopes.member_mut(variable_name).type_ = Some(get_type(types, &self.ast, self.type_stack.pop().unwrap())?);

					Node::new(
						node,
						NodeKind::DeclareFunctionArgument(variable_name),
						EMPTY_TYPE_ID
					)
				}
				parser::NodeKind::MemberAccess(_, sub_name) => {
					let type_id = self.type_stack.pop().unwrap();
					let type_kind = &types.get(type_id.type_).kind;
					
					let type_ = match *type_kind {
						TypeKind::U64 => {
							if sub_name == "low" {
								U32_TYPE_ID
							} else if sub_name == "high" {
								U32_TYPE_ID
							} else {
								return error!(node, "This member does not exist on U64");
							}
						}
						TypeKind::BufferPointer(sub_type) => {
							if sub_name == "pointer" {
								types.insert(Type::new(TypeKind::Pointer(sub_type)))
							} else if sub_name == "length" {
								U64_TYPE_ID
							} else {
								return error!(node, "This member does not exist on BufferPointer");
							}
						}
						TypeKind::Struct { ref members } => {
							let mut type_ = None;
							for (name, _, handle) in members {
								if *name == sub_name {
									type_ = Some(handle.id);
									break;
								}
							}
							
							if let Some(type_) = type_ {
								type_
							} else {
								return error!(node, "This member does not exist in struct");
							}
						}
						_ => return error!(node, "Type {} does not have members", types.type_to_string(type_id.type_)),
					};

					Node::new(
						node,
						NodeKind::MemberAccess(type_id.type_, sub_name),
						type_,
					)
				}
				parser::NodeKind::Loop(_, b, break_label) => {
					let _ = self.type_stack.pop().unwrap();
					Node::new(
						node,
						NodeKind::Loop(b, break_label),
						*self.ast.locals.labels.get(break_label),
					)
				}
				parser::NodeKind::If { condition: _, body: _, end_label } => {
					let _body = self.type_stack.pop().unwrap();
					let condition = self.type_stack.pop().unwrap();
					if condition.type_ != BOOL_TYPE_ID {
						return error!(condition.loc,
							"If condition has to be Bool, got {}",
							types.type_to_string(condition.type_));
					}

					// If on its own never returns a type
					Node::new(
						node,
						NodeKind::If(end_label),
						EMPTY_TYPE_ID,
					)
				}
				parser::NodeKind::IfWithElse { end_label, .. } => {
					let false_body = self.type_stack.pop().unwrap();
					let true_body  = self.type_stack.pop().unwrap();
					let condition  = self.type_stack.pop().unwrap();

					if condition.type_ != BOOL_TYPE_ID {
						return error!(condition.loc,
							"If condition has to be Bool, got {}",
							types.type_to_string(condition.type_));
					}
					
					let return_type = combine_types(
						node,
						types,
						true_body.type_,
						false_body.type_,
					)?;

					Node::new(
						node,
						NodeKind::IfWithElse { end_label },
						return_type,
					)
				}
				parser::NodeKind::Resource(id) => {
					let resource = resources.resource(id);
					if let Some(type_) = resource.type_ {
						Node::new(
							node,
							NodeKind::Resource(id),
							type_,
						)
					} else {
						return Ok(Some(Dependency::Type(node.loc, id)));
					}
				}
				parser::NodeKind::EmptyLiteral => {
					Node::new(
						node,
						NodeKind::Constant(smallvec![]),
						EMPTY_TYPE_ID,
					)
				}
				parser::NodeKind::BitCast { into_type: _, value: _ } => {
					let value = self.type_stack.pop().unwrap();
					let value_type_handle = types.handle(value.type_);
					let into = self.type_stack.pop().unwrap();
					let into_type_handle = types.handle(get_type(types, &self.ast, into)?);

					if into_type_handle.size != value_type_handle.size {
						info!(value.loc, "This is {}", types.type_to_string(value_type_handle.id));
						info!(into.loc, "This is {}", types.type_to_string(into_type_handle.id));
						return error!(node, "You can only bitcast types with the same size");
					}

					Node::new(
						node,
						NodeKind::BitCast,
						into_type_handle.id,
					)
				}
				parser::NodeKind::Identifier { source: mut id, const_members: ref sub_members, is_type } => {
					for sub_member_name in sub_members {
						let member = scopes.member(id);
						match member.kind {
							ScopeMemberKind::Constant(constant_id) => {
								if let Some(scope_inside) = resources.resource(constant_id).scope_inside {
									id = scopes.find_or_create_temp(scope_inside, *sub_member_name)?;
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
									Node::new(
										node,
										NodeKind::Identifier(id),
										type_,
									)
								} else {
									return error!(node, "Type is not assigned, is the variable not declared? (This is probably a compiler problem)");
								}
							} 
							ScopeMemberKind::Constant(scope_member_id) => {
								if let Some(type_) = resources.resource(scope_member_id).type_ {
									Node::new(
										node,
										NodeKind::Identifier(id),
										type_,
									)
								} else {
									return Ok(Some(Dependency::Type(node.loc, scope_member_id)));
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
										return error!(node, "A Type identifier has to contain a type!");
									}
								} else {
									return Ok(Some(Dependency::Type(node.loc, id)));
								}

								match resources.resource(id).kind {
									ResourceKind::Done(ref value, _) => {
										Node::new(
											node,
											NodeKind::Constant(value.clone()),
											TYPE_TYPE_ID,
										)
									}
									ResourceKind::Value(_) => {
										return Ok(Some(Dependency::Value(node.loc, id)));
									}
									_ => return error!(node, "A Type identifier has to contain a type!"),
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
					let arg_list = &self.type_stack[stack_loc..];

					// TODO: Check if the types in the arg_list are the same as the function
					// pointer type
					let func_type = self.type_stack[stack_loc - 1];
					if let Type { kind: TypeKind::FunctionPointer { ref args, returns }, .. }
						= types.get(func_type.type_)
					{
						if arg_list.len() != args.len() {
							return error!(node.loc, "Expected {} arguments, got {}", 
								args.len(), arg_list.len());
						}

						for (&wanted, got) in args.iter().zip(arg_list) {
							if wanted != got.type_ {
								return error!(node, "Expected '{}', got '{}'",
									types.type_to_string(wanted), 
									types.type_to_string(got.type_),
								);
							}
						}

						self.type_stack.truncate(stack_loc - 1);

						Node::new(
							node,
							NodeKind::FunctionCall(func_type.type_),
							*returns,
						)
					} else {
						return error!(node, "This is not a function pointer, yet a function call was attemted on it");
					}
				}
				parser::NodeKind::BinaryOperator { operator, .. } => {
					let right = self.type_stack.pop().unwrap();
					let left  = self.type_stack.pop().unwrap();

					if let Operator::Assign = operator {
						if left.type_ != right.type_ {
							return error!(node,
								"Cannot assign {} to {}",
								types.type_to_string(right.type_),
								types.type_to_string(left.type_),
							);
						}

						Node::new(
							node,
							NodeKind::Assign,
							left.type_,
						)
					} else {
						let (intrinsic, return_type) =
							match get_binary_operator_intrinsic(operator, types, left.type_, right.type_)
						{
							Some(value) => value,
							None => return error!(node, "This combination of operator and types does not exist"),
						};

						match (&self.ast.nodes[left.node_id].kind, &self.ast.nodes[right.node_id].kind) {
							// Constant folding
							(NodeKind::Constant(ref left), NodeKind::Constant(ref right)) => {
								let mut buffer = 0;
								run_intrinsic_two(intrinsic, &mut buffer, left, right);

								self.ast.nodes.pop();
								self.ast.nodes.pop();

								Node::new(
									node,
									NodeKind::Constant(buffer.to_le_bytes().as_slice().into()),
									return_type,
								)
							}
							_ => {
								Node::new(
									node,
									NodeKind::IntrinsicTwo(intrinsic),
									return_type,
								)
							}
						}
					}
				},
				parser::NodeKind::UnaryOperator { operand: _, operator } => {
					let type_ = match operator {
						Operator::BitAndOrPointer => types.insert(Type::new(
							TypeKind::Pointer(self.type_stack.pop().unwrap().type_)
						)),
						Operator::MulOrDeref => {
							if let TypeKind::Pointer(sub_type) 
								= types.get(self.type_stack.pop().unwrap().type_).kind
							{
								sub_type
							} else {
								return error!(node, "Can only dereference pointers");
							}
						}
						_ => return error!(node, "Unhandled operator (compiler error)"),
					};

					Node::new(
						node,
						NodeKind::UnaryOperator { operator },
						type_,
					)
				},
				parser::NodeKind::Declaration { variable_name, .. } => {
					scopes.member_mut(variable_name).type_ = Some(self.type_stack.pop().unwrap().type_);
					
					Node::new(
						node,
						NodeKind::Declaration { variable_name },
						EMPTY_TYPE_ID,
					)
				}
				parser::NodeKind::Block { ref contents, label } => {
					let stack_bottom = self.type_stack.len() - contents.len();
					let content_types = &self.type_stack[stack_bottom..];
					let is_never_type = content_types.iter().find(|v| v.type_ == NEVER_TYPE_ID).is_some();

					if is_never_type && !matches!(content_types.last().unwrap().type_, EMPTY_TYPE_ID) {
						return error!(
							content_types.last().unwrap().loc,
							"Cannot use dead code as return expression"
						);
					}

					let type_ = if is_never_type {
						NEVER_TYPE_ID
					} else {
						content_types.last().unwrap().type_
					};

					self.type_stack.truncate(stack_bottom);

					let label_val = self.ast.locals.labels.get_mut(label);
					*label_val = combine_types(node, types, *label_val, type_)?;

					Node::new(
						node,
						NodeKind::Block { contents: contents.clone(), label },
						*self.ast.locals.labels.get(label),
					)
				}
				parser::NodeKind::Skip { label, value: _ } => {
					let type_ = self.type_stack.pop().unwrap().type_;

					let label_val = self.ast.locals.labels.get_mut(label);
					*label_val = combine_types(node, types, *label_val, type_)?;

					Node::new(
						node,
						NodeKind::Skip { label },
						NEVER_TYPE_ID,
					)
				},

				// --- Type expressions ---
				parser::NodeKind::GetType(_) => {
					let type_ = get_type(types, &self.ast, self.type_stack.pop().unwrap())?;
					Node::new(
						node,
						type_to_const(type_),
						TYPE_TYPE_ID,
					)
				}
				parser::NodeKind::TypeFunctionPointer { ref arg_list, return_type: returns } => {
					let return_type = match returns {
						Some(_) => Some(get_type(types, &self.ast, self.type_stack.pop().unwrap())?),
						None => None
					};
					let kind = TypeKind::FunctionPointer {
						args: arg_list.iter().map(
							|_| get_type(types, &self.ast, self.type_stack.pop().unwrap())
						).rev().collect::<Result<_, ()>>()?,
						returns: match return_type {
							Some(return_type) => return_type,
							None => types.insert(Type::new(TypeKind::EmptyType)),
						}
					};

					let new_len = self.ast.nodes.len() - arg_list.len() - returns.is_some() as usize;
					self.ast.nodes.truncate(new_len);

					let type_ = types.insert(Type::new(kind));
					Node::new(
						node,
						type_to_const(type_),
						TYPE_TYPE_ID,
					)
				}
				parser::NodeKind::TypeStruct { ref args } => {
					// Figure out the wanted offsets of the arguments.
					let stack_len = self.type_stack.len() - args.len();
					let struct_args = &self.type_stack[stack_len ..];
					let type_ = types.create_struct(args.iter().enumerate().map(|(i, (name, _))|
						Ok((*name, get_type(types, &self.ast, struct_args[i])?))
					))?;
					let type_ = types.insert(type_);
					self.ast.nodes.truncate(struct_args[0].node_id);
					self.type_stack.truncate(stack_len);
					Node::new(
						node,
						type_to_const(type_),
						TYPE_TYPE_ID
					)
				}
				parser::NodeKind::TypePointer(_) => {
					let pointing_to_type =
						get_type(types, &self.ast, self.type_stack.pop().unwrap())?;
					let type_ = types.insert(Type::new(TypeKind::Pointer(pointing_to_type)));
					self.ast.nodes.pop();
					Node::new(
						node,
						type_to_const(type_),
						TYPE_TYPE_ID,
					)
				}
				parser::NodeKind::TypeBufferPointer(_) => {
					let pointing_to_type =
						get_type(types, &self.ast, self.type_stack.pop().unwrap())?;
					let type_ = types.insert(Type::new(TypeKind::BufferPointer(pointing_to_type)));
					self.ast.nodes.pop();
					Node::new(
						node,
						type_to_const(type_),
						TYPE_TYPE_ID,
					)
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

		Ok(None)
	}
}

fn type_to_const(id: TypeId) -> NodeKind {
	NodeKind::Constant(id.into_index().to_le_bytes().as_slice().into())
}

fn get_type(types: &Types, ast: &Ast, element: TypeStackElement) -> Result<TypeId, ()> {
	if element.type_ != TYPE_TYPE_ID {
		return error!(element.loc, "This needs to be a type(internal compiler error)");
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
pub fn combine_types(loc: &impl Location, types: &Types, a: TypeId, b: TypeId) -> Result<TypeId, ()> {
	if a == NEVER_TYPE_ID { Ok(b) }
	else if b == NEVER_TYPE_ID { Ok(a) }
	else if a == b { Ok(a) }
	else { error!(loc, "Types '{}' and '{}' do not match", types.type_to_string(a), types.type_to_string(b)) }
}
