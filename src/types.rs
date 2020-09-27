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

	pub fn insert_struct(&mut self, type_: impl Iterator<Item = (ustr::Ustr, TypeId)>) -> TypeId {
		let mut full_member_data = Vec::new();
		let mut offset = 0;
		for (name, member_type_id) in type_ {
			let member_type_handle = self.handle(member_type_id);
			let aligned_off = to_aligned(member_type_handle.align, offset);
			full_member_data.push((name, aligned_off, member_type_handle));

			offset = aligned_off + member_type_handle.size;
		}

		let type_ = Type::new(TypeKind::Struct { members: full_member_data });

		// Try to find a type that is already the same.
		for (id, self_type) in self.types.iter_ids() {
			if *self_type == type_ {
				return id;
			}
		}

		self.types.push(type_)
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
	pub type_: Option<TypeId>,
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
			type_: Some(type_),
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
	MemberAccess(AstNodeId, ustr::Ustr),
	Number(i128),
	Float(f64),

	IntrinsicTwo(IntrinsicKindTwo),

	EmptyLiteral,
	Identifier
	{
		source: ScopeMemberId, 
		const_members: smallvec::SmallVec<[ustr::Ustr; 3]>,
		is_type: bool,
	},

	BitCast {
		into_type: AstNodeId,
		value: AstNodeId,
	},

	Assign,

	Resource(ResourceId),
	FunctionCall {
		function_pointer: AstNodeId,
		arg_list: Vec<AstNodeId>,
	},
	BinaryOperator {
		operator: Operator,
		left:  AstNodeId,
		right: AstNodeId,
	},
	UnaryOperator {
		operator: Operator,
		operand: AstNodeId,
	},
	/// # Members
	/// 0: Condition member
	/// 1: Body
	If {
		condition: AstNodeId,
		body: AstNodeId,
		end_label: LabelId,
	},
	/// # Members
	/// 0: Condition member
	/// 1: True body
	/// 2: False body
	IfWithElse {
		condition : AstNodeId,
		true_body : AstNodeId,
		false_body: AstNodeId,
		end_label: LabelId,
	},

	Loop(AstNodeId, LabelId, LabelId),

	Struct {
		members: Vec<(ustr::Ustr, AstNodeId)>,
	},

	DeclareFunctionArgument { variable_name: ScopeMemberId, type_node: AstNodeId },
	Declaration { variable_name: ScopeMemberId, value: AstNodeId, },
	Block {
		contents: Vec<AstNodeId>,
		label: LabelId,
	},
	Skip {
		label: LabelId,
		value: AstNodeId,
	},

	/// Returns the type of a type expression as a value instead of a type.
	GetType(AstNodeId),

	HeapClone(AstNodeId),
	StackClone(AstNodeId),

	// Type expressions
	// Type expressions have all their data in their types, and are never turned into bytecode.
	// The 'type' that they have is not the type of the value, but the value itself. I.e.,
	// the type of a TypeIdentifier produced from U64 is U64, as opposed to
	// Identifier from U64 which would be of type Type.
	//
	// GetType makes the type of a typeexpression node into a constant value, to make it
	// usable for other nodes.
	/// Exactly the same as an identifier but it is a type expression.
	TypeFunctionPointer {
		arg_list: Vec<AstNodeId>,
		return_type: Option<AstNodeId>,
	},
	TypeStruct {
		args: Vec<(ustr::Ustr, AstNodeId)>,
	},
	TypePointer(AstNodeId),
	TypeBufferPointer(AstNodeId),
}

pub struct AstTyper {
	/// Each element in this corresponds to an ast node.
	/// Once done, this list should be the same length as the ast.
	node_id: usize,

	pub ast: Ast,
}

impl AstTyper {
	pub fn new(local_variables: LocalVariables) -> AstTyper {
		AstTyper {
			node_id: 0,
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
					Node::new(
						node,
						NodeKind::Struct { members: members.clone() },
						types.insert_struct(members.iter().map(|(name, node)|
							(*name, self.ast.nodes[*node as usize].type_.unwrap())
						)),
					)
				}
				parser::NodeKind::HeapClone(_) => { todo!("Heap clone"); }
				parser::NodeKind::StackClone(_) => { todo!("Stack clone"); }
				parser::NodeKind::Marker(marker_kind @ parser::MarkerKind::IfElseTrueBody { contains, .. }) => {
					Node::new(
						node,
						NodeKind::Marker(marker_kind),
						self.ast.nodes[contains as usize].type_.unwrap(),
					)
				}
				parser::NodeKind::Marker(marker_kind @ parser::MarkerKind::IfCondition(_, _)) => {
					Node::new(
						node,
						NodeKind::Marker(marker_kind),
						self.ast.nodes[self.node_id - 1].type_.unwrap(),
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
						NodeKind::Number(number),
						U64_TYPE_ID,
					)
				}
				parser::NodeKind::Float(number) => {
					Node::new(
						node,
						NodeKind::Float(number),
						F64_TYPE_ID,
					)
				}
				parser::NodeKind::DeclareFunctionArgument { variable_name, type_node } => {
					scopes.member_mut(variable_name).type_ 
						= Some(self.ast.nodes[type_node as usize].type_.unwrap());

					Node::new(
						node,
						NodeKind::DeclareFunctionArgument { variable_name, type_node },
						EMPTY_TYPE_ID
					)
				}
				parser::NodeKind::MemberAccess(member, sub_name) => {
					let id = self.ast.nodes[member as usize].type_.unwrap();
					let type_kind = &types.get(id).kind;
					
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
						_ => return error!(node, "This type doesn't have members"),
					};

					Node::new(
						node,
						NodeKind::MemberAccess(member, sub_name),
						type_,
					)
				}
				parser::NodeKind::Loop(a, b, break_label) => {
					Node::new(
						node,
						NodeKind::Loop(a, b, break_label),
						*self.ast.locals.labels.get(break_label),
					)
				}
				parser::NodeKind::If { condition, body, end_label } => {
					let condition_type = self.ast.nodes[condition as usize].type_.unwrap();
					if condition_type != BOOL_TYPE_ID {
						return error!(node,
							"If condition has to be Bool, got {}",
							types.type_to_string(condition_type));
					}

					// If on its own never returns a type
					Node::new(
						node,
						NodeKind::If { condition, body, end_label },
						EMPTY_TYPE_ID,
					)
				}
				parser::NodeKind::IfWithElse { true_body, false_body, condition, end_label } => {
					let condition_type = self.ast.nodes[condition as usize].type_.unwrap();
					if condition_type != BOOL_TYPE_ID {
						return error!(node,
							"If condition has to be Bool, got {}",
							types.type_to_string(condition_type));
					}
					
					let return_type = combine_types(
						node,
						types,
						self.ast.nodes[true_body as usize].type_.unwrap(),
						self.ast.nodes[false_body as usize].type_.unwrap(),
					)?;

					self.ast.nodes[true_body  as usize].type_ = Some(return_type);
					self.ast.nodes[false_body as usize].type_ = Some(return_type);

					Node::new(
						node,
						NodeKind::IfWithElse { true_body, false_body, condition, end_label },
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
						NodeKind::EmptyLiteral,
						EMPTY_TYPE_ID,
					)
				}
				parser::NodeKind::BitCast { into_type, value } => {
					let into_type_handle =
						types.handle(self.ast.nodes[into_type as usize].type_.unwrap());
					let value_type_handle =
						types.handle(self.ast.nodes[value as usize].type_.unwrap());

					if into_type_handle.size != value_type_handle.size {
						return error!(node, "Bit casting requires the type you're casting to and the type you're casting from to be the same size in bits");
					}

					Node::new(
						node,
						NodeKind::BitCast { into_type, value },
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
					let final_type = if !is_type {
						match member.kind {
							ScopeMemberKind::LocalVariable => {
								if let Some(type_) = member.type_ {
									type_
								} else {
									return error!(node, "Type is not assigned, is the variable not declared? (This is probably a compiler problem)");
								}
							} 
							ScopeMemberKind::Constant(id) => {
								if let Some(type_) = resources.resource(id).type_ {
									type_
								} else {
									return Ok(Some(Dependency::Type(node.loc, id)));
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
										if let &[a, b, c, d, e, f, g, h] = value.as_slice() {
											let id = usize::from_le_bytes([a, b, c, d, e, f, g, h]);
											if id >= types.types.len() {
												return error!(node, "Invalid type id");
											}
											TypeId::create(id as u32)
										} else {
											unreachable!("The value of a type has to be a 64 bit value");
										}
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
					};

					Node::new(
						node,
						NodeKind::Identifier {
							source: id,
							const_members: smallvec::SmallVec::new(),
							is_type,
						},
						final_type,
					)
				}
				parser::NodeKind::FunctionCall { function_pointer, ref arg_list } => {
					// TODO: Check if the types in the arg_list are the same as the function
					// pointer type
					let func_type =
						types.get(self.ast.nodes[function_pointer as usize].type_.unwrap());
					if let Type { kind: TypeKind::FunctionPointer { ref args, returns }, .. }
						= func_type 
					{
						if arg_list.len() != args.len() {
							return error!(node.loc, "Expected {} arguments, got {}", 
								args.len(), arg_list.len());
						}

						for (wanted, got) in args.iter().zip(arg_list) {
							if Some(*wanted) != self.ast.nodes[*got as usize].type_ {
								return error!(ast.get_node(*got as u32), "Expected '{}', got '{}'",
									types.type_to_string(*wanted), 
									types.type_to_string(self.ast.nodes[*got as usize].type_.unwrap())
								);
							}
						}

						Node::new(
							node,
							NodeKind::FunctionCall { function_pointer, arg_list: arg_list.clone() },
							*returns,
						)
					} else {
						return error!(node, "This is not a function pointer, yet a function call was attemted on it");
					}
				}
				parser::NodeKind::BinaryOperator { left, right, operator } => {
					let left_type = self.ast.nodes[left as usize].type_.unwrap();
					let right_type = self.ast.nodes[right as usize].type_.unwrap();

					if let Operator::Assign = operator {
						if left_type != right_type {
							return error!(node,
								"Cannot assign {} to {}",
								types.type_to_string(right_type),
								types.type_to_string(left_type),
							);
						}

						Node::new(
							node,
							NodeKind::Assign,
							left_type,
						)
					} else {
						// Generate an intrinsic for the combination of types.
						// TODO: Move this to a separate file at least, to hide the mess a bit.
						let (intrinsic, return_type) =
							match get_binary_operator_intrinsic(operator, types, left_type, right_type)
						{
							Some(value) => value,
							None => return error!(node, "This combination of operator and types does not exist"),
						};

						Node::new(
							node,
							NodeKind::IntrinsicTwo(intrinsic),
							return_type,
						)
					}
				},
				parser::NodeKind::UnaryOperator { operand, operator } => {
					let type_ = match operator {
						Operator::BitAndOrPointer => types.insert(Type::new(
							TypeKind::Pointer(self.ast.nodes[operand as usize].type_.unwrap())
						)),
						Operator::MulOrDeref => {
							if let TypeKind::Pointer(sub_type) 
								= types.get(self.ast.nodes[operand as usize].type_.unwrap()).kind
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
						NodeKind::UnaryOperator { operand, operator },
						type_,
					)
				},
				parser::NodeKind::Declaration { variable_name, value } => {
					if let Some(type_) = self.ast.nodes[value as usize].type_ {
						scopes.member_mut(variable_name).type_ = Some(type_);
					} else {
						return error!(node, "Cannot assign nothing to a variable");
					}
					
					Node::new(
						node,
						NodeKind::Declaration { variable_name, value },
						EMPTY_TYPE_ID,
					)
				}
				parser::NodeKind::Block { ref contents, label } => {
					let mut is_never_type = false;
					for &content_node_id in contents.iter() {
						if is_never_type {
							if !matches!(self.ast.nodes[content_node_id as usize].kind, NodeKind::EmptyLiteral) {
								warning!(
									ast.nodes[content_node_id as usize],
									"Dead code"
								);
							}
						}

						if self.ast.nodes[content_node_id as usize].type_.unwrap() == NEVER_TYPE_ID {
							is_never_type = true;
						}
					}

					if is_never_type && !matches!(self.ast.nodes[*contents.last().unwrap() as usize].kind, NodeKind::EmptyLiteral) {
						return error!(
							ast.nodes[*contents.last().unwrap() as usize],
							"Cannot use dead code as return expression"
						);
					}

					let type_ = if is_never_type {
						NEVER_TYPE_ID
					} else {
						self.ast.nodes[*contents.last().unwrap() as usize].type_.unwrap()
					};

					let label_val = self.ast.locals.labels.get_mut(label);
					*label_val = combine_types(node, types, *label_val, type_)?;

					Node::new(
						node,
						NodeKind::Block { contents: contents.clone(), label },
						*self.ast.locals.labels.get(label),
					)
				}
				parser::NodeKind::Skip { label, value } => {
					let type_ = self.ast.nodes[value as usize].type_.unwrap();

					let label_val = self.ast.locals.labels.get_mut(label);
					*label_val = combine_types(node, types, *label_val, type_)?;

					Node::new(
						node,
						NodeKind::Skip { label, value },
						NEVER_TYPE_ID,
					)
				},

				// --- Type expressions ---
				parser::NodeKind::GetType(id) => {
					Node::new(
						node,
						NodeKind::GetType(id),
						TYPE_TYPE_ID,
					)
				}
				parser::NodeKind::TypeFunctionPointer { ref arg_list, return_type } => {
					let kind = TypeKind::FunctionPointer {
						args: arg_list.iter().map(|&v| self.ast.nodes[v as usize].type_.unwrap())
							.collect(),
						returns: match return_type {
							Some(v) => self.ast.nodes[v as usize].type_.unwrap(),
							None => types.insert(Type::new(TypeKind::EmptyType)),
						}
					};

					Node::new(
						node,
						NodeKind::TypeFunctionPointer { arg_list: arg_list.clone(), return_type },
						types.insert(Type::new(kind)),
					)
				}
				parser::NodeKind::TypeStruct { ref args } => {
					// Figure out the wanted offsets of the arguments.
					Node::new(
						node,
						NodeKind::TypeStruct { args: args.clone() },
						types.insert_struct(args.iter().map(|(name, node)|
							(*name, self.ast.nodes[*node as usize].type_.unwrap())
						)),
					)
				}
				parser::NodeKind::TypePointer(pointing_to) => {
					let pointing_to_type = self.ast.nodes[pointing_to as usize].type_.unwrap();
					Node::new(
						node,
						NodeKind::TypePointer(pointing_to),
						types.insert(Type::new(TypeKind::Pointer(pointing_to_type))),
					)
				}
				parser::NodeKind::TypeBufferPointer(pointing_to) => {
					let pointing_to_type = self.ast.nodes[pointing_to as usize].type_.unwrap();
					Node::new(
						node,
						NodeKind::TypeBufferPointer(pointing_to),
						types.insert(Type::new(TypeKind::BufferPointer(pointing_to_type))),
					)
				}
			};

			// This will get removed later, it's just a check to make sure I don't do something
			// bad for now.
			let id = self.ast.nodes.len();
			assert_eq!(self.node_id, id);

			self.ast.nodes.push(new_node);

			self.node_id += 1;
		}

		Ok(None)
	}
}

#[inline]
pub fn combine_types(loc: &impl Location, types: &Types, a: TypeId, b: TypeId) -> Result<TypeId, ()> {
	if a == NEVER_TYPE_ID { Ok(b) }
	else if b == NEVER_TYPE_ID { Ok(a) }
	else if a == b { Ok(a) }
	else { error!(loc, "Types '{}' and '{}' do not match", types.type_to_string(a), types.type_to_string(b)) }
}
