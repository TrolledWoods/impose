use std::collections::HashMap;

use crate::intrinsic::*;
use crate::parser::*;
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

pub struct AstTyper {
	/// Each element in this corresponds to an ast node.
	/// Once done, this list should be the same length as the ast.
	node_id: usize,
	label_types: HashMap<ScopeMemberId, Option<TypeId>>,
}

impl AstTyper {
	pub fn new() -> AstTyper {
		AstTyper {
			node_id: 0,
			label_types: HashMap::new(),
		}
	}

	pub fn try_type_ast(
		&mut self, 
		types: &mut Types, 
		ast: &mut Ast,
		scopes: &mut Scopes,
		resources: &Resources,
	) -> Result<Option<Dependency>, ()> {
		while self.node_id < ast.nodes.len() {
			let node = &ast.nodes[self.node_id];

			let type_kind = match node.kind {
				NodeKind::Temporary => return error!(node, "Temporaries have to be removed in the parser, they are not to be kept around until type checking(internal compiler error)"),
				NodeKind::Assign => return error!(node, "Assign is generated by typer, cannot be found here"),
				NodeKind::IntrinsicTwo(_) => {
					return error!(node, "For now, the parser cannot output any intrinsics. This will be allowed in the future, however, but for now intrinsics can only be generated by the typer");
				}
				NodeKind::Struct { ref members } => {
					Some(types.insert_struct(members.iter().map(|(name, node)|
						(*name, ast.nodes[*node as usize].type_.unwrap())
					)))
				}
				NodeKind::HeapClone(_) => {
					todo!("Heap clone");
				}
				NodeKind::StackClone(_) => {
					todo!("Stack clone");
				}
				NodeKind::Marker(MarkerKind::IfElseTrueBody(contains)) => {
					ast.nodes[contains as usize].type_
				}
				NodeKind::Marker(_) => {
					None
				}
				NodeKind::Number(_) => {
					Some(U64_TYPE_ID)
				}
				NodeKind::Float(_) => {
					Some(F64_TYPE_ID)
				}
				NodeKind::DeclareFunctionArgument { variable_name, type_node } => {
					scopes.member_mut(variable_name).type_ 
						= Some(ast.nodes[type_node as usize].type_.unwrap());
					None
				}
				NodeKind::MemberAccess(member, sub_name) => {
					let id = ast.nodes[member as usize].type_.unwrap();
					let type_kind = &types.get(id).kind;
					
					match *type_kind {
						TypeKind::U64 => {
							if sub_name == "low" {
								Some(U32_TYPE_ID)
							} else if sub_name == "high" {
								Some(U32_TYPE_ID)
							} else {
								return error!(node, "This member does not exist on U64");
							}
						}
						TypeKind::BufferPointer(sub_type) => {
							if sub_name == "pointer" {
								Some(types.insert(Type::new(TypeKind::Pointer(sub_type))))
							} else if sub_name == "length" {
								Some(U64_TYPE_ID)
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
								Some(type_)
							} else {
								return error!(node, "This member does not exist in struct");
							}
						}
						_ => return error!(node, "This type doesn't have members"),
					}
				}
				NodeKind::Loop { .. } => {
					Some(types.insert(Type::new(TypeKind::EmptyType)))
				}
				NodeKind::If { .. } => {
					// TODO: Check that condition is a boolean, but booleans do not exist yet.

					// If on its own never returns a type
					Some(types.insert(Type::new(TypeKind::EmptyType)))
				}
				NodeKind::IfWithElse { true_body, false_body, .. } => {
					// TODO: Check that condition is a boolean
					
					if ast.nodes[true_body as usize].type_ != ast.nodes[false_body as usize].type_ {
						return error!(node, "if and else blocks have to have the same types");
					}

					ast.nodes[true_body as usize].type_
				}
				NodeKind::Resource(id) => {
					let resource = resources.resource(id);
					if let Some(type_) = resource.type_ {
						Some(type_)
					} else {
						return Ok(Some(Dependency::Type(node.loc, id)));
					}
				}
				NodeKind::EmptyLiteral => {
					Some(types.insert(Type::new(TypeKind::EmptyType)))
				}
				NodeKind::BitCast { into_type, value } => {
					let into_type_handle =
						types.handle(ast.nodes[into_type as usize].type_.unwrap());
					let value_type_handle =
						types.handle(ast.nodes[value as usize].type_.unwrap());

					if into_type_handle.size != value_type_handle.size {
						return error!(node, "Bit casting requires the type you're casting to and the type you're casting from to be the same size in bits");
					}

					Some(into_type_handle.id)
				}
				NodeKind::Identifier { source: mut id, const_members: ref sub_members, is_type } => {
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
									ResourceKind::Value(ResourceValue::Value(_, _, ref value, _)) => {
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

					ast.nodes[self.node_id as usize].kind =
						NodeKind::Identifier {
							source: id,
							const_members: smallvec::SmallVec::new(),
							is_type,
						};

					Some(final_type)
				}
				NodeKind::FunctionCall { function_pointer, ref arg_list } => {
					// TODO: Check if the types in the arg_list are the same as the function
					// pointer type
					let func_type = types.get_if(ast.nodes[function_pointer as usize].type_);
					if let Some(Type { kind: TypeKind::FunctionPointer { ref args, returns }, .. }) 
						= func_type 
					{
						if arg_list.len() != args.len() {
							return error!(node.loc, "Expected {} arguments, got {}", 
								args.len(), arg_list.len());
						}

						for (wanted, got) in args.iter().zip(arg_list) {
							if Some(*wanted) != ast.nodes[*got as usize].type_ {
								return error!(ast.get_node(*got as u32), "Expected '{}', got '{}'",
									types.type_to_string(*wanted), 
									types.type_to_string(ast.nodes[*got as usize].type_.unwrap())
								);
							}
						}

						Some(*returns)
					} else {
						return error!(node, "This is not a function pointer, yet a function call was attemted on it");
					}
				}
				NodeKind::BinaryOperator { left, right, operator } => {
					let left_type = ast.nodes[left as usize].type_.unwrap();
					let right_type = ast.nodes[right as usize].type_.unwrap();

					if let Operator::Assign = operator {
						if left_type != right_type {
							return error!(node,
								"Cannot assign {} to {}",
								types.type_to_string(right_type),
								types.type_to_string(left_type),
							);
						}

						ast.nodes[self.node_id as usize].kind = NodeKind::Assign;
						Some(left_type)
					} else {
						// Generate an intrinsic for the combination of types.
						// TODO: Move this to a separate file at least, to hide the mess a bit.
						let (intrinsic, return_type) =
							match get_binary_operator_intrinsic(operator, types, left_type, right_type)
						{
							Some(value) => value,
							None => return error!(node, "This combination of operator and types does not exist"),
						};

						ast.nodes[self.node_id as usize].kind = NodeKind::IntrinsicTwo(intrinsic);
						Some(return_type)
					}
				},
				NodeKind::UnaryOperator { operand, operator } => {
					match operator {
						Operator::BitAndOrPointer => Some(types.insert(Type::new(
							TypeKind::Pointer(ast.nodes[operand as usize].type_.unwrap())
						))),
						Operator::MulOrDeref => {
							if let TypeKind::Pointer(sub_type) 
								= types.get(ast.nodes[operand as usize].type_.unwrap()).kind
							{
								Some(sub_type)
							} else {
								return error!(node, "Can only dereference pointers");
							}
						}
						_ => return error!(node, "Unhandled operator (compiler error)"),
					}
				},
				NodeKind::Declaration { variable_name, value } => {
					if let Some(type_) = ast.nodes[value as usize].type_ {
						scopes.member_mut(variable_name).type_ = Some(type_);
					} else {
						return error!(node, "Cannot assign nothing to a variable");
					}
					None
				}
				NodeKind::Block { ref contents, label } => {
					let type_ = ast.nodes[*contents.last().unwrap() as usize].type_;

					if let Some(label) = label {
						if let Some(label_type) = self.label_types.get(&label) {
							if type_ != *label_type {
								return error!(
									ast.nodes[*contents.last().unwrap() as usize], 
									"Incompatible types, block doesn't return this type"
								);
							}
						} else {
							// TODO: Make unused label?
						}
					}

					type_
				}
				NodeKind::Skip { label, value } => {
					if let Some(label_type) = self.label_types.get(&label) {
						if value.map(|value| ast.nodes[value as usize].type_).flatten() != *label_type {
							return error!(node, "Incompatible types, block doesn't return this type");
						}
					} else {
						self.label_types.insert(
							label, 
							match value {
								Some(value) => ast.nodes[value as usize].type_,
								None => Some(types.insert(Type::new(TypeKind::EmptyType))),
							}
						);
					}

					None
				},

				// --- Type expressions ---
				NodeKind::GetType(_) => {
					Some(TYPE_TYPE_ID)
				}
				NodeKind::TypeFunctionPointer { ref arg_list, return_type } => {
					let kind = TypeKind::FunctionPointer {
						args: arg_list.iter().map(|&v| ast.nodes[v as usize].type_.unwrap())
							.collect(),
						returns: match return_type {
							Some(v) => ast.nodes[v as usize].type_.unwrap(),
							None => types.insert(Type::new(TypeKind::EmptyType)),
						}
					};

					Some(types.insert(Type::new(kind)))
				}
				NodeKind::TypeStruct { ref args } => {
					// Figure out the wanted offsets of the arguments.
					Some(types.insert_struct(args.iter().map(|(name, node)|
						(*name, ast.nodes[*node as usize].type_.unwrap())
					)))
				}
				NodeKind::TypePointer(pointing_to) => {
					let pointing_to_type = ast.nodes[pointing_to as usize].type_.unwrap();
					Some(types.insert(Type::new(TypeKind::Pointer(pointing_to_type))))
				}
				NodeKind::TypeBufferPointer(pointing_to) => {
					let pointing_to_type = ast.nodes[pointing_to as usize].type_.unwrap();
					Some(types.insert(Type::new(TypeKind::BufferPointer(pointing_to_type))))
				}
			};

			ast.nodes[self.node_id].type_ = type_kind;

			self.node_id += 1;
		}

		ast.is_typed = true;
		Ok(None)
	}
}
