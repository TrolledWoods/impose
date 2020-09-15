use std::collections::HashMap;

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
pub const STRING_TYPE_ID: TypeId = TypeId::create_raw(3);
pub const EMPTY_TYPE_ID:  TypeId = TypeId::create_raw(4);

create_id!(TypeId);

pub struct Types {
	types: IdVec<Type, TypeId>,
}

impl Types {
	pub fn new() -> Self {
		let mut types = IdVec::new();
		assert_eq!(types.push(Type::new(TypeKind::Type)), TYPE_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::Primitive(PrimitiveKind::U64))), U64_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::Primitive(PrimitiveKind::U32))), U32_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::String)), STRING_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::EmptyType)), EMPTY_TYPE_ID);
		Self { types }
	}

	pub fn handle(&self, id: TypeId) -> TypeHandle {
		let type_ = self.types.get(id);
		TypeHandle { id, size: type_.size, align: type_.align }
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
		match self.types.get(type_).kind {
			TypeKind::EmptyType => print!("Empty"),
			TypeKind::Type => print!("Type"),
			TypeKind::Struct { ref members } => {
				print!("struct{{ ");
				for (i, (name, offset, member)) in members.iter().enumerate() {
					if i > 0 { print!(", "); }

					print!("{}[{}]: ", name, offset);
					self.print(member.id);
				}
				print!("}}");
			}
			TypeKind::Pointer(sub_type) => {
				print!("&");
				self.print(sub_type);
			}
			TypeKind::FunctionPointer { ref args, returns } => {
				print!("(");
				for (i, arg) in args.iter().enumerate() {
					if i > 0 { print!(", "); }
					self.print(*arg);
				}
				print!(") -> (");
				self.print(returns);
				print!(")");
			}
			TypeKind::String => {
				print!("string");
			}
			TypeKind::Primitive(primitive_kind) => {
				print!("{:?}", primitive_kind);
			}
		}
	}
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
			TypeKind::EmptyType => (0, 1),
			TypeKind::Type => (8, 8),
			TypeKind::Primitive(PrimitiveKind::U64) => (8, 8),
			TypeKind::Primitive(PrimitiveKind::U32) => (4, 4),
			TypeKind::String => (8, 8),
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
	FunctionPointer {
		args: Vec<TypeId>,
		returns: TypeId,
	},
	Type,
	String,
	Primitive(PrimitiveKind),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum PrimitiveKind {
	U32,
	U64,
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
				NodeKind::Member { contains, .. } => {
					ast.nodes[contains as usize].type_
				}
				NodeKind::Number(_) => {
					Some(types.insert(Type::new(TypeKind::Primitive(PrimitiveKind::U64))))
				}
				NodeKind::DeclareFunctionArgument { variable_name, type_node } => {
					scopes.member_mut(variable_name).type_ 
						= Some(ast.nodes[type_node as usize].type_.unwrap());
					None
				}
				NodeKind::MemberAccess(member, sub_name) => {
					let id = ast.nodes[member as usize].type_.unwrap();
					let type_kind = &types.get(id).kind;
					
					match type_kind {
						TypeKind::Primitive(PrimitiveKind::U64) => {
							if sub_name == "low" {
								Some(U32_TYPE_ID)
							} else if sub_name == "high" {
								Some(U32_TYPE_ID)
							} else {
								return error!(node, "This member does not exist on U64");
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
				NodeKind::LocationMarker => None,
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
						return Ok(Some(Dependency::Type(id)));
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
				NodeKind::Identifier(id) => {
					let member = scopes.member(id);
					match member.kind {
						ScopeMemberKind::LocalVariable | ScopeMemberKind::FunctionArgument => {
							if let Some(type_) = member.type_ {
								Some(type_)
							} else {
								return error!(node, "Type is not assigned, is the variable not declared? (This is probably a compiler problem)");
							}
						} 
						ScopeMemberKind::Constant(id) => {
							if let Some(type_) = resources.resource(id).type_ {
								Some(type_)
							} else {
								return Ok(Some(Dependency::Type(id)));
							}
						}
						ScopeMemberKind::UndefinedDependency(_) => {
							return Ok(Some(Dependency::Constant(id)));
						}
						ScopeMemberKind::Label => {
							return error!(node, "This is not a variable, it is a label!");
						}
						ScopeMemberKind::Indirect(_) => { 
							unreachable!("scope.member function should never return Indirect");
						}
					}
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
								return error!(ast.get_node(*got as u32), "Expected {:?}, got {:?}",
									wanted, 
									ast.nodes[*got as usize].type_
								);
							}
						}

						Some(*returns)
					} else {
						return error!(node, "This is not a function pointer, yet a function call was attemted on it");
					}
				}
				NodeKind::BinaryOperator { left, right, operator: _ } => {
					if ast.nodes[right as usize].type_ != ast.nodes[left as usize].type_ {
						return error!(node, "This operator needs both operands to be of the same type");
					}

					ast.nodes[right as usize].type_
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
				NodeKind::TypeIdentifier(member) => {
					let member = scopes.member(member);
					match member.kind {
						ScopeMemberKind::Constant(id) => {
							if let Some(type_) = resources.resource(id).type_ {
								if type_ != TYPE_TYPE_ID {
									return error!(node, "A Type identifier has to contain a type!");
								}
							} else {
								return Ok(Some(Dependency::Type(id)));
							}

							match resources.resource(id).kind {
								ResourceKind::Value { value: Some(ref value), .. } => {
									if let &[a, b, c, d, e, f, g, h] = value.as_slice() {
										let id = usize::from_le_bytes([a, b, c, d, e, f, g, h]);
										if id >= types.types.len() {
											return error!(node, "Invalid type id");
										}
										Some(TypeId::create(id as u32))
									} else {
										unreachable!("The value of a type has to be a 64 bit value");
									}
								}
								ResourceKind::Value { value: None, .. } => {
									return Ok(Some(Dependency::Value(id)));
								}
								_ => return error!(node, "A Type identifier has to contain a type!"),
							}
						}
						_ => return error!(node, "A Type identifier has to be constant"), 
					}
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
					let mut full_member_data = Vec::new();

					let mut offset = 0;
					for (name, member_type_node) in args {
						let member_type_handle = types.handle(
							ast.nodes[*member_type_node as usize].type_.unwrap()
						);
						let aligned_off = to_aligned(member_type_handle.align, offset);
						full_member_data.push((*name, aligned_off, member_type_handle));

						offset = aligned_off + member_type_handle.size;
					}

					let kind = TypeKind::Struct {
						members: full_member_data,
					};

					Some(types.insert(Type::new(kind)))
				}
				NodeKind::TypePointer(pointing_to) => {
					let pointing_to_type = ast.nodes[pointing_to as usize].type_.unwrap();
					Some(types.insert(Type::new(TypeKind::Pointer(pointing_to_type))))
				}
			};

			ast.nodes[self.node_id].type_ = type_kind;

			self.node_id += 1;
		}

		ast.is_typed = true;
		Ok(None)
	}
}
