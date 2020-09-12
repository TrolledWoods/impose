use crate::prelude::*;
use crate::parser::ScopeMemberId;
use std::collections::HashMap;

pub const U64_TYPE_ID:    TypeId = TypeId::create_raw(0);
pub const STRING_TYPE_ID: TypeId = TypeId::create_raw(1);

create_id!(TypeId);

pub struct Types {
	types: IdVec<Type, TypeId>,
}

impl Types {
	pub fn new() -> Self {
		let mut types = IdVec::new();
		assert_eq!(types.push(Type::new(TypeKind::Primitive(PrimitiveKind::U64))), U64_TYPE_ID);
		assert_eq!(types.push(Type::new(TypeKind::String)), STRING_TYPE_ID);
		Self { types }
	}

	// TODO: This function is deprecated
	pub fn u64(&mut self) -> TypeId {
		U64_TYPE_ID
	}

	pub fn insert_function(&mut self, args: Vec<TypeId>, returns: TypeId) -> TypeId {
		self.insert(Type::new(TypeKind::FunctionPointer {
			args,
			returns,
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

	pub fn get_if(&self, type_: Option<TypeId>) -> Option<&Type> {
		type_.map(|type_| self.types.get(type_))
	}

	pub fn print(&self, type_: TypeId) {
		match self.types.get(type_).kind {
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

#[derive(Debug, PartialEq)]
pub struct Type {
	pub loc: Option<CodeLoc>,
	pub kind: TypeKind,
	pub representation: Vec<PrimitiveKind>,
}

impl Type {
	pub fn new(kind: TypeKind) -> Self {
		Type {
			loc: None,
			kind,
			representation: Vec::new(), // TODO: Make good representation
		}
	}
}

// TODO: Make an empty type to differentiate between no type and
// a type that isn't computed yet.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
	FunctionPointer {
		args: Vec<TypeId>,
		returns: TypeId,
	},
	String,
	Primitive(PrimitiveKind),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum PrimitiveKind {
	U64,
}

pub struct AstTyper {
	/// Each element in this corresponds to an ast node.
	/// Once done, this list should be the same length as the ast.
	pub types: Vec<Option<TypeId>>,
	node_id: usize,
	label_types: HashMap<ScopeMemberId, Option<TypeId>>,
}

impl AstTyper {
	pub fn new(ast: &Ast) -> AstTyper {
		AstTyper {
			types: Vec::with_capacity(ast.nodes.len()),
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
	) -> Result<Option<Dependency>> {
		while self.node_id < ast.nodes.len() {
			debug_assert_eq!(self.types.len(), self.node_id);
			let node = &ast.nodes[self.node_id];

			let type_kind = match node.kind {
				NodeKind::Number(_) => {
					Some(types.insert(Type::new(TypeKind::Primitive(PrimitiveKind::U64))))
				}
				NodeKind::Type(ref kind) => {
					Some(types.insert(Type::new(kind.clone())))
				}
				NodeKind::DeclareFunctionArgument { variable_name, type_node } => {
					scopes.member_mut(variable_name).type_ 
						= Some(self.types[type_node as usize].unwrap());
					None
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
					None
				}
				NodeKind::Identifier(id) => {
					let member = scopes.member(id);
					if member.kind == ScopeMemberKind::LocalVariable || member.kind == ScopeMemberKind::FunctionArgument {
						if let Some(type_) = member.type_ {
							Some(type_)
						} else {
							return_error!(node, "Type is not assigned, is the variable not declared? (This is probably a compiler problem)");
						}
					} else if let ScopeMemberKind::Constant(id) = member.kind {
						if let Some(type_) = resources.resource(id).type_ {
							Some(type_)
						} else {
							return Ok(Some(Dependency::Type(id)));
						}
					} else {
						return_error!(node, "Typing does not handle {:?} scope members yet", member.kind);
					}
				}
				NodeKind::FunctionCall { function_pointer, ref arg_list } => {
					// TODO: Check if the types in the arg_list are the same as the function
					// pointer type
					let func_type = types.get_if(self.types[function_pointer as usize]);
					if let Some(Type { kind: TypeKind::FunctionPointer { ref args, returns }, .. }) 
						= func_type 
					{
						if arg_list.len() != args.len() {
							return_error!(node.loc, "Expected {} arguments, got {}", 
								args.len(), arg_list.len());
						}

						for (wanted, got) in args.iter().zip(arg_list) {
							if Some(*wanted) != self.types[*got as usize] {
								return_error!(ast.get_node(*got as u32), "Expected (TODO: Print type here), got (TODO: Print type here)");
							}
						}

						Some(*returns)
					} else {
						return_error!(node, "This is not a function pointer, yet a function call was attemted on it");
					}
				}
				NodeKind::BinaryOperator { left: _, right, .. } => {
					// TODO: Make a better operator system
					self.types[right as usize]
				},
				NodeKind::UnaryOperator { operand, .. } => {
					self.types[operand as usize]
				},
				NodeKind::Declaration { variable_name, value } => {
					if let Some(type_) = self.types[value as usize] {
						scopes.member_mut(variable_name).type_ = Some(type_);
					} else {
						return_error!(node, "Cannot assign nothing to a variable");
					}
					None
				}
				NodeKind::Block { ref contents, label } => {
					let type_ = self.types[*contents.last().unwrap() as usize];

					if let Some(label) = label {
						if let Some(label_type) = self.label_types.get(&label) {
							if type_ != *label_type {
								return_error!(
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
						if value.map(|value| self.types[value as usize]).flatten() != *label_type {
							return_error!(node, "Incompatible types, block doesn't return this type");
						}
					} else {
						self.label_types.insert(
							label, 
							value.map(|value| self.types[value as usize]).flatten()
						);
					}

					None
				},
			};

			self.types.push(type_kind);

			self.node_id += 1;
		}

		ast.is_typed = true;
		Ok(None)
	}
}
