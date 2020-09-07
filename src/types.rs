use crate::prelude::*;
use crate::parser::ScopeMemberId;
use std::collections::HashMap;
use std::fmt;

pub type TypeId = usize;

pub struct Types {
	types: Vec<Type>,
}

impl Types {
	pub fn new() -> Self {
		Types { types: Vec::new() }
	}

	pub fn insert(&mut self, type_: Type) -> TypeId {
		// Try to find a type that is already the same.
		for (i, self_type) in self.types.iter().enumerate() {
			if *self_type == type_ {
				return i as TypeId;
			}
		}

		let id = self.types.len();
		self.types.push(type_);
		id
	}

	pub fn get(&self, type_: TypeId) -> &Type {
		&self.types[type_]
	}

	pub fn get_if(&self, type_: Option<TypeId>) -> Option<&Type> {
		type_.map(|type_| &self.types[type_])
	}

	pub fn print(&self, type_: TypeId) {
		match self.types[type_].kind {
			TypeKind::FunctionPointer { ref args, returns } => {
				print!("(");
				for (i, arg) in args.iter().enumerate() {
					if i > 0 { print!(", "); }
					self.print(*arg);
				}
				print!(")");
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

	pub fn new_loc(loc: &impl Location, kind: TypeKind) -> Self {
		Type {
			loc: Some(loc.get_location()),
			kind,
			representation: Vec::new(), // TODO: Make good representation
		}
	}
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
	FunctionPointer {
		args: Vec<TypeId>,
		returns: TypeId,
	},
	Primitive(PrimitiveKind),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum PrimitiveKind {
	U64,
	Pointer,
}

pub struct AstTyper {
	/// Each element in this corresponds to an ast node.
	/// Once done, this list should be the same length as the ast.
	pub types: Vec<Option<TypeId>>,
	node_id: usize,

	pub scope_variables: ScopeBuffer<Option<TypeId>>,
	label_types: HashMap<ScopeMemberId, Option<TypeId>>,
}

impl AstTyper {
	pub fn new(ast: &Ast) -> AstTyper {
		AstTyper {
			types: Vec::with_capacity(ast.nodes.len()),
			node_id: 0,
			scope_variables: ast.scopes.create_buffer(|| None),
			label_types: HashMap::new(),
		}
	}

	pub fn try_type_ast(&mut self, types: &mut Types, ast: &Ast) -> Result<()> {
		while self.node_id < ast.nodes.len() {
			debug_assert_eq!(self.types.len(), self.node_id);
			let node = &ast.nodes[self.node_id];

			let type_kind = match node.kind {
				NodeKind::Number(i128) => {
					Some(types.insert(Type::new(TypeKind::Primitive(PrimitiveKind::U64))))
				}
				NodeKind::String(ref string) => {
					todo!();
				}
				NodeKind::EmptyLiteral => {
					None
				}
				NodeKind::Identifier(id) => {
					*self.scope_variables.member(id)
				}
				NodeKind::FunctionDeclaration { routine_id } => {
					None
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

						for (got, wanted) in args.iter().zip(arg_list) {
							if self.types[*got as usize] != self.types[*wanted as usize] {
								return_error!(ast.get_node(*got as u32), "Expected (TODO: Print type here), got (TODO: Print type here)");
							}
						}

						self.types[*returns as usize]
					} else {
						return_error!(&node.loc, "This is not a function pointer, yet a function call was attemted on it");
					}
				}
				NodeKind::BinaryOperator { operator, left, right } => {
					self.types[right as usize]
				},
				NodeKind::UnaryOperator { operator, operand, } => {
					self.types[operand as usize]
				},
				NodeKind::Declaration { variable_name, value } => {
					*self.scope_variables.member_mut(variable_name) = self.types[value as usize];
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

		Ok(())
	}
}
