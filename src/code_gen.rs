use crate::parser;
use crate::parser::{Scopes, ScopeId};
use crate::operator::Operator;
use std::fmt;

/// A 'Local' is the equivalent of a register, but there is an arbitrary amount
/// of locals possible.
/// All locals are u64(for now).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Value {
	Local(LocalId),
	/// An indirect local, with a byte offset.
	LocalIndirect(LocalId, i64),
	Constant(i64),
	Poison,
}

impl fmt::Debug for Value {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Value::Local(local) => write!(f, "({})", local),
			Value::LocalIndirect(value, offset) => write!(f, "[{}+{}]", value, offset),
			Value::Constant(value) => write!(f, "{}", value),
			Value::Poison => write!(f, "Poison"),
		}
	}
}

pub enum Instruction {
	AddU64(Value, Value, Value),
	SubU64(Value, Value, Value),
	MoveU64(Value, Value),
	JumpRel(i64),
}

impl fmt::Debug for Instruction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Instruction::AddU64(a, b, c) => write!(f, "add {:?}, {:?}, {:?}", a, b, c),
			Instruction::SubU64(a, b, c) => write!(f, "sub {:?}, {:?}, {:?}", a, b, c),
			Instruction::MoveU64(a, b) => write!(f, "mov {:?}, {:?}", a, b),
			Instruction::JumpRel(a) => write!(f, "jump {:?}", a),
		}
	}
}

// TODO: Make a custom type for this?
pub type LocalId = usize;

pub fn compile_expression(
	ast: &parser::Ast, 
	node: parser::AstNodeId,
	scopes: &mut Scopes,
	scope: ScopeId,
) -> (Locals, Vec<Instruction>) {
	let mut locals = Locals::new();
	let mut node_values: Vec<Value> = Vec::with_capacity(ast.nodes.len());
	let mut instructions = Vec::new();

	let mut temporary_labels = Vec::new();

	for (i, node) in ast.nodes.iter().enumerate() {
		match node.kind {
			parser::NodeKind::Identifier(member_id) => {
				let member = scopes.member(member_id).storage_location
					.expect("Undeclared variable in code_gen...");
				// We use the member twice
				
				// TODO: Fix in place assignment jankyness
				let new_loc = locals.clone(&member); // Value::Local(locals.alloc());
				// instructions.push(Instruction::MoveU64(new_loc, member));
				node_values.push(new_loc);
			}
			parser::NodeKind::Declaration { variable_name, value } => {
				let location = Value::Local(locals.alloc());
				scopes.member_mut(variable_name).storage_location 
					= Some(location);
				
				let input = node_values[value as usize];
				locals.note_usage(&location);
				locals.note_usage(&input);
				instructions.push(Instruction::MoveU64(location, input));
				locals.free_value(input);
				node_values.push(Value::Poison);
			}
			parser::NodeKind::Skip { label, value } => {
				let instruction_loc = instructions.len();
				if let Some(value) = value {
					let input = node_values[value as usize];
					locals.note_usage(&input);
					instructions.push(Instruction::MoveU64(Value::Local(9999), input));
					locals.free_value(input);
				}else {
					instructions.push(Instruction::MoveU64(Value::Poison, Value::Constant(9999)));
				}
				instructions.push(Instruction::JumpRel(-42069));

				temporary_labels.push((label, instruction_loc));
				node_values.push(Value::Poison);
			}
			parser::NodeKind::Block { ref contents, label } => {
				for &content in &contents[..contents.len() - 1] {
					locals.free_value(
						node_values[content as usize]
					);
				}

				let result = node_values[*contents.last().unwrap() as usize];
				node_values.push(result);

				for member in scopes.members(node.scope) {
					if let Some(location) = member.storage_location {
						locals.free_value(location);
					} else {
						println!("WARNING!!! {:?} Member in scope not declared", 
							member.declaration_location);
					}
				}

				if let Some(label) = label {
					for (temp_label, instruction_loc) in 
						temporary_labels.drain_filter(|(l, _)| l == &label) 
					{
						if let Instruction::MoveU64(a, _) = &mut instructions[instruction_loc] {
							locals.note_usage(&result);
							// TODO: Stability, 
							// check if this is a constant
							*a = result;
						}

						instructions[instruction_loc + 1] = 
							Instruction::JumpRel((instructions.len() - instruction_loc) as i64 - 2);
					}
				}
			}
			parser::NodeKind::Number(num) => {
				// TODO: Check that the number fits, although I guess this should
				// be down further up in the pipeline
				node_values.push(Value::Constant(num as i64));
			}
			parser::NodeKind::BinaryOperator { operator, left, right } => {
				let a = node_values[left as usize];
				let b = node_values[right as usize];
				locals.note_usage(&a);
				locals.note_usage(&b);

				let result = Value::Local(locals.alloc());

				match operator {
					Operator::Assign => {
						instructions.push(Instruction::MoveU64(a, b));
						// TODO: Check if the result is used eventually, we will have a flag for if
						// the return value of an AstNode is used or not
						instructions.push(Instruction::MoveU64(result, b));
					}
					Operator::Add => 
						instructions.push(Instruction::AddU64(result, a, b)),
					Operator::Sub => 
						instructions.push(Instruction::SubU64(result, a, b)),
					_ => todo!()
				}

				locals.note_usage(&result);
				node_values.push(result);
				
				// I know what I'm doing, we are not copying these without reason!
				locals.free_value(node_values[left as usize].clone());
				locals.free_value(node_values[right as usize].clone());
			}
			parser::NodeKind::EmptyLiteral => {
				node_values.push(Value::Poison);
			}
			_ => todo!()
		}
	}

	(locals, instructions)
}

// TODO!!!
// We're just going to assume all return types are i64:s for now, when typing is done 
// this will not be the case!

///
/// Allocates locals,
/// keeps track of which ones are used and unused,
/// and keeps track of how many times each one has been used.
/// The ones that have been used a lot are preferred, basically
/// we want a few to be used a lot and most to be used just a little bit,
/// because if we think about what happens on a real computer, only some
/// of these are going to be in actual registers, so we want the ones
/// that are used a lot to be in registers, and those are going to be used
/// a lot.
///
pub struct Locals {
	// (number of locks, total number of reads / writes)
	pub locals: Vec<(u32, u32)>,

	free_locals: Vec<(LocalId, u32)>,
}

impl Locals {
	fn new() -> Self {
		Locals { locals: Vec::new(), free_locals: Vec::new() }
	}

	fn alloc(&mut self) -> LocalId {
		if self.free_locals.len() > 0 {
			let mut best_local = 0;
			let mut most_uses = 0;
			for (i, &(_, uses)) in self.free_locals.iter().enumerate() {
				if uses >= most_uses {
					best_local = i;
				}
			}
			let local = self.free_locals[best_local].0;
			self.locals[local].0 += 1;
			self.free_locals.remove(best_local);
			local
		} else {
			let id = self.locals.len();
			self.locals.push((1, 0));
			id 
		}
	}

	fn clone(&mut self, value: &Value) -> Value {
		let local = match *value {
			Value::Local(local) => local,
			Value::LocalIndirect(local, offset) => local,
			Value::Constant(_) => return *value, // Constants do not use locals
			Value::Poison => return Value::Poison,
		};

		assert!(self.locals[local].0 > 0);
		self.locals[local].0 += 1;

		value.clone()
	}

	fn note_usage(&mut self, value: &Value) {
		let local = match *value {
			Value::Local(local) => local,
			Value::LocalIndirect(local, offset) => local,
			Value::Constant(_) => return, // Constants do not use locals
			Value::Poison => panic!("Tried using poison"),
		};

		assert!(self.locals[local].0 > 0);
		self.locals[local ].1 += 1;
	}

	fn free_value(&mut self, value: Value) {
		let local = match value {
			Value::Local(local) => local,
			Value::LocalIndirect(local, offset) => local,
			Value::Constant(_) => return, // Constants do not use locals
			Value::Poison => return,
		};

		assert!(self.locals[local ].0 > 0);
		self.locals[local ].0 -= 1;

		if self.locals[local ].0 == 0 {
			self.free_locals.push((local, self.locals[local ].1));
		}
	}
}
