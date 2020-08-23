use crate::parser;
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
}

impl fmt::Debug for Value {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Value::Local(local) => write!(f, "({})", local),
			Value::LocalIndirect(value, offset) => write!(f, "[{}+{}]", value, offset),
			Value::Constant(value) => write!(f, "{}", value),
		}
	}
}

pub enum Instruction {
	AddU64(Value, Value, Value),
	SubU64(Value, Value, Value),
	MoveU64(Value, Value),
}

impl fmt::Debug for Instruction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Instruction::AddU64(a, b, c) => write!(f, "add {:?}, {:?}, {:?}", a, b, c),
			Instruction::SubU64(a, b, c) => write!(f, "sub {:?}, {:?}, {:?}", a, b, c),
			Instruction::MoveU64(a, b) => write!(f, "mov {:?}, {:?}", a, b),
		}
	}
}

// TODO: Make a custom type for this?
pub type LocalId = usize;

pub fn compile_expression(
	ast: &parser::Ast, 
	node: parser::AstNodeId,
) -> (Locals, Vec<Instruction>) {
	let mut locals = Locals::new();
	let mut node_values = Vec::with_capacity(ast.nodes.len());
	let mut instructions = Vec::new();

	for (i, node) in ast.nodes.iter().enumerate() {
		match node.kind {
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

	fn note_usage(&mut self, value: &Value) {
		let local = match *value {
			Value::Local(local) => local,
			Value::LocalIndirect(local, offset) => local,
			Value::Constant(_) => return, // Constants do not use locals
		};

		assert!(self.locals[local].0 > 0);
		self.locals[local ].1 += 1;
	}

	fn free(&mut self, local: LocalId) {
		assert!(self.locals[local ].0 > 0);
		self.locals[local ].0 -= 1;

		if self.locals[local ].0 == 0 {
			self.free_locals.push((local, self.locals[local ].1));
		}
	}

	fn free_value(&mut self, value: Value) {
		let local = match value {
			Value::Local(local) => local,
			Value::LocalIndirect(local, offset) => local,
			Value::Constant(_) => return, // Constants do not use locals
		};

		assert!(self.locals[local ].0 > 0);
		self.locals[local ].0 -= 1;

		if self.locals[local ].0 == 0 {
			self.free_locals.push((local, self.locals[local ].1));
		}
	}
}
