use crate::{ parser::{self, Scopes, ScopeMemberId}, operator::Operator };
use std::fmt;

/// A 'Local' is the equivalent of a register, but there is an arbitrary amount
/// of locals possible.
/// All locals are u64(for now).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Value {
	Local(LocalId),
	Constant(i64),
	Poison,
}

impl fmt::Debug for Value {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Value::Local(local) => write!(f, "({})", local),
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
	scopes: &mut Scopes,
) -> (Locals, Vec<Instruction>) {
	let mut locals = Locals::new();
	let mut node_values: Vec<Value> = Vec::with_capacity(ast.nodes.len());
	let mut instructions = Vec::new();

	let mut temporary_labels = Vec::new();

	for node in ast.nodes.iter() {
		match node.kind {
			parser::NodeKind::Identifier(member_id) => {
				let member = match scopes.member(member_id).storage_location {
					Some(value) => value,
					None => panic!("Invalid thing, \nLocals: {:?}, \nScopes: {:?}, \nInstructions: {:?}", locals, scopes, instructions),
				};
				
				// TODO: Fix in place assignment jankyness(probably by differentiating
				// between lvalues and rvalues).
				node_values.push(member);
			}
			parser::NodeKind::Declaration { variable_name, value } => {
				let location = Value::Local(locals.alloc_custom(Local {
					n_uses: 0,
					scope_member: Some(variable_name),
				}));
				scopes.member_mut(variable_name).storage_location 
					= Some(location);
				
				let input = node_values[value as usize];
				locals.note_usage(&location);
				locals.note_usage(&input);
				instructions.push(Instruction::MoveU64(location, input));
				node_values.push(Value::Poison);
			}
			parser::NodeKind::Skip { label, value } => {
				let instruction_loc = instructions.len();
				if let Some(value) = value {
					let input = node_values[value as usize];
					locals.note_usage(&input);
					instructions.push(Instruction::MoveU64(Value::Local(9999), input));
				}else {
					instructions.push(Instruction::MoveU64(Value::Poison, Value::Constant(9999)));
				}
				instructions.push(Instruction::JumpRel(-42069));

				temporary_labels.push((label, instruction_loc));
				node_values.push(Value::Poison);
			}
			parser::NodeKind::Block { ref contents, label } => {
				/*for &content in &contents[..contents.len() - 1] {
					locals.free_value(
						node_values[content as usize]
					);
				}*/

				let result = node_values[*contents.last().unwrap() as usize];
				node_values.push(result);

				/*for member in scopes.members(node.scope) {
					if let Some(location) = member.storage_location {
						locals.free_value(location);
					} else {
						println!("WARNING!!! {:?} Member in scope not declared", 
							member.declaration_location);
					}
				}*/

				if let Some(label) = label {
					for (_, instruction_loc) in 
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

						locals.note_usage(&b);
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
				// locals.free_value(node_values[left as usize].clone());
				// locals.free_value(node_values[right as usize].clone());
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

#[derive(Debug, Clone)]
pub struct Local {
	// type_: PrimitiveType,
	n_uses: u32,
	pub scope_member: Option<ScopeMemberId>,
}

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
#[derive(Debug)]
pub struct Locals {
	pub locals: Vec<Local>,
}

impl Locals {
	fn new() -> Self {
		Locals { locals: Vec::new() }
	}

	fn alloc(&mut self) -> LocalId {
		let id = self.locals.len();
		self.locals.push(Local {
			n_uses: 0,
			scope_member: None,
		});
		id
	}

	fn alloc_custom(&mut self, local: Local) -> LocalId {
		assert_eq!(local.n_uses, 0);
		let id = self.locals.len();
		self.locals.push(local);
		id
	}

	fn note_usage(&mut self, value: &Value) {
		match *value {
			Value::Local(local) => {
				self.locals[local].n_uses += 1;
			}
			Value::Constant(_) => (),
			Value::Poison => (),
		}
	}
}
