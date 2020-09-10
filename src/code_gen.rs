use crate::prelude::*;
use std::fmt;

macro_rules! push_instr {
	($instrs:expr, $instr:expr) => {{
		// println!("{} {}", line!(), column!());
		$instrs.push($instr);
	}}
}

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
	Call {
		calling: Value, 
		returns: LocalId, 
		args: Vec<Value>,
	},
}

impl fmt::Debug for Instruction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Instruction::AddU64(a, b, c) => write!(f, "add {:?}, {:?}, {:?}", a, b, c),
			Instruction::SubU64(a, b, c) => write!(f, "sub {:?}, {:?}, {:?}", a, b, c),
			Instruction::MoveU64(a, b) => write!(f, "mov {:?}, {:?}", a, b),
			Instruction::JumpRel(a) => write!(f, "jump {:?}", a),
			Instruction::Call { calling, returns, ref args } => {
				write!(f, "call {:?} with ", calling)?;
				for arg in args.iter() {
					write!(f, ", {:?}", arg)?;
				}
				write!(f, ", return into ({:?})", returns)?;

				Ok(())
			}
		}
	}
}

// TODO: Make a custom type for this?
pub type LocalId = usize;

pub fn compile_expression(
	ast: &Ast, 
	scopes: &Scopes,
	resources: &Resources,
) -> (Locals, Vec<Instruction>, Value) {
	let mut locals = Locals::new();
	let mut node_values: Vec<Value> = Vec::with_capacity(ast.nodes.len());
	let mut instructions = Vec::new();

	let mut temporary_labels: Vec<(_, _, Option<Value>)> = Vec::new();
	let mut storage_locations = scopes.create_buffer(|| None);
	
	let mut function_arg_locations = Vec::new();

	for node in ast.nodes.iter() {
		if node.is_meta_data { 
			node_values.push(Value::Poison);
			continue; 
		}

		match node.kind {
			NodeKind::Identifier(member_id) => {
				let member = match storage_locations.member(member_id) {
					Some(value) => *value,
					None => panic!("Invalid thing, \nLocals: {:?}, \nScopes: {:?}, \nInstructions: {:?}", locals, scopes, instructions),
				};
				
				node_values.push(member);
			}
			NodeKind::DeclareFunctionArgument { variable_name, type_node } => {
				// Declaring a function argument is like moving the responsibility of setting
				// the locals to the caller. This should be done by the 'call' instruction,
				// which will set all the affected locals to the appropriate values.
				let location = Value::Local(locals.alloc_custom(Local {
					n_uses: 0,
					scope_member: Some(variable_name),
				}));

				*storage_locations.member_mut(variable_name) = Some(location);
				function_arg_locations.push(location);
				node_values.push(Value::Poison);
			}
			NodeKind::Declaration { variable_name, value } => {
				let location = Value::Local(locals.alloc_custom(Local {
					n_uses: 0,
					scope_member: Some(variable_name),
				}));
				*storage_locations.member_mut(variable_name) = Some(location);
				
				let input = node_values[value as usize];
				locals.note_usage(&location);
				locals.note_usage(&input);
				push_instr!(instructions, Instruction::MoveU64(location, input));
				node_values.push(Value::Poison);
			}
			NodeKind::Skip { label, value } => {
				let mut instruction_loc = instructions.len();

				let mut return_value_local = None;
				if let Some(value) = value {
					for (name, _, return_value) in &temporary_labels {
						if name == &label {
							// If we have a value, the type checker has to make sure that the
							// other skip also has a value
							return_value_local = Some(return_value.unwrap());
						}
					}

					if return_value_local.is_none() {
						return_value_local = Some(Value::Local(locals.alloc()));
					}

					let input = node_values[value as usize];
					locals.note_usage(&input);
					locals.note_usage(return_value_local.as_ref().unwrap());

					instruction_loc += 1;
					push_instr!(instructions, Instruction::MoveU64(return_value_local.unwrap(), input));
				}

				push_instr!(instructions, Instruction::JumpRel(-42069));

				temporary_labels.push((label, instruction_loc, return_value_local));
				node_values.push(Value::Poison);
			}
			NodeKind::Block { ref contents, label } => {
				let mut return_value_loc = None;

				if let Some(label) = label {
					for (_, instruction_loc, return_value) in 
						temporary_labels.drain_filter(|(l, _, _)| l == &label) 
					{
						if return_value.is_none() {
							instructions[instruction_loc] = 
								Instruction::JumpRel((instructions.len() - instruction_loc - 1) as i64);
						} else {
							instructions[instruction_loc] = 
								Instruction::JumpRel((instructions.len() - instruction_loc) as i64);
						}

						return_value_loc = return_value;
					}
				}

				let result = node_values[*contents.last().unwrap() as usize];
				match return_value_loc {
					Some(location) => {
						push_instr!(instructions, Instruction::MoveU64(location, result));
						node_values.push(location);
					}
					None => {
						node_values.push(result);
					}
				}
			}
			NodeKind::Number(num) => {
				// TODO: Check that the number fits, although I guess this should
				// be down further up in the pipeline
				node_values.push(Value::Constant(num as i64));
			}
			NodeKind::BinaryOperator { operator, left, right } => {
				let a = node_values[left as usize];
				let b = node_values[right as usize];
				locals.note_usage(&a);
				locals.note_usage(&b);

				let result = Value::Local(locals.alloc());

				match operator {
					Operator::Assign => {
						push_instr!(instructions, Instruction::MoveU64(a, b));

						locals.note_usage(&b);
						// TODO: Check if the result is used eventually, we will have a flag for if
						// the return value of an AstNode is used or not
						push_instr!(instructions, Instruction::MoveU64(result, b));
					}
					Operator::Add => 
						push_instr!(instructions, Instruction::AddU64(result, a, b)),
					Operator::Sub => 
						push_instr!(instructions, Instruction::SubU64(result, a, b)),
					_ => todo!()
				}

				locals.note_usage(&result);
				node_values.push(result);
				
				// I know what I'm doing, we are not copying these without reason!
				// locals.free_value(node_values[left as usize].clone());
				// locals.free_value(node_values[right as usize].clone());
			}
			NodeKind::EmptyLiteral => {
				node_values.push(Value::Poison);
			}
			NodeKind::FunctionCall { function_pointer, ref arg_list } => {
				let returns = locals.alloc();

				let args = arg_list.iter().map(|arg| node_values[*arg as usize]).collect();
				let calling = node_values[function_pointer as usize];

				push_instr!(instructions, Instruction::Call { calling, returns, args });

				node_values.push(Value::Local(returns));
			}
			NodeKind::Resource(id) => {
				let resource = resources.resource(id);
				match resource.kind {
					ResourceKind::CurrentlyUsed => 
						todo!("Deal with CurrentlyUsed resources in code_gen"),
					ResourceKind::Function { .. } => {
						node_values.push(Value::Constant(id as i64));
					}
					_ => todo!("Resource kind not dealt with in code gen"),
				}
			}
			_ => todo!()
		}
	}

	(locals, instructions, node_values.last().copied().unwrap_or(Value::Poison))
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
