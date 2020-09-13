use crate::prelude::*;
use std::fmt;
use std::collections::HashMap;

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
	/// Temporary instruction. Cannot be run, because it's supposed to be overwritten later.
	Temporary,
	AddU64(Value, Value, Value),
	SubU64(Value, Value, Value),
	MoveU64(Value, Value),
	JumpRel(i64),
	JumpRelIfZero(Value, i64),
	Call {
		calling: Value, 
		returns: LocalId, 
		args: Vec<Value>,
	},
}

impl fmt::Debug for Instruction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Instruction::Temporary => write!(f, "temp"),
			Instruction::AddU64(a, b, c) => write!(f, "add {:?}, {:?}, {:?}", a, b, c),
			Instruction::SubU64(a, b, c) => write!(f, "sub {:?}, {:?}, {:?}", a, b, c),
			Instruction::MoveU64(a, b) => write!(f, "mov {:?}, {:?}", a, b),
			Instruction::JumpRel(a) => write!(f, "jump {:?}", a),
			Instruction::JumpRelIfZero(value, a) => write!(f, "jump {:?} if {:?} == 0", a, value),
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

create_id!(LocalId);

// TODO: Add a struct with data about compiling an expression, so that we can keep going
// at the same point that we stopped if there is an undefined dependency.
pub fn compile_expression(
	ast: &Ast, 
	scopes: &mut Scopes,
	resources: &Resources,
) -> std::result::Result<(Locals, Vec<Instruction>, Value), Dependency> {
	let mut locals = Locals::new();
	let mut node_values: Vec<Value> = Vec::with_capacity(ast.nodes.len());
	let mut instructions = Vec::new();

	let mut temporary_labels: Vec<(_, _, Option<Value>)> = Vec::new();
	let mut instruction_locations: HashMap<AstNodeId, usize> = HashMap::new();
	
	let mut function_arg_locations = Vec::new();

	for (node_id, node) in ast.nodes.iter().enumerate().map(|(a, b)| (a as u32, b)) {
		if node.is_meta_data { 
			node_values.push(Value::Poison);
			continue; 
		}

		match node.kind {
			NodeKind::Identifier(member_id) => {
				match scopes.member(member_id).kind {
					ScopeMemberKind::UndefinedDependency(_) => panic!("Cannot run code_gen on undefined dependencies(they have to have been caught in the typer)"),
					ScopeMemberKind::Indirect(_) => unreachable!("the member function on Scopes should handle indirects and shouldn't return one of them"),
					ScopeMemberKind::LocalVariable | ScopeMemberKind::FunctionArgument => {
						let member = match scopes.member(member_id).storage_loc {
							Some(value) => value,
							None => panic!("Invalid thing, \nLocals: {:?}, \nScopes: {:?}, \nInstructions: {:?}", locals, scopes, instructions),
						};
						
						node_values.push(Value::Local(member));
					}
					ScopeMemberKind::Constant(id) => {
						node_values.push(get_resource_constant(resources, id)?);
					}
					ScopeMemberKind::Label => panic!("Cannot do labels"),
				}
			}
			NodeKind::DeclareFunctionArgument { variable_name, .. } => {
				// Declaring a function argument is like moving the responsibility of setting
				// the locals to the caller. This should be done by the 'call' instruction,
				// which will set all the affected locals to the appropriate values.
				let location = locals.alloc_custom(Local {
					n_uses: 0,
					scope_member: Some(variable_name),
				});

				scopes.member_mut(variable_name).storage_loc = Some(location);
				function_arg_locations.push(Value::Local(location));
				node_values.push(Value::Poison);
			}
			NodeKind::Declaration { variable_name, value } => {
				let location = locals.alloc_custom(Local {
					n_uses: 0,
					scope_member: Some(variable_name),
				});
				scopes.member_mut(variable_name).storage_loc = Some(location);
				
				let input = node_values[value as usize];
				locals.note_usage(&Value::Local(location));
				locals.note_usage(&input);
				push_instr!(instructions, Instruction::MoveU64(Value::Local(location), input));
				node_values.push(Value::Poison);
			}
			NodeKind::Member { child_of, contains, id } => {
				let mut node_value = None;

				match (&ast.nodes[child_of as usize].kind, id) {
					(NodeKind::If { .. }, 0) => {
						instruction_locations.insert(node_id, instructions.len());
						// Will be a jump instruction over the body
						push_instr!(instructions, Instruction::Temporary);
					}
					(NodeKind::If { .. }, 1) => {
						// TODO: Remove this state
					}
					(NodeKind::IfWithElse { .. }, 0) => {
						instruction_locations.insert(node_id, instructions.len());
						// Jump instruction to skip the true body and jump to the else
						push_instr!(instructions, Instruction::Temporary);
					}
					(NodeKind::IfWithElse { .. }, 1) => {
						// Instruction to move the value into a new local, so that the else can
						// also use that same local
						let local = locals.alloc();
						push_instr!(
							instructions, 
							Instruction::MoveU64(Value::Local(local), node_values[contains as usize])
						);
						node_value = Some(Value::Local(local));

						// Instruction to jump to to skip the if body
						instruction_locations.insert(node_id, instructions.len());

						// Jump instruction to skip else
						push_instr!(instructions, Instruction::Temporary);
					}
					(NodeKind::IfWithElse { .. }, 2) => {
						// Instruction to jump to to skip the else
						instruction_locations.insert(node_id, instructions.len());
					}
					(node_kind, id) => 
						panic!("{:?} does not have a member with id {}", node_kind, id),
				}

				let node_value = node_value.unwrap_or_else(|| node_values[contains as usize]);
				node_values.push(node_value);
			}
			NodeKind::If { condition, .. } => {
				let condition_instr_loc = *instruction_locations.get(&condition).unwrap();
				let current_instr_loc   = instructions.len();
				instructions[condition_instr_loc] = Instruction::JumpRelIfZero(
					node_values[condition as usize],
					current_instr_loc as i64 - condition_instr_loc as i64 - 1
				);

				node_values.push(Value::Poison);
			}
			NodeKind::IfWithElse { condition, true_body, false_body } => {
				let condition_instr_loc = *instruction_locations.get(&condition).unwrap();
				let true_body_instr_loc = *instruction_locations.get(&true_body).unwrap();
				let current_instr_loc   = instructions.len();

				instructions[condition_instr_loc] = Instruction::JumpRelIfZero(
					node_values[condition as usize],
					// We don't subtract one here, because we wanna move past the Jump that skips
					// over the else block at true_body_instr_loc
					true_body_instr_loc as i64 - condition_instr_loc as i64
				);

				instructions[true_body_instr_loc] = Instruction::JumpRel(
					// Move past the MoveU64 that moves the false body return value into the
					// true body return value
					current_instr_loc as i64 - true_body_instr_loc as i64
				);

				push_instr!(instructions, Instruction::MoveU64(
					node_values[true_body as usize], 
					node_values[false_body as usize],
				));

				let true_body_value = node_values[true_body as usize];
				node_values.push(true_body_value);
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
				node_values.push(Value::Constant(0));
			}
			NodeKind::FunctionCall { function_pointer, ref arg_list } => {
				let returns = locals.alloc();

				let args = arg_list.iter().map(|arg| node_values[*arg as usize]).collect();
				let calling = node_values[function_pointer as usize];

				push_instr!(instructions, Instruction::Call { calling, returns, args });

				node_values.push(Value::Local(returns));
			}
			NodeKind::Resource(id) => {
				node_values.push(get_resource_constant(resources, id)?)
			}
			_ => todo!()
		}
	}

	Ok((locals, instructions, node_values.last().copied().unwrap_or(Value::Poison)))
}

fn get_resource_constant(resources: &Resources, id: ResourceId) 
	-> std::result::Result<Value, Dependency>
{
	let resource = resources.resource(id);
	match resource.kind {
		ResourceKind::ExternalFunction { .. } |
		ResourceKind::Function { .. } | 
		ResourceKind::String(_) =>
			Ok(Value::Constant(id.into_index() as i64)),
		ResourceKind::CurrentlyUsed => 
			todo!("Deal with CurrentlyUsed resources in code_gen"),
		ResourceKind::Value { value, .. } => {
			if let Some(value) = value {
				Ok(Value::Constant(value))
			} else {
				Err(Dependency::Value(id))
			}
		}
	}
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
	pub locals: IdVec<Local, LocalId>,
}

impl Locals {
	fn new() -> Self {
		Locals { locals: IdVec::new() }
	}

	fn alloc(&mut self) -> LocalId {
		self.locals.push(Local {
			n_uses: 0,
			scope_member: None,
		})
	}

	fn alloc_custom(&mut self, local: Local) -> LocalId {
		assert_eq!(local.n_uses, 0);
		self.locals.push(local)
	}

	fn note_usage(&mut self, value: &Value) {
		match *value {
			Value::Local(local) => {
				self.locals.get_mut(local).n_uses += 1;
			}
			Value::Constant(_) => (),
			Value::Poison => (),
		}
	}
}
