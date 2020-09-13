use crate::prelude::*;
use crate::code_gen::{Instruction, Locals, Value};

fn set_value(locals: &mut [i64], value: Value, num: i64) {
	match value {
		Value::Local(local) => locals[local.into_index()] = num,
		Value::Constant(_) => panic!("Cannot set constant"),
		Value::Poison => panic!("Cannot set poison"),
	}
}

fn get_value(locals: &[i64], value: Value) -> i64 {
	match value {
		Value::Local(local) => locals[local.into_index()],
		Value::Constant(i) => i,
		Value::Poison => panic!("Cannot get poison"),
	}
}

pub fn run_instructions(
	locals: &Locals, 
	instructions: &[Instruction], 
	result_value: Value, 
	resources: &Resources
) -> i64 {
	let mut local_data = vec![0; locals.locals.len()];
	run_instructions_with_locals(
		locals,
		instructions,
		result_value,
		&mut local_data,
		resources,
	)
}

pub fn run_instructions_with_locals(
	locals: &Locals, 
	instructions: &[Instruction], 
	result_value: Value, 
	local_data: &mut [i64],
	resources: &Resources
) -> i64 {
	let mut instr_pointer = 0;
	assert_eq!(local_data.len(), locals.locals.len());
	
	while instr_pointer < instructions.len() {
		let instruction = &instructions[instr_pointer];
		instr_pointer += 1;

		match *instruction {
			Instruction::Temporary => panic!("Cannot run temporary instruction"),
			Instruction::PrimitiveBinaryOperator(operator, primitive, result, a, b) => {
				let a = get_value(local_data, a);
				let b = get_value(local_data, b);

				use Operator::*;
				use PrimitiveKind::*;
				match (operator, primitive) {
					(Equ, U64) => set_value(local_data, result, if a == b { 1 } else { 0 }),
					(NEqu, U64) => set_value(local_data, result, if a != b { 1 } else { 0 }),
					(LessEqu, U64) => set_value(local_data, result, if a <= b { 1 } else { 0 }),
					(GreaterEqu, U64) => set_value(local_data, result, if a >= b { 1 } else { 0 }),
					(Less, U64) => set_value(local_data, result, if a < b { 1 } else { 0 }),
					(Greater, U64) => set_value(local_data, result, if a > b { 1 } else { 0 }),
					(Not, U64) => set_value(local_data, result, if a < b { 1 } else { 0 }),
					(And, U64) => set_value(local_data, result, 
						if a != 0 && b != 0 { 1 } else { 0 }),
					(Or, U64) => set_value(local_data, result,
						if a != 0 || b != 0 { 1 } else { 0 }),
					(Xor, U64) => set_value(local_data, result,
						if (a != 0) ^ (b != 0) { 1 } else { 0 }),
					(BitwiseOrOrLambda, U64) => set_value(local_data, result, a | b),
					(Add, U64) => set_value(local_data, result, a + b),
					(Sub, U64) => set_value(local_data, result, a - b),
					(MulOrDeref, U64) => set_value(local_data, result, a * b),
					(Div, U64) => set_value(local_data, result, a / b),
					(Mod, U64) => set_value(local_data, result, a % b),
					(_, _) => panic!("Unhandled combination {:?} {:?}", operator, primitive),
				}
			}
			Instruction::MoveU64(into, from) => {
				let from = get_value(local_data, from);
				set_value(local_data, into, from);
			}
			Instruction::JumpRel(a) => {
				instr_pointer = (instr_pointer as i64 + a) as usize;
			}
			Instruction::JumpRelIfZero(value, a) => {
				let value = get_value(local_data, value);
				if value == 0 {
					instr_pointer = (instr_pointer as i64 + a) as usize;
				}
			}
			Instruction::Call { calling, returns, ref args } => {
				// TODO: Get rid of recursion(by introducing call stack), 
				// and don't crash if the function is not defined yet, just pause the execution
				// and continue when it is ready.
				use crate::id::Id;
				let resource = resources.resource(ResourceId::create(get_value(local_data, calling) as u32));

				match resource.kind {
					ResourceKind::Function { 
						instructions: Some((ref sub_locals, ref instructions, return_value)), 
						..
					} => {
						let mut sub_local_data = vec![0; sub_locals.locals.len()];
						for (i, arg) in args.iter().enumerate() {
							sub_local_data[i] = get_value(local_data, *arg);
						}

						let return_value = run_instructions_with_locals(
							sub_locals,
							instructions,
							return_value,
							&mut sub_local_data,
							resources,
						);

						local_data[returns.into_index()] = return_value;
					}
					ResourceKind::ExternalFunction { ref func, .. } => {
						let args = args.iter().map(|v| get_value(local_data, *v)).collect::<Vec<_>>();
						local_data[returns.into_index()] = func(resources, &args);
					}
					_ => {
						unreachable!(
							"Resource is not function! This should have been caught in type checking"
						);
					}
				}
			}
		}
	}

	get_value(&local_data, result_value)
}
