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
			Instruction::AddU64(result, a, b) => {
				let a = get_value(local_data, a);
				let b = get_value(local_data, b);
				set_value(local_data, result, a + b);
			}
			Instruction::SubU64(result, a, b) => {
				let a = get_value(local_data, a);
				let b = get_value(local_data, b);
				set_value(local_data, result, a - b);
			}
			Instruction::MoveU64(into, from) => {
				let from = get_value(local_data, from);
				set_value(local_data, into, from);
			}
			Instruction::JumpRel(a) => {
				instr_pointer = (instr_pointer as i64 + a) as usize;
			}
			Instruction::Call { calling, returns, ref args } => {
				// TODO: Get rid of recursion(by introducing call stack), 
				// and don't crash if the function is not defined yet, just pause the execution
				// and continue when it is ready.
				let resource = resources.resource(get_value(local_data, calling) as ResourceId);

				if let ResourceKind::Function { 
					instructions: Some((ref sub_locals, ref instructions, return_value)), 
					..
				} = resource.kind {
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
				} else {
					unreachable!(
						"Resource is not function! This should have been caught in type checking"
					);
				}
			}
		}
	}

	get_value(&local_data, result_value)
}
