use crate::code_gen::{Instruction, Locals, Value};

fn set_value(locals: &mut [i64], value: Value, num: i64) {
	match value {
		Value::Local(local) => locals[local] = num,
		Value::Constant(_) => panic!("Cannot set constant"),
		Value::Poison => panic!("Cannot set poison"),
	}
}

fn get_value(locals: &[i64], value: Value) -> i64 {
	match value {
		Value::Local(local) => locals[local],
		Value::Constant(i) => i,
		Value::Poison => panic!("Cannot get poison"),
	}
}

pub fn run_instructions(locals: &Locals, instructions: &[Instruction], result_value: Value) -> i64 {
	let mut instr_pointer = 0;
	let mut local_data = vec![0; locals.locals.len()];
	
	while instr_pointer < instructions.len() {
		let instruction = &instructions[instr_pointer];
		instr_pointer += 1;

		match *instruction {
			Instruction::AddU64(result, a, b) => {
				let a = get_value(&local_data, a);
				let b = get_value(&local_data, b);
				set_value(&mut local_data, result, a + b);
			}
			Instruction::SubU64(result, a, b) => {
				let a = get_value(&local_data, a);
				let b = get_value(&local_data, b);
				set_value(&mut local_data, result, a - b);
			}
			Instruction::MoveU64(into, from) => {
				let from = get_value(&local_data, from);
				set_value(&mut local_data, into, from);
			}
			Instruction::JumpRel(a) => {
				instr_pointer = (instr_pointer as i64 + a) as usize;
			}
		}
	}

	get_value(&local_data, result_value)
}
