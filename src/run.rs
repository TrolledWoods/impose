use crate::resource::{ ResourceKind, ResourceId, Resources };
use crate::code_gen::Instruction;
use crate::stack_frame::{StackFrameInstance, Value};

// TODO: Optimize the way we return data.
pub fn run_instructions(
	instructions: &[Instruction], 
	result_value: Option<&Value>, 
	stack_frame_instance: &mut StackFrameInstance,
	resources: &Resources
) -> crate::stack_frame::ConstBuffer {
	let mut instr_pointer = 0;
	
	while instr_pointer < instructions.len() {
		let instruction = &instructions[instr_pointer];
		instr_pointer += 1;

		match *instruction {
			Instruction::Temporary => panic!("Cannot run temporary instruction"),
			Instruction::Move(into, ref from) => {
				stack_frame_instance.insert_value_into_local(into, from);
			}
			Instruction::JumpRel(a) => {
				instr_pointer = (instr_pointer as i64 + a) as usize;
			}
			Instruction::JumpRelIfZero(ref value, a) => {
				let value = stack_frame_instance.get_u64(value);
				if value == 0 {
					instr_pointer = (instr_pointer as i64 + a) as usize;
				}
			}
			Instruction::WrappingAdd(result, ref a, ref b) => {
				match result.size {
					4 => {
						let a = stack_frame_instance.get_u32(a);
						let b = stack_frame_instance.get_u32(b);

						stack_frame_instance.insert_into_local(result, &(a.wrapping_add(b)).to_le_bytes());
					}
					8 => {
						let a = stack_frame_instance.get_u64(a);
						let b = stack_frame_instance.get_u64(b);

						stack_frame_instance.insert_into_local(result, &(a.wrapping_add(b)).to_le_bytes());
					}
					_ => panic!("Unknown thing"),
				}
			}
			Instruction::WrappingSub(result, ref a, ref b) => {
				match result.size {
					4 => {
						let a = stack_frame_instance.get_u32(a);
						let b = stack_frame_instance.get_u32(b);

						stack_frame_instance.insert_into_local(result, &(a.wrapping_sub(b)).to_le_bytes());
					}
					8 => {
						let a = stack_frame_instance.get_u64(a);
						let b = stack_frame_instance.get_u64(b);

						stack_frame_instance.insert_into_local(result, &(a.wrapping_sub(b)).to_le_bytes());
					}
					_ => panic!("Unknown thing"),
				}
			}
			Instruction::WrappingMul(result, ref a, ref b) => {
				match result.size {
					4 => {
						let a = stack_frame_instance.get_u32(a);
						let b = stack_frame_instance.get_u32(b);

						stack_frame_instance.insert_into_local(result, &(a.wrapping_mul(b)).to_le_bytes());
					}
					8 => {
						let a = stack_frame_instance.get_u64(a);
						let b = stack_frame_instance.get_u64(b);

						stack_frame_instance.insert_into_local(result, &(a.wrapping_mul(b)).to_le_bytes());
					}
					_ => panic!("Unknown thing"),
				}
			}
			Instruction::WrappingDiv(result, ref a, ref b) => {
				match result.size {
					4 => {
						let a = stack_frame_instance.get_u32(a);
						let b = stack_frame_instance.get_u32(b);

						stack_frame_instance.insert_into_local(result, &(a.wrapping_div(b)).to_le_bytes());
					}
					8 => {
						let a = stack_frame_instance.get_u64(a);
						let b = stack_frame_instance.get_u64(b);

						stack_frame_instance.insert_into_local(result, &(a.wrapping_div(b)).to_le_bytes());
					}
					_ => panic!("Unknown thing"),
				}
			}
			Instruction::Call { ref calling, returns, ref args } => {
				// TODO: Get rid of recursion(by introducing call stack), 
				// and don't crash if the function is not defined yet, just pause the execution
				// and continue when it is ready.
				use crate::id::Id;
				let resource = resources.resource(
					ResourceId::create(stack_frame_instance.get_u64(calling) as u32)
				);

				match resource.kind {
					ResourceKind::Function { 
						instructions: Some((ref sub_scope, ref instructions, ref return_value)), 
						..
					} => {
						let mut sub_stack_frame_instance = 
							sub_scope.create_instance_with_func_args(
								args.iter().map(|(index, value)| (
									*index,
									stack_frame_instance.get_value(value),
								))
							);

						let return_value = run_instructions(
							instructions,
							return_value.as_ref(),
							&mut sub_stack_frame_instance,
							resources,
						);

						stack_frame_instance.insert_into_local(returns, &return_value);
					}
					ResourceKind::ExternalFunction { ref func, n_arg_bytes, n_return_bytes } => {
						let mut arg_buffer = vec![0; n_arg_bytes];
						let mut return_buffer = vec![0; n_return_bytes]; 

						for (index, value) in args {
							let value_buffer = stack_frame_instance.get_value(value);

							arg_buffer[*index..*index + value_buffer.len()].copy_from_slice(value_buffer);
						}

						func(resources, &arg_buffer, &mut return_buffer);
						stack_frame_instance.insert_into_local(returns, &return_buffer);
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

	result_value.map(|val| stack_frame_instance.clone_value(val)).unwrap_or_default() }
