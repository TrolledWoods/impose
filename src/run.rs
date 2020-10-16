use crate::code_gen::*;
use crate::intrinsic::*;
use crate::resource::*;
use crate::stack_frame::*;

// TODO: Optimize the way we return data.
pub fn run_instructions(
    resources: &Resources,
    stack_frame_instance: &mut StackFrameInstance,
    program: &Program,
) -> ConstBuffer {
    let mut instr_pointer = 0;

    while instr_pointer < program.instructions.len() {
        let instruction = &program.instructions[instr_pointer];
        instr_pointer += 1;

        match *instruction {
            Instruction::DebugLocation(_) => (),
            Instruction::IndirectMove(into, ref from) => {
                stack_frame_instance.insert_value_into_indirect_local(into, from);
            }
            Instruction::Move(into, ref from) => {
                stack_frame_instance.insert_value_into_local(into, from);
            }
            Instruction::JumpRel(a) => {
                instr_pointer = program.labels[a.into_index()];
            }
            Instruction::JumpRelIfZero(ref value, a) => {
                let value = stack_frame_instance.get_value(value)[0];
                if value == 0 {
                    instr_pointer = program.labels[a.into_index()];
                }
            }
            Instruction::Dereference(to, ref from) => {
                let u8_pointer = (stack_frame_instance.get_u64(from) as usize) as *const u8;

                let slice = unsafe { std::slice::from_raw_parts(u8_pointer, to.size) };
                stack_frame_instance.insert_into_local(to, slice);
            }
            Instruction::IntrinsicTwoArgs(intrinsic, result, ref a, ref b) => {
                let a = stack_frame_instance.get_value(a);
                let b = stack_frame_instance.get_value(b);

                // This is to make sure the alignment is good
                let mut buffer_u64: u64 = 0;
                run_intrinsic_two(intrinsic, &mut buffer_u64, a, b);

                let result_size = result.size;
                stack_frame_instance
                    .insert_into_local(result, &buffer_u64.to_le_bytes()[..result_size]);
            }
            Instruction::GetAddressOfResource(to, resource_id) => {
                if let ResourceKind::Done(ref val, _) = resources.resource(resource_id).kind {
                    let bytes = (val.as_ptr() as u64).to_le_bytes();
                    stack_frame_instance.insert_into_local(to, &bytes);
                } else {
                    panic!();
                }
            }
            Instruction::SetAddressOf(to, from) => {
                let bytes = (stack_frame_instance.address_of_local(from) as u64).to_le_bytes();
                stack_frame_instance.insert_into_local(to, &bytes);
            }
            Instruction::Call {
                ref calling,
                returns,
                ref args,
            } => {
                // TODO: Get rid of recursion(by introducing call stack),
                // and don't crash if the function is not defined yet, just pause the execution
                // and continue when it is ready.

                let id = stack_frame_instance.get_u64(calling) as usize;

                match resources.functions[id] {
                    FunctionKind::Function(ref program) => {
                        let mut sub_stack_frame_instance = program
                            .layout
                            .create_instance_with_func_args(args.iter().map(
                                |(index, value, _)| (*index, stack_frame_instance.get_value(value)),
                            ));

                        let return_value =
                            run_instructions(resources, &mut sub_stack_frame_instance, program);

                        stack_frame_instance.insert_into_local(returns, &return_value);
                    }
                    FunctionKind::ExternalFunction {
                        ref func,
                        n_arg_bytes,
                        n_return_bytes,
                    } => {
                        let mut arg_buffer = vec![0; n_arg_bytes];
                        let mut return_buffer = vec![0; n_return_bytes];

                        for (index, value, size) in args {
                            let value_buffer = &stack_frame_instance.get_value(value)[0..*size];

                            arg_buffer[*index..*index + value_buffer.len()]
                                .copy_from_slice(value_buffer);
                        }

                        func(resources, &arg_buffer, &mut return_buffer);
                        stack_frame_instance.insert_into_local(returns, &return_buffer);
                    }
                }
            }
        }
    }

    stack_frame_instance.clone_value(&program.value)
}
