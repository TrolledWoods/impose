use std::fmt;

use crate::intrinsic::*;
use crate::parser::*;
use crate::types::*;
use crate::scopes::*;
use crate::resource::*;
use crate::stack_frame::*;
use crate::operator::*;
use crate::code_loc::*;

macro_rules! push_instr {
	($instrs:expr, $instr:expr) => {{
		// println!("{} {}", line!(), column!());
		$instrs.push($instr);
	}}
}

pub enum Instruction {
	/// Temporary instruction. Cannot be run, because it's supposed to be overwritten later.
	Temporary,

	IntrinsicTwoArgs(IntrinsicKindTwo, LocalHandle, Value, Value),

	SetAddressOf(LocalHandle, LocalHandle),
	GetAddressOfResource(LocalHandle, ResourceId),

	IndirectMove(IndirectLocalHandle, Value),
	Move(LocalHandle, Value),

	JumpRel(i64),
	JumpRelIfZero(Value, i64),
	Call {
		calling: Value, 
		returns: LocalHandle, 
		args: Vec<(usize, Value, usize)>,
	},
}

impl fmt::Debug for Instruction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Instruction::Temporary => write!(f, "temp"),
			Instruction::IntrinsicTwoArgs(intrinsic, result, a, b)
				=> write!(f, "{:?} = {:?} {:?}, {:?}", result, intrinsic, a, b),
			Instruction::GetAddressOfResource(to, id) =>
				write!(f, "{:?} = resource({:?})", to, id),
			Instruction::SetAddressOf(to, from) =>
				write!(f, "{:?} = &{:?}", to, from),
			Instruction::IndirectMove(into, from) => write!(f, "mov {:?} = {:?}", into, from),
			Instruction::Move(a, b) => write!(f, "mov {:?} = {:?}", a, b),
			Instruction::JumpRel(a) => write!(f, "jump {:?}", a),
			Instruction::JumpRelIfZero(value, a) => write!(f, "jump {:?} if {:?} == 0", a, value),
			Instruction::Call { calling, returns, ref args } => {
				write!(f, "call {:?} with ", calling)?;
				for arg in args.iter() {
					write!(f, ", {:?}", arg.1)?;
				}
				write!(f, ", return into ({:?})", returns)?;

				Ok(())
			}
		}
	}
}

// TODO: Add a struct with data about compiling an expression, so that we can keep going
// at the same point that we stopped if there is an undefined dependency.
pub fn compile_expression(
	ast: &Ast, 
	scopes: &mut Scopes,
	resources: &Resources,
	types: &Types,
) -> Result<(StackFrameLayout, Vec<Instruction>, Option<Value>), Dependency> {
	let mut locals = Locals::new();

	let mut node_values: Vec<Value> = Vec::new();
	let mut marker_locs = Vec::new();
	let mut temporary_labels: Vec<(_, _, Option<LocalHandle>)> = Vec::new();

	let mut instructions = Vec::new();

	for node in ast.nodes.iter() {
		if node.is_meta_data { 
			continue; 
		}

		let evaluation_value = match node.kind {
			NodeKind::BitCast { into_type: _, value: _ } => {
				node_values.pop().unwrap()
			}
			NodeKind::Identifier { source: member_id, const_members: ref sub_members, is_type } => {
				assert!(!is_type, "Identifier that is type should be meta");

				assert_eq!(sub_members.len(), 0, "Const member access should be resolved in type checking!");

				match scopes.member(member_id).kind {
					ScopeMemberKind::UndefinedDependency(_) => panic!("Cannot run code_gen on undefined dependencies(they have to have been caught in the typer)"),
					ScopeMemberKind::Indirect(_) => unreachable!("the member function on Scopes should handle indirects and shouldn't return one of them"),
					ScopeMemberKind::LocalVariable => {
						let member = match scopes.member(member_id).storage_loc {
							Some(value) => value,
							None => panic!("Invalid thing, \nScopes: {:?}, \nInstructions: {:?}", scopes, instructions),
						};
						
						Value::Local(member)
					}
					ScopeMemberKind::Constant(id) => {
						let (_, value) = get_resource_constant(types, &mut instructions, &mut locals, &node.loc, resources, id)?;
						value
					}
					ScopeMemberKind::Label => panic!("Cannot do labels"),
				}
			}
			NodeKind::Assign => {
				let right = node_values.pop().unwrap();
				let left = node_values.pop().unwrap();

				let new_value = locals.allocate(types.handle(node.type_.unwrap()));
				match left {
					Value::Local(handle) => {
						push_instr!(instructions, Instruction::Move(handle, right.clone()));
					},
					Value::Pointer(handle) => {
						push_instr!(instructions, Instruction::IndirectMove(handle, right.clone()));
					},
					Value::Constant(_) => {
						panic!("Cannot assign to a constant");
					}
				};

				push_instr!(instructions, Instruction::Move(new_value, right));
				Value::Local(new_value)
			}
			NodeKind::IntrinsicTwo(kind) => {
				let right = node_values.pop().unwrap();
				let left  = node_values.pop().unwrap();

				let result = locals.allocate(types.handle(node.type_.unwrap()));
				push_instr!(instructions, Instruction::IntrinsicTwoArgs(kind, result, left, right));
				Value::Local(result)
			},
			NodeKind::DeclareFunctionArgument { variable_name, .. } => {
				let scope_member = scopes.member_mut(variable_name);

				let location = locals.allocate(types.handle(scope_member.type_.unwrap()));
				scope_member.storage_loc = Some(location);

				continue;
			}
			NodeKind::Declaration { variable_name, value } => {
				let location = locals.allocate(
					types.handle(ast.nodes[value as usize].type_.unwrap())
				);
				scopes.member_mut(variable_name).storage_loc = Some(location);
				
				let input = node_values.pop().unwrap();
				push_instr!(instructions, Instruction::Move(location, input));

				Value::Local(EMPTY_LOCAL)
			}
			NodeKind::Marker(MarkerKind::LoopHead) => {
				marker_locs.push(instructions.len());
				Value::Local(EMPTY_LOCAL)
			}
			NodeKind::Marker(MarkerKind::IfCondition(_)) => {
				marker_locs.push(instructions.len());
				// Will be a jump instruction over the body
				push_instr!(instructions, Instruction::Temporary);
				let value = node_values.pop().unwrap();
				value
			}
			NodeKind::Marker(MarkerKind::IfElseTrueBody(contains)) => {
				// Instruction to move the value into a new local, so that the else can
				// also use that same local
				let local = locals.allocate(
					types.handle(ast.nodes[contains as usize].type_.unwrap())
				);
				push_instr!(
					instructions, 
					Instruction::Move(local, node_values.pop().unwrap())
				);

				// Instruction to jump to to skip the if body
				marker_locs.push(instructions.len());

				// Jump instruction to skip else
				push_instr!(instructions, Instruction::Temporary);

				Value::Local(local)
			}
			NodeKind::Loop(_) => {
				node_values.pop().unwrap(); // Loop body
				node_values.pop().unwrap(); // Loop head marker

				let jump_to_instr_loc = marker_locs.pop().unwrap();
				let current_instr_loc = instructions.len();
				push_instr!(instructions, Instruction::JumpRel(
					jump_to_instr_loc as i64 - current_instr_loc as i64 - 1
				));
				Value::Local(EMPTY_LOCAL)
			}
			NodeKind::If { .. } => {
				let condition_instr_loc = marker_locs.pop().unwrap();
				let current_instr_loc   = instructions.len();

				let _true_body = node_values.pop().unwrap();
				let condition = node_values.pop().unwrap();
				instructions[condition_instr_loc] = Instruction::JumpRelIfZero(
					condition,
					current_instr_loc as i64 - condition_instr_loc as i64 - 1
				);
				Value::Local(EMPTY_LOCAL)
			}
			NodeKind::IfWithElse { .. } => {
				let true_body_instr_loc = marker_locs.pop().unwrap();
				let condition_instr_loc = marker_locs.pop().unwrap();
				let current_instr_loc   = instructions.len();

				let false_body = node_values.pop().unwrap();
				let true_body = node_values.pop().unwrap();
				let condition = node_values.pop().unwrap();

				instructions[condition_instr_loc] = Instruction::JumpRelIfZero(
					condition,
					// We don't subtract one here, because we wanna move past the Jump that skips
					// over the else block at true_body_instr_loc
					true_body_instr_loc as i64 - condition_instr_loc as i64
				);

				instructions[true_body_instr_loc] = Instruction::JumpRel(
					// Move past the MoveU64 that moves the false body return value into the
					// true body return value
					current_instr_loc as i64 - true_body_instr_loc as i64
				);

				if let Value::Local(local) = true_body {
					push_instr!(instructions, Instruction::Move(
						local, 
						false_body,
					));
				} else {
					panic!("This can't be a constant bruh");
				}

				true_body
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
							break;
						}
					}

					if return_value_local.is_none() {
						return_value_local = Some(locals.allocate(
							types.handle(ast.nodes[value as usize].type_.unwrap())
						));
					}

					let input = node_values.pop().unwrap();

					instruction_loc += 1;
					push_instr!(instructions, Instruction::Move(return_value_local.unwrap(), input));
				}

				push_instr!(instructions, Instruction::JumpRel(-42069));

				temporary_labels.push((label, instruction_loc, return_value_local));

				Value::Local(EMPTY_LOCAL)
			}
			NodeKind::Block { ref contents, label } => {
				let mut return_value_loc = None;
				let result = node_values.pop().unwrap();

				node_values.truncate(node_values.len() + 1 - contents.len());

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

				match return_value_loc {
					Some(location) => {
						push_instr!(instructions, Instruction::Move(location, result));
						Value::Local(location)
					}
					None => {
						result
					}
				}
			}
			NodeKind::Struct { .. } => {
				let id = node.type_.unwrap();
				let handle = types.handle(id);
				let type_kind = &types.get(id).kind;

				let local = locals.allocate(handle);
				match type_kind {
					TypeKind::Struct { members: ref type_members } => {
						for (_, offset, type_handle) in type_members.iter().rev() {
							let sub_local = 
								local.sub_local(*offset, type_handle.size, type_handle.align);
							push_instr!(instructions, Instruction::Move(sub_local, node_values.pop().unwrap()));
						}
					}
					_ => unreachable!(),
				}

				Value::Local(local)
			}
			NodeKind::MemberAccess(member, sub_name) => {
				let id = ast.nodes[member as usize].type_.unwrap();
				let type_kind = &types.get(id).kind;

				let value = node_values.pop().unwrap();

				// TODO: We don't wanna recheck the name twice, 
				match type_kind {
					TypeKind::U64 => {
						if sub_name == "low" {
							value.get_sub_value(0, 4, 4)
						} else if sub_name == "high" {
							value.get_sub_value(4, 4, 4)
						} else {
							panic!("bleh");
						}
					}
					TypeKind::BufferPointer(_) => {
						if sub_name == "pointer" {
							value.get_sub_value(0, 8, 8)
						} else if sub_name == "length" {
							value.get_sub_value(8, 8, 8)
						} else {
							panic!("bleh");
						}
					}
					TypeKind::Struct { ref members } => {
						members.iter().find_map(|(name, offset, handle)| {
							if *name == sub_name {
								Some(value.get_sub_value(*offset, handle.size, handle.align))
							} else {
								None
							}
						}).expect("Struct does not contain member, should be caught in type check")
					}
					_ => panic!("bleh"),
				}
			}
			NodeKind::Number(num) => {
				// TODO: Check that the number fits, although I guess this should
				// be down further up in the pipeline
				(num as u64).into()
			}
			NodeKind::Float(num) => {
				num.to_bits().into()
			}
			NodeKind::EmptyLiteral => {
				Value::Local(EMPTY_LOCAL)
			}
			NodeKind::FunctionCall { function_pointer, ref arg_list } => {
				// Get the type of the function
				let (arg_types, return_type) = match types.get(
					ast.nodes[function_pointer as usize].type_.unwrap()
				).kind {
					TypeKind::FunctionPointer { ref args, returns } => (args, returns),
					_ => unreachable!("´The function pointer wasn't of type function pointer!?"),
				};

				// TODO: Use the argument types?

				let returns = locals.allocate(types.handle(return_type));

				let arg_list = &node_values[node_values.len() - arg_list.len() ..];

				// TODO: If I have zst:s, this won't handle them properly.
				let mut offset_ctr = 0;
				let args = arg_list.iter().zip(arg_types)
					.map(|(arg, type_)| {
						let type_handle = types.handle(*type_);
						let offset = crate::align::to_aligned(type_handle.align, offset_ctr);
						offset_ctr = offset + type_handle.size;
						(offset, arg.clone(), type_handle.size)
					})
					.collect();

				let len = node_values.len() - arg_list.len();
				node_values.truncate(len);

				let calling = node_values.pop().unwrap();

				push_instr!(instructions, Instruction::Call { calling, returns, args });

				Value::Local(returns)
			}
			NodeKind::Resource(id) => {
				let (_, value) = get_resource_constant(types, &mut instructions, &mut locals, &node.loc, resources, id)?;
				value
			}

			NodeKind::UnaryOperator { operator: Operator::BitAndOrPointer, operand } => {
				let to = locals.allocate(types.handle(node.type_.unwrap()));
				let from = match node_values.pop().unwrap() {
					Value::Local(handle) => handle,
					value => {
						let local = locals.allocate(types.handle(
								ast.nodes[operand as usize].type_.unwrap()
						));
						push_instr!(instructions, Instruction::Move(local, value));
						local
					}
				};

				push_instr!(instructions, Instruction::SetAddressOf(to, from));
				Value::Local(to)
			}
			NodeKind::UnaryOperator { operator: Operator::MulOrDeref, operand } => {
				// Get a local, no matter what!
				// (only 1 level indirect access, so you cannot indirectly access an indirect
				// so to speak)
				let from = match node_values.pop().unwrap() {
					Value::Local(handle) => handle,
					Value::Constant(_) => panic!("Cannot dereference constants"),
					Value::Pointer(handle) => {
						let local = locals.allocate(types.handle(
							ast.nodes[operand as usize].type_.unwrap()
						));
						push_instr!(instructions, Instruction::Move(local, Value::Pointer(handle)));
						local
					}
				};

				let size = types.handle(node.type_.unwrap()).size;

				// Make a pointer value.
				Value::Pointer(from.indirect_local_handle_to_self(size))
			}

			// Get the type of some value as a constant.
			NodeKind::GetType(node) => {
				let type_ = ast.nodes[node as usize].type_.unwrap().into_index() as u64;
				Value::Constant(type_.to_le_bytes().into())
			}

			// Type expressions evaluate types with the typing system at typing type, we do not
			// need to generate any instructions for them.
			NodeKind::TypeStruct { .. } |
			NodeKind::TypeFunctionPointer { .. } |
			NodeKind::TypeBufferPointer(_) |
			NodeKind::TypePointer(_) => {
				continue;
			},

			_ => todo!()
		};

		node_values.push(evaluation_value);
		// println!("{:?}", node.kind);
		// for instruction in &instructions[instr_index ..] {
		// 	println!(" + {:?}", instruction);
		// }
		// println!("{:?}", node_values);
	}

	Ok((locals.layout(), instructions, node_values.pop()))
}

/// Returns a pointer to a resource, either by copying the resource onto the stack and taking a
/// pointer to that, or by taking a pointer to the resource itself. The pointer is always
/// in a local, because it cannot possibly be a constant(because pointers to resources change
/// when compiling etc).
fn get_resource_pointer(
	types: &Types,
	instructions: &mut Vec<Instruction>,
	locals: &mut Locals,
	loc: &CodeLoc,
	resources: &Resources,
	id: ResourceId,
	local: LocalHandle,
	sub_type_handle: TypeHandle,
) -> Result<(), Dependency> {
	// TODO: Also optimize direct pointers to constants.
	let resource = resources.resource(id);
	match resource.kind {
		ResourceKind::Value(ResourceValue::Value(_, _, _, ref pointer_members)) 
			if pointer_members.len() == 0 => 
		{
			// There is an instruction for this!
			push_instr!(instructions, Instruction::GetAddressOfResource(local, id));
			Ok(())
		}
		_ => {
			// This is just a random pointer
			let (n_values, value) =
				get_resource_constant(types, instructions, locals, loc, resources, id)?;

			let value_local = match value {
				Value::Local(local) => local,
				_ => {
					let value_local = locals.allocate_several(sub_type_handle, n_values);
					push_instr!(instructions, Instruction::Move(value_local, value));
					value_local
				}
			};

			push_instr!(instructions, Instruction::SetAddressOf(local, value_local));
			Ok(())
		}
	}
}

fn get_resource_constant(
	types: &Types,
	instructions: &mut Vec<Instruction>,
	locals: &mut Locals,
	loc: &CodeLoc,
	resources: &Resources,
	id: ResourceId,
) -> Result<(usize, Value), Dependency> {
	let resource = resources.resource(id);
	match resource.kind {
		ResourceKind::Poison => panic!("Used poison. TODO: Return"),
		ResourceKind::ExternalFunction { .. } |
		ResourceKind::Function { .. } =>
			Ok((1, id.into_index().into())),
		ResourceKind::Value(ResourceValue::Value(type_handle, n_values, ref value, ref pointer_members)) => {
			if pointer_members.len() > 0 {
				// TODO: Deal with pointers in pointer buffers.

				let local = locals.allocate(type_handle);

				push_instr!(instructions, Instruction::Move(local, Value::Constant(value.clone())));

				for &(offset, sub_resource_id, sub_type_handle) in pointer_members {
					// Put the resource pointer into the right local.
					get_resource_pointer(types, instructions, locals, loc, resources, sub_resource_id, local.sub_local(offset, 8, 8), sub_type_handle)?;
				}

				Ok((n_values, Value::Local(local)))
			} else {
				Ok((n_values, Value::Constant(value.clone())))
			}
		}
		ResourceKind::Value(_) =>
			Err(Dependency::Value(*loc, id)),
	}
}
