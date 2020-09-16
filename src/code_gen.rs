use std::collections::HashMap;
use std::fmt;

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

	/// Wrapping addition. The LocalHandle, Value and Value have to have the same size.
	// TODO: We can make this take up less space by having the same size 
	// for everything, potentially?
	WrappingAdd(LocalHandle, Value, Value),
	WrappingSub(LocalHandle, Value, Value),
	WrappingMul(LocalHandle, Value, Value),
	WrappingDiv(LocalHandle, Value, Value),

	LessThan(LocalHandle, Value, Value),

	SetAddressOf(LocalHandle, LocalHandle),

	IndirectMove(IndirectLocalHandle, Value),
	Move(LocalHandle, Value),

	JumpRel(i64),
	JumpRelIfZero(Value, i64),
	Call {
		calling: Value, 
		returns: LocalHandle, 
		args: Vec<(usize, Value)>,
	},
}

impl fmt::Debug for Instruction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Instruction::Temporary => write!(f, "temp"),
			Instruction::WrappingAdd(result, a, b) => 
				write!(f, "{:?} = {:?} + {:?}", result, a, b),
			Instruction::WrappingSub(result, a, b) => 
				write!(f, "{:?} = {:?} - {:?}", result, a, b),
			Instruction::WrappingMul(result, a, b) => 
				write!(f, "{:?} = {:?} * {:?}", result, a, b),
			Instruction::WrappingDiv(result, a, b) => 
				write!(f, "{:?} = {:?} / {:?}", result, a, b),
			Instruction::SetAddressOf(to, from) =>
				write!(f, "({:?}) = &({:?})", to, from),
			Instruction::LessThan(result, a, b) =>
				write!(f, "{:?} = {:?} < {:?}", result, a, b),
			Instruction::IndirectMove(into, from) => write!(f, "mov *({:?}) = {:?}", into, from),
			Instruction::Move(a, b) => write!(f, "mov ({:?}) = {:?}", a, b),
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

// TODO: Add a struct with data about compiling an expression, so that we can keep going
// at the same point that we stopped if there is an undefined dependency.
pub fn compile_expression(
	ast: &Ast, 
	scopes: &mut Scopes,
	resources: &Resources,
	types: &Types,
) -> Result<(StackFrameLayout, Vec<Instruction>, Option<Value>), Dependency> {
	let mut locals = Locals::new();
	let mut node_values: Vec<Option<Value>> = Vec::with_capacity(ast.nodes.len());
	let mut instructions = Vec::new();

	let mut temporary_labels: Vec<(_, _, Option<LocalHandle>)> = Vec::new();
	let mut instruction_locations: HashMap<AstNodeId, usize> = HashMap::new();
	
	let mut function_arg_locations = Vec::new();

	for (node_id, node) in ast.nodes.iter().enumerate().map(|(a, b)| (a as u32, b)) {
		if node.is_meta_data { 
			node_values.push(None);
			continue; 
		}

		match node.kind {
			NodeKind::BitCast { into_type: _, value } => {
				// Bit casting just reinterprets the type, we don't actually do anything :D
				node_values.push(node_values[value as usize].clone());
			}
			NodeKind::Identifier { source: member_id, const_members: ref sub_members, is_type } => {
				assert!(!is_type, "Identifier that is type should be meta");

				assert_eq!(sub_members.len(), 0, "Const member access should be resolved in type checking!");

				match scopes.member(member_id).kind {
					ScopeMemberKind::UndefinedDependency(_) => panic!("Cannot run code_gen on undefined dependencies(they have to have been caught in the typer)"),
					ScopeMemberKind::Indirect(_) => unreachable!("the member function on Scopes should handle indirects and shouldn't return one of them"),
					ScopeMemberKind::LocalVariable | ScopeMemberKind::FunctionArgument => {
						let member = match scopes.member(member_id).storage_loc {
							Some(value) => value,
							None => panic!("Invalid thing, \nScopes: {:?}, \nInstructions: {:?}", scopes, instructions),
						};
						
						node_values.push(Some(Value::Local(member)));
					}
					ScopeMemberKind::Constant(id) => {
						node_values.push(Some(get_resource_constant(types, &mut instructions, &mut locals, &node.loc, resources, id)?))
					}
					ScopeMemberKind::Label => panic!("Cannot do labels"),
				}
			}
			NodeKind::DeclareFunctionArgument { variable_name, .. } => {
				let scope_member = scopes.member_mut(variable_name);

				// Declaring a function argument is like moving the responsibility of setting
				// the locals to the caller. This should be done by the 'call' instruction,
				// which will set all the affected locals to the appropriate values.
				let location = locals.allocate(types.handle(scope_member.type_.unwrap()));

				scope_member.storage_loc = Some(location);

				function_arg_locations.push(location);
				node_values.push(None);
			}
			NodeKind::Declaration { variable_name, value } => {
				let location = locals.allocate(
					types.handle(ast.nodes[value as usize].type_.unwrap())
				);
				scopes.member_mut(variable_name).storage_loc = Some(location);
				
				let input = node_values[value as usize].clone().unwrap();
				push_instr!(instructions, Instruction::Move(location, input));
				node_values.push(None);
			}
			NodeKind::LocationMarker => {
				instruction_locations.insert(node_id, instructions.len());
				node_values.push(None);
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
						let local = locals.allocate(
							types.handle(ast.nodes[contains as usize].type_.unwrap())
						);
						push_instr!(
							instructions, 
							Instruction::Move(local, node_values[contains as usize].clone().unwrap())
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

				match node_value {
					Some(node_value) => node_values.push(Some(node_value)),
					None => node_values.push(node_values[contains as usize].clone()),
				}
			}
			NodeKind::Loop { start_location, .. } => {
				let jump_to_instr_loc = *instruction_locations.get(&start_location).unwrap();
				let current_instr_loc = instructions.len();
				push_instr!(instructions, Instruction::JumpRel(
					jump_to_instr_loc as i64 - current_instr_loc as i64 - 1
				));

				node_values.push(None);
			}
			NodeKind::If { condition, .. } => {
				let condition_instr_loc = *instruction_locations.get(&condition).unwrap();
				let current_instr_loc   = instructions.len();
				instructions[condition_instr_loc] = Instruction::JumpRelIfZero(
					node_values[condition as usize].clone().unwrap(),
					current_instr_loc as i64 - condition_instr_loc as i64 - 1
				);

				node_values.push(None);
			}
			NodeKind::IfWithElse { condition, true_body, false_body } => {
				let condition_instr_loc = *instruction_locations.get(&condition).unwrap();
				let true_body_instr_loc = *instruction_locations.get(&true_body).unwrap();
				let current_instr_loc   = instructions.len();

				instructions[condition_instr_loc] = Instruction::JumpRelIfZero(
					node_values[condition as usize].clone().unwrap(),
					// We don't subtract one here, because we wanna move past the Jump that skips
					// over the else block at true_body_instr_loc
					true_body_instr_loc as i64 - condition_instr_loc as i64
				);

				instructions[true_body_instr_loc] = Instruction::JumpRel(
					// Move past the MoveU64 that moves the false body return value into the
					// true body return value
					current_instr_loc as i64 - true_body_instr_loc as i64
				);

				if let Value::Local(local) = node_values[true_body as usize].clone().unwrap() {
					push_instr!(instructions, Instruction::Move(
						local, 
						node_values[false_body as usize].clone().unwrap(),
					));
				} else {
					panic!("This can't be a constant bruh");
				}

				let true_body_value = node_values[true_body as usize].clone();
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
						return_value_local = Some(locals.allocate(
							types.handle(ast.nodes[value as usize].type_.unwrap())
						));
					}

					let input = node_values[value as usize].clone().unwrap();

					instruction_loc += 1;
					push_instr!(instructions, Instruction::Move(return_value_local.unwrap(), input));
				}

				push_instr!(instructions, Instruction::JumpRel(-42069));

				temporary_labels.push((label, instruction_loc, return_value_local));
				node_values.push(None);
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

				let result = node_values[*contents.last().unwrap() as usize].clone();
				match return_value_loc {
					Some(location) => {
						push_instr!(instructions, Instruction::Move(location, result.unwrap()));
						node_values.push(Some(Value::Local(location)));
					}
					None => {
						node_values.push(result);
					}
				}
			}
			NodeKind::Struct { ref members } => {
				let id = node.type_.unwrap();
				let handle = types.handle(id);
				let type_kind = &types.get(id).kind;

				let local = locals.allocate(handle);
				match type_kind {
					TypeKind::Struct { members: ref type_members } => {
						for ((_, offset, type_handle), (_, member_node_id)) 
							in type_members.iter().zip(members) 
						{
							let sub_local = 
								local.sub_local(*offset, type_handle.size, type_handle.align);
							push_instr!(instructions, Instruction::Move(sub_local, node_values[*member_node_id as usize].clone().unwrap()));
						}
					}
					_ => unreachable!(),
				}

				node_values.push(Some(Value::Local(local)));
			}
			NodeKind::MemberAccess(member, sub_name) => {
				let id = ast.nodes[member as usize].type_.unwrap();
				let type_kind = &types.get(id).kind;

				let value = node_values[member as usize].clone().unwrap();

				// TODO: We don't wanna recheck the name twice, 
				match type_kind {
					TypeKind::Primitive(PrimitiveKind::U64) => {
						if sub_name == "low" {
							node_values.push(Some(value.get_sub_value(0, 4, 4)));
						} else if sub_name == "high" {
							node_values.push(Some(value.get_sub_value(4, 4, 4)));
						} else {
							panic!("bleh");
						}
					}
					TypeKind::Struct { ref members } => {
						for (name, offset, handle) in members {
							if *name == sub_name {
								node_values.push(Some(
									value.get_sub_value(*offset, handle.size, handle.align)
								));
							}
						}
					}
					_ => panic!("bleh"),
				}
			}
			NodeKind::Number(num) => {
				// TODO: Check that the number fits, although I guess this should
				// be down further up in the pipeline
				node_values.push(Some((num as u64).into()));
			}
			NodeKind::BinaryOperator { operator, left, right } => {
				let a = node_values[left as usize] .clone().unwrap();
				let b = node_values[right as usize].clone().unwrap();

				let result = locals.allocate(types.handle(ast.nodes[right as usize].type_.unwrap()));

				match operator {
					Operator::Assign => {
						match a {
							Value::Local(local) => {
								push_instr!(instructions, Instruction::Move(local, b.clone()));
							}
							Value::Pointer(local) => {
								push_instr!(
									instructions, 
									Instruction::IndirectMove(local, b.clone())
								);
							}
							_ => todo!("Left hand side of assignment cannot be constant atm"),
						}

						// TODO: Check if the result is used eventually, we will have a flag for if
						// the return value of an AstNode is used or not
						push_instr!(instructions, Instruction::Move(result, b));
					}
					Operator::Less =>
						push_instr!(instructions, Instruction::LessThan(result, a, b)),
					Operator::Add =>
						push_instr!(instructions, Instruction::WrappingAdd(result, a, b)),
					Operator::Sub =>
						push_instr!(instructions, Instruction::WrappingSub(result, a, b)),
					Operator::MulOrDeref =>
						push_instr!(instructions, Instruction::WrappingMul(result, a, b)),
					Operator::Div =>
						push_instr!(instructions, Instruction::WrappingDiv(result, a, b)),
					_ => todo!("Unhandled operator"),
				}

				node_values.push(Some(Value::Local(result)));
				
				// I know what I'm doing, we are not copying these without reason!
				// locals.free_value(node_values[left as usize].clone());
				// locals.free_value(node_values[right as usize].clone());
			}
			NodeKind::EmptyLiteral => {
				node_values.push(None);
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

				// TODO: If I have zst:s, this won't handle them properly.
				let mut offset_ctr = 0;
				let args = arg_list.iter().zip(arg_types)
					.map(|(arg, type_)| {
						let type_handle = types.handle(*type_);
						let offset = crate::align::to_aligned(type_handle.align, offset_ctr);
						offset_ctr = offset + type_handle.size;
						(offset, node_values[*arg as usize].clone().unwrap())
					})
					.collect();
				let calling = node_values[function_pointer as usize].clone().unwrap();

				push_instr!(instructions, Instruction::Call { calling, returns, args });

				node_values.push(Some(Value::Local(returns)));
			}
			NodeKind::Resource(id) => {
				node_values.push(Some(get_resource_constant(types, &mut instructions, &mut locals, &node.loc, resources, id)?))
			}

			NodeKind::UnaryOperator { operator: Operator::BitAndOrPointer, operand } => {
				let to = locals.allocate(types.handle(node.type_.unwrap()));
				let from = match node_values[operand as usize].clone().unwrap() {
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
				node_values.push(Some(Value::Local(to)));
			}
			NodeKind::UnaryOperator { operator: Operator::MulOrDeref, operand } => {
				// Get a local, no matter what!
				// (only 1 level indirect access, so you cannot indirectly access an indirect
				// so to speak)
				let from = match node_values[operand as usize].clone().unwrap() {
					Value::Local(handle) => handle,
					Value::Constant(_) => panic!("Cannot dereference constants"),
					value => {
						let local = locals.allocate(types.handle(
								ast.nodes[operand as usize].type_.unwrap()
						));
						push_instr!(instructions, Instruction::Move(local, value));
						local
					}
				};

				// Make a pointer value.
				node_values.push(Some(Value::Pointer(from.indirect_local_handle_to_self())));
			}

			// Get the type of some value as a constant.
			NodeKind::GetType(node) => {
				let type_ = ast.nodes[node as usize].type_.unwrap().into_index() as u64;
				node_values.push(Some(Value::Constant(type_.to_le_bytes().into())));
			}

			// Type expressions evaluate types with the typing system at typing type, we do not
			// need to generate any instructions for them.
			NodeKind::TypeStruct { .. } |
			NodeKind::TypeFunctionPointer { .. } |
			NodeKind::TypeBufferPointer(_) |
			NodeKind::TypePointer(_) => {
				node_values.push(None);
			}

			_ => todo!()
		}
	}

	Ok((locals.layout(), instructions, node_values.last().unwrap().clone()))
}

fn get_resource_constant(
	types: &Types,
	instructions: &mut Vec<Instruction>,
	locals: &mut Locals,
	loc: &CodeLoc,
	resources: &Resources,
	id: ResourceId
) -> Result<Value, Dependency> {
	let resource = resources.resource(id);
	match resource.kind {
		ResourceKind::Poison => panic!("Used poison. TODO: Return"),
		ResourceKind::ExternalFunction { .. } |
		ResourceKind::Function { .. } | 
		ResourceKind::String(_) =>
			Ok(id.into_index().into()),
		ResourceKind::Value(ResourceValue::Value(type_handle, ref value, ref pointer_members)) => {
			if pointer_members.len() > 0 {
				let local = locals.allocate(type_handle);
				for &(offset, sub_resource_id, sub_type_handle) in pointer_members {
					let value = 
						get_resource_constant(types, instructions, locals, loc, resources, sub_resource_id)?;

					let value_local = match value {
						Value::Local(local) => local,
						_ => {
							let value_local = locals.allocate(sub_type_handle);
							push_instr!(instructions, Instruction::Move(value_local, value));
							value_local
						}
					};

					push_instr!(instructions, Instruction::SetAddressOf(
						local.sub_local(offset, 8, 8), value_local
					));
				}

				Ok(Value::Local(local))
			} else {
				Ok(Value::Constant(value.clone()))
			}
		}
		ResourceKind::Value(_) =>
			Err(Dependency::Value(*loc, id)),
	}
}
