use std::fmt;

use crate::DEBUG;
use crate::intrinsic::*;
use crate::types::*;
use crate::parser::MarkerKind;
use crate::scopes::*;
use crate::resource::*;
use crate::stack_frame::*;
use crate::operator::*;
use crate::code_loc::*;

pub enum Instruction {
	DebugLocation(CodeLoc),

	IntrinsicTwoArgs(IntrinsicKindTwo, LocalHandle, Value, Value),

	SetAddressOf(LocalHandle, LocalHandle),
	GetAddressOfResource(LocalHandle, ResourceId),

	IndirectMove(IndirectLocalHandle, Value),
	Move(LocalHandle, Value),

	JumpRel(LabelId),
	JumpRelIfZero(Value, LabelId),
	Call {
		calling: Value, 
		returns: LocalHandle, 
		args: Vec<(usize, Value, usize)>,
	},
}

impl fmt::Debug for Instruction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Instruction::DebugLocation(loc)
				=> write!(f, " -- {:?} -- ", loc),
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

pub struct Program {
	pub layout: std::sync::Arc<StackFrameLayout>,
	pub instructions: Vec<Instruction>,
	pub labels: Vec<usize>,
	pub value: Value,
}

// TODO: Add a struct with data about compiling an expression, so that we can keep going
// at the same point that we stopped if there is an undefined dependency.
pub fn compile_expression(
	ast: &Ast, 
	scopes: &mut Scopes,
	resources: &Resources,
	types: &Types,
) -> Result<Program, Dependency> {
	let mut locals = Locals::new();
	let mut node_values: Vec<Value> = Vec::new();
	let mut instructions = Vec::new();
	let mut labels = vec![None; ast.locals.labels.len()];

	// Allocate locals for all the things to reside within
	let mut label_locals = Vec::new();

	for node in ast.nodes.iter() {
		if node.is_meta_data { 
			continue; 
		}

		// TODO: Get rid of this
		if label_locals.len() == 0 && !matches!(node.kind, NodeKind::DeclareFunctionArgument { .. }) {
			label_locals = ast.locals.labels.iter()
				.map(|&v| locals.allocate(types.handle(v)))
				.collect::<Vec<_>>();
		}

		// instructions.push(Instruction::DebugLocation(node.loc));

		let evaluation_value = match node.kind {
			NodeKind::BitCast => {
				node_values.pop().unwrap()
			}
			NodeKind::Identifier(member_id) => {
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

				match left {
					Value::Local(handle) => {
						push_move(&mut instructions, handle, right.clone());
					},
					Value::Pointer(handle) => {
						push_move_indirect(&mut instructions, handle, right.clone());
					},
					Value::Function(_) => {
						panic!("Cannot assign to a function");
					}
					Value::Constant(_) => {
						panic!("Cannot assign to a constant");
					}
				};

				right
			}
			NodeKind::IntrinsicTwo(kind) => {
				let right = node_values.pop().unwrap();
				let left  = node_values.pop().unwrap();

				let result = locals.allocate(types.handle(node.type_.unwrap()));
				instructions.push(Instruction::IntrinsicTwoArgs(kind, result, left, right));
				Value::Local(result)
			},
			NodeKind::DeclareFunctionArgument { variable_name, .. } => {
				let scope_member = scopes.member_mut(variable_name);

				let location = locals.allocate(types.handle(scope_member.type_.unwrap()));
				scope_member.storage_loc = Some(location);

				continue;
			}
			NodeKind::Declaration { variable_name } => {
				let input = node_values.pop().unwrap();
				let location = locals.allocate_raw(input.size(), 1);
				scopes.member_mut(variable_name).storage_loc = Some(location);
				push_move(&mut instructions, location, input);

				Value::Local(EMPTY_LOCAL)
			}
			NodeKind::Marker(MarkerKind::LoopHead(label)) => {
				assert_eq!(labels[label.into_index()], None);
				labels[label.into_index()] = Some(instructions.len());
				Value::Local(EMPTY_LOCAL)
			}
			NodeKind::Marker(MarkerKind::IfCondition(_, label)) => {
				let value = node_values.pop().unwrap();
				instructions.push(Instruction::JumpRelIfZero(value, label));
				Value::Local(EMPTY_LOCAL)
			}
			NodeKind::Marker(
				MarkerKind::IfElseTrueBody { contains, true_body_label, false_body_label }
			) => {
				// Instruction to move the value into a new local, so that the else can
				// also use that same local
				let local = locals.allocate(
					types.handle(ast.nodes[contains as usize].type_.unwrap())
				);
				push_move(&mut instructions, local, node_values.pop().unwrap());

				// Jump instruction to skip else
				instructions.push(Instruction::JumpRel(false_body_label));

				labels[true_body_label.into_index()] = Some(instructions.len());

				Value::Local(local)
			}
			NodeKind::Loop(label, break_label) => {
				node_values.pop().unwrap(); // Loop body
				node_values.pop().unwrap(); // Loop head marker

				instructions.push(Instruction::JumpRel(label));

				labels[break_label.into_index()] = Some(instructions.len());

				Value::Local(label_locals[break_label.into_index()])
			}
			NodeKind::If(end_label) => {
				let _true_body = node_values.pop().unwrap();
				let _condition = node_values.pop().unwrap();

				labels[end_label.into_index()] = Some(instructions.len());

				Value::Local(EMPTY_LOCAL)
			}
			NodeKind::IfWithElse { end_label, .. } => {
				// TODO: Do more sophisticated stuff with never types.

				let false_body = node_values.pop().unwrap();
				let true_body = node_values.pop().unwrap();
				let _condition = node_values.pop().unwrap();

				let return_value = match (true_body.size(), false_body.size()) {
					(0, 0) => Value::Local(EMPTY_LOCAL),
					(_, 0) => true_body,
					(0, _) => false_body,
					(_, _) => {
						let handle = if let Value::Local(handle) = true_body { handle }
							else { panic!() };

						push_move(&mut instructions, handle, false_body);

						true_body
					}
				};

				labels[end_label.into_index()] = Some(instructions.len());

				return_value
			}
			NodeKind::Skip { label, .. } => {
				let value = node_values.pop().unwrap();
				push_move(&mut instructions, label_locals[label.into_index()], value);

				instructions.push(Instruction::JumpRel(label));

				Value::Local(EMPTY_LOCAL)
			}
			NodeKind::Block { ref contents, label } => {
				let result = node_values.pop().unwrap();
				node_values.truncate(node_values.len() + 1 - contents.len());

				let label_loc = label_locals[label.into_index()];
				push_move(&mut instructions, label_loc, result);

				labels[label.into_index()] = Some(instructions.len());

				Value::Local(label_loc)
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
							push_move(&mut instructions, sub_local, node_values.pop().unwrap());
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

				instructions.push(Instruction::Call { calling, returns, args });

				Value::Local(returns)
			}
			NodeKind::Resource(id) => {
				let (_, value) = get_resource_constant(types, &mut instructions, &mut locals, &node.loc, resources, id)?;
				value
			}

			NodeKind::UnaryOperator { operator: Operator::BitAndOrPointer } => {
				let to = locals.allocate(types.handle(node.type_.unwrap()));
				let from = match node_values.pop().unwrap() {
					Value::Local(handle) => handle,
					value => {
						let local = locals.allocate_raw(value.size(), 1);
						push_move(&mut instructions, local, value);
						local
					}
				};

				instructions.push(Instruction::SetAddressOf(to, from));
				Value::Local(to)
			}
			NodeKind::UnaryOperator { operator: Operator::MulOrDeref } => {
				// Get a local, no matter what!
				// (only 1 level indirect access, so you cannot indirectly access an indirect
				// so to speak)
				let from = match node_values.pop().unwrap() {
					Value::Local(handle) => handle,
					Value::Function(_) => panic!("Cannot dereference functions"),
					Value::Constant(_) => panic!("Cannot dereference constants"),
					Value::Pointer(handle) => {
						// TODO: Is it fine to not have any alignment here?
						let local = locals.allocate_raw(handle.resulting_size, 1);
						push_move(&mut instructions, local, Value::Pointer(handle));
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
	}

	if DEBUG {
		println!("\n---Instructions generated ---");
		for (i, instruction) in instructions.iter().enumerate() {
			for (label, val) in labels.iter().enumerate() {
				if *val == Some(i) {
					println!(" -- label {}:", label);
				}
			}
			if let Instruction::DebugLocation(_) = *instruction {
				// print_location(resources.code_cache.get(&loc.file).unwrap(), &loc, "");
			} else {
				println!("{:?}", instruction);
			}
		}

		for (label, val) in labels.iter().enumerate() {
			if *val == Some(instructions.len()) {
				println!(" -- label {}:", label);
			}
		}
	}

	Ok(Program {
		layout: std::sync::Arc::new(locals.layout()),
		instructions,
		labels: labels.into_iter().map(|v| v.unwrap()).collect(),
		value: node_values.pop().unwrap(),
	})
}

fn push_move_indirect(instructions: &mut Vec<Instruction>, into: IndirectLocalHandle, from: Value) {
	if from.size() > 0 {
		assert_eq!(into.resulting_size, from.size());

		instructions.push(Instruction::IndirectMove(into, from));
	}
}

fn push_move(instructions: &mut Vec<Instruction>, into: LocalHandle, from: Value) {
	if from.size() > 0 {
		assert_eq!(into.size, from.size());

		instructions.push(Instruction::Move(into, from));
	}
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
		ResourceKind::Done(_, ref pointer_members) 
			if pointer_members.len() == 0 => 
		{
			// There is an instruction for this!
			instructions.push(Instruction::GetAddressOfResource(local, id));
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
					instructions.push(Instruction::Move(value_local, value));
					value_local
				}
			};

			instructions.push(Instruction::SetAddressOf(local, value_local));
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
		ResourceKind::Function { .. } =>
			Ok((1, id.into_index().into())),
		ResourceKind::Done(ref value, ref pointer_members) => {
			let type_handle = types.handle(resource.type_.unwrap());

			if pointer_members.len() > 0 {
				// TODO: Deal with pointers in pointer buffers.

				let local = locals.allocate(type_handle);

				push_move(instructions, local, Value::Constant(value.clone()));

				for &(offset, sub_resource_id, sub_type_handle) in pointer_members {
					// Put the resource pointer into the right local.
					get_resource_pointer(types, instructions, locals, loc, resources, sub_resource_id, local.sub_local(offset, 8, 8), sub_type_handle)?;
				}

				Ok((value.len().checked_div(type_handle.size).unwrap_or(1), Value::Local(local)))
			} else {
				match types.get(resource.type_.unwrap()).kind {
					TypeKind::FunctionPointer { .. } => {
						use std::convert::TryInto;
						Ok((8, Value::Function(usize::from_le_bytes(value.as_slice().try_into().unwrap()))))
					}
					_ => {
						Ok((value.len().checked_div(type_handle.size).unwrap_or(1), Value::Constant(value.clone())))
					}
				}
			}
		}
		ResourceKind::Value(_) =>
			Err(Dependency::Value(*loc, id)),
	}
}
