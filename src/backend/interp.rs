use crate::intrinsic::*;
use crate::resource::*;
use crate::types::*;
use crate::align::*;
use crate::parser::MarkerKind;

use std::collections::HashMap;
use std::alloc::{ alloc, dealloc, Layout };

pub type Value = smallvec::SmallVec<[u8; 8]>;

struct Stack {
	buffer: *mut u8,
	buffer_max: *mut u8,
	head: *mut u8,
	member_sizes: Vec<usize>,
}

impl Stack {
	fn new() -> Self {
		let stack_layout = Layout::from_size_align(STACK_SIZE, STACK_ALIGN).unwrap();
		let stack_ptr: *mut u8 = unsafe { alloc(stack_layout) };

		Stack {
			buffer: stack_ptr,
			buffer_max: unsafe { stack_ptr.add(STACK_SIZE) },
			head: stack_ptr,
			member_sizes: Vec::new(),
		}
	}

	fn push(&mut self, value: *const u8, size: usize) {
		self.member_sizes.push(size);
		if size == 0 { return; }

		assert!(self.head as usize + size < self.buffer_max as usize, "Stack overflow");

		unsafe {
			std::ptr::copy(value, self.head, size);
			self.head = self.head.add(to_aligned(size, STACK_ALIGN));
		}
	}

	fn pop(&mut self) -> (*const u8, usize) {
		let size = self.member_sizes.pop().unwrap();
		if size == 0 { return (std::ptr::NonNull::dangling().as_ptr(), 0); }

		unsafe {
			self.head = self.head.sub(to_aligned(size, STACK_ALIGN));
			(self.head, size)
		}
	}
}

impl Drop for Stack {
	fn drop(&mut self) {
		unsafe {
			dealloc(self.buffer, Layout::from_size_align(STACK_SIZE, STACK_ALIGN).unwrap());
		}
	}
}

const STACK_SIZE:  usize = 2048;
const STACK_ALIGN: usize = 16;

pub fn interpret(resources: &Resources, types: &Types, ast: &Ast) -> Value {
	// Allocate some buffers
	let mut stack = Stack::new();

	// Find the marker locations.
	// TODO: Move this out somewhere else to not do it for every function call.
	let mut label_map = HashMap::new();
	for (node_id, node) in ast.nodes.iter().enumerate() {
		match node.kind {
			NodeKind::Marker(MarkerKind::IfElseTrueBody
				{ contains: _, true_body_label, false_body_label: _}) => 
			{
				label_map.insert(true_body_label, node_id + 1);
			}
			NodeKind::Marker(MarkerKind::LoopHead(label_id)) => {
				label_map.insert(label_id, node_id);
			}
			NodeKind::Block { label, .. } => {
				label_map.insert(label, node_id);
			}
			NodeKind::If(label) => {
				label_map.insert(label, node_id);
			}
			NodeKind::IfWithElse { end_label } => {
				label_map.insert(end_label, node_id);
			}
			NodeKind::Loop(_, body) => {
				label_map.insert(body, node_id + 1);
			}
			_ => (),
		}
	}

	// Run the program
	let mut node_id = 0;
	while let Some(node) = ast.nodes.get(node_id) {
		node_id += 1;
		if node.is_meta_data { continue; }
		
		// TODO: Include enough information in the Ast to not have to rely on the runtime
		// to keep track of the size of values.
		match node.kind {
			NodeKind::Marker(MarkerKind::IfCondition(_, label_id)) => {
				// The size of a boolean is 1.
				let (condition, size) = stack.pop();
				assert_eq!(size, 1);

				if unsafe { *condition } == 0 {
					node_id = *label_map.get(&label_id).unwrap();
				}
			}
			NodeKind::Marker(MarkerKind::IfElseTrueBody
				{ contains: _, true_body_label: _, false_body_label}) => 
			{
				node_id = *label_map.get(&false_body_label).unwrap();
			}
			NodeKind::Marker(MarkerKind::LoopHead(_)) => { }
			NodeKind::MemberAccess { offset, size } => {
				let (value, length) = stack.pop();
				assert!(offset + size <= length);
				stack.push(unsafe { value.add(offset) }, size);
			}
			NodeKind::Constant(ref buffer) =>
				stack.push(buffer.as_ptr(), buffer.len()),
			NodeKind::IntrinsicTwo(intrinsic_kind) => {
				let (right, right_len) = stack.pop();
				let (left, left_len)   = stack.pop();
				let mut output = 0;
				run_intrinsic_two(
					intrinsic_kind,
					&mut output,
					unsafe { std::slice::from_raw_parts(left, left_len) },
					unsafe { std::slice::from_raw_parts(right, right_len) },
				);

				stack.push(output as *const u64 as *const u8, types.handle(node.type_).size);
			}

			NodeKind::ScopeMemberReference(_) => todo!(),
			NodeKind::Identifier(_) => todo!(),

			NodeKind::BitCast => {},

			NodeKind::Assign => {
				let (value, value_len) = stack.pop();
				let (pointer, pointer_len) = stack.pop();

				if value_len > 0 {
					assert_eq!(pointer_len, 8);

					unsafe {
						std::ptr::copy(value, *(pointer as *mut *mut u8), value_len);
					}

					stack.push(value, value_len);
				}
			},

			NodeKind::Resource(id) => {
				let resource = resources.resource(id);
				match resource.kind {
					ResourceKind::Done(ref value, ref pointers) => {
						let mut value_copy = value.clone();

						for &(sub_offset, sub_id, _) in pointers {
							match resources.resource(sub_id).kind {
								ResourceKind::Done(ref sub_value, ref sub_pointers) => {
									if sub_pointers.len() > 0 {
										panic!("Cannot copy a resource with recursive subpointers");
									}

									value_copy[sub_offset..sub_offset + 8].copy_from_slice(
										&(sub_value.as_ptr() as usize).to_le_bytes()
									);
								}
								_ => {
									todo!("We can't currently deal with non-finished resources");
								}
							}
						}

						stack.push(value_copy.as_ptr(), value_copy.len());
					},
					_ => {
						todo!("We can't currently deal with non-finished resources");
					}
				}
			},
			NodeKind::FunctionCall(_) => todo!(),

			NodeKind::Dereference => {
				let (pointer, pointer_len) = stack.pop();
				assert_eq!(pointer_len, 8);

				stack.push(unsafe { *(pointer as *mut *mut u8) }, types.handle(node.type_).size);
			},
			NodeKind::If(_) => { },
			NodeKind::IfWithElse { end_label: _ } => {},

			NodeKind::Loop(head, _) => node_id = *label_map.get(&head).unwrap(),

			NodeKind::Struct { .. } => todo!(),

			NodeKind::DeclareFunctionArgument(_) => todo!(),
			NodeKind::Declaration { variable_name: _, } => todo!(),
			NodeKind::Block { ref contents, label: _ } => {
				let (return_value, return_value_length) = stack.pop();
				for _ in contents[1..].iter() {
					stack.pop();
				}

				stack.push(return_value, return_value_length);
			},
			NodeKind::Skip { label } => {
				node_id = *label_map.get(&label).unwrap();
			},
		}
	}

	let (buffer_raw_ptr, buffer_raw_len) = stack.pop();
	let buffer = unsafe { std::slice::from_raw_parts(buffer_raw_ptr, buffer_raw_len).into() };

	buffer
}
