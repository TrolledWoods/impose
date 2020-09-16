#![feature(assoc_char_funcs)]
#![feature(drain_filter)]

#![warn(unused_qualifications)]

pub const DEBUG: bool = false;

#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate smallvec;

#[macro_use]
pub mod id;
#[macro_use]
pub mod error;

pub mod operator;
pub mod parser;
pub mod scopes;
pub mod types;
pub mod code_gen;
pub mod code_loc;
pub mod run;
pub mod resource;
pub mod stack_frame;
pub mod align;

fn main() {
	// VERY simple benchmarking
	let time = std::time::Instant::now();

	use scopes::*;
	use types::*;
	use resource::*;

	let mut scopes = Scopes::new();
	let mut resources = Resources::new();
	let mut types = Types::new();

	// -- NICE CONSTANTS --
	let type_type_handle = types.handle(TYPE_TYPE_ID);
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("Type"), 
		TYPE_TYPE_ID, 
		ResourceKind::Value(ResourceValue::Value(type_type_handle, (TYPE_TYPE_ID.into_index() as u64).to_le_bytes().into(), vec![])),
	).unwrap();
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("U32"), 
		TYPE_TYPE_ID, 
		ResourceKind::Value(ResourceValue::Value(type_type_handle, (U32_TYPE_ID.into_index() as u64).to_le_bytes().into(), vec![])),
	).unwrap();
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("U64"), 
		TYPE_TYPE_ID, 
		ResourceKind::Value(ResourceValue::Value(type_type_handle, (U64_TYPE_ID.into_index() as u64).to_le_bytes().into(), vec![])),
	).unwrap();
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("String"), 
		TYPE_TYPE_ID, 
		ResourceKind::Value(ResourceValue::Value(type_type_handle, (STRING_TYPE_ID.into_index() as u64).to_le_bytes().into(), vec![])),
	).unwrap();

	let print_type_id = types.insert(Type::new(TypeKind::FunctionPointer {
		args: vec![STRING_TYPE_ID],
		returns: EMPTY_TYPE_ID,
	}));
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("print"), 
		print_type_id, 
		ResourceKind::ExternalFunction {
			func: Box::new(|resources, args, _| {
				if let &[a, b, c, d, e, f, g, h] = args {
					use crate::id::Id;
					let id = ResourceId::create(usize::from_le_bytes([a, b, c, d, e, f, g, h]) as u32);
					if let ResourceKind::String(ref string) = resources.resource(id).kind {
						use std::io::Write;
						print!("{}", string);
						std::io::stdout().lock().flush().unwrap();
					}else { panic!("bad"); }
				} else { panic!("bad"); }
			}),
			n_arg_bytes: 8,
			n_return_bytes: 0,
		}
	).unwrap();

	let u64_buffer_type_id = types.insert(Type::new(TypeKind::BufferPointer(U64_TYPE_ID)));
	// TODO: When u8's happen, fix this!
	let print_type_id = types.insert(Type::new(TypeKind::FunctionPointer {
		args: vec![U64_TYPE_ID, U64_TYPE_ID],
		returns: u64_buffer_type_id,
	}));
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("alloc"), 
		print_type_id, 
		ResourceKind::ExternalFunction {
			func: Box::new(|_, args, returns| {
				if let &[a, b, c, d, e, f, g, h] = &args[0..8] {
					let n_elements = usize::from_le_bytes([a, b, c, d, e, f, g, h]);
					if let &[a, b, c, d, e, f, g, h] = &args[8..16] {
						let align = usize::from_le_bytes([a, b, c, d, e, f, g, h]);
						let pointer_bytes = (unsafe { 
							std::alloc::alloc(std::alloc::Layout::from_size_align(n_elements, align)
								.unwrap())
						} as usize).to_le_bytes();

						returns[0..8].copy_from_slice(&pointer_bytes);
						returns[8..16].copy_from_slice(&args[0..8]);
					} else { panic!("bad"); }
				} else { panic!("bad"); }
			}),
			n_arg_bytes: 16,
			n_return_bytes: 16,
		}
	).unwrap();

	let print_type_id = types.insert(Type::new(TypeKind::FunctionPointer {
		args: vec![U64_TYPE_ID],
		returns: EMPTY_TYPE_ID,
	}));
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("print_num"), 
		print_type_id, 
		ResourceKind::ExternalFunction {
			func: Box::new(|_, args, _| {
				if let &[a, b, c, d, e, f, g, h] = args {
					print!("{}", i64::from_le_bytes([a, b, c, d, e, f, g, h]));
				} else { panic!("bad"); }
			}),
			n_arg_bytes: 8,
			n_return_bytes: 0,
		}
	).unwrap();

	let print_type_id = types.insert(Type::new(TypeKind::FunctionPointer {
		args: vec![],
		returns: U64_TYPE_ID,
	}));

	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("input"), 
		print_type_id, 
		ResourceKind::ExternalFunction {
			func: Box::new(|_, _, returns| {
				let mut input = String::new();

				std::io::stdin().read_line(&mut input).unwrap();

				let num: i64 = input.trim().parse().unwrap();
				returns[0..8].copy_from_slice(&num.to_le_bytes());
			}),
			n_arg_bytes: 0,
			n_return_bytes: 8,
		}
	).unwrap();

	// -- COMPILE STUFF --
	let scope = scopes.super_scope;
	let id = resources.insert(Resource::new(
		code_loc::CodeLoc { file: ustr::ustr("no"), line: 0, column: 0 },
		ResourceKind::Value(ResourceValue::File {
			scope,
			module_folder: "".into(),
			file: "test".into(),
		}),
	));

	// Compute stuff until we are out of things to compute
	while match resources.compute_one(&mut types, &mut scopes) {
		Ok(should_continue) => {
			should_continue
		}
		Err(()) => {
			false
		}
	} {}

	if DEBUG {
		println!("\n\n --- TYPES --- ");
		types.print_types();
	}

	// See if it's ready
	resources.check_completion();

	error::print_output(&resources);

	// If the value we want got completed, print the result
	if let ResourceKind::Value(ResourceValue::Value(_, ref value, ref _pointer_members))
		= resources.resource(id).kind
	{
		// TODO: Print pointer stuff out as well.

		println!("\n\n --- RESULT ---");
		print!(" > ");
		for b in value.iter() {
			print!("{:X} ", b);
		}
		println!();
		
		println!("Completed compilation in {:?}", time.elapsed());
	}
}

fn print_location(code: &str, loc: &code_loc::CodeLoc, message: &str) {
	if let Some(line) = code.lines().nth(loc.line as usize - 1) {
		println!("{:>5} | {}", loc.line, line);

		print!("        ");

		let mut chars = line.chars();
		for _ in 1..loc.column {
			if let Some(c) = chars.next() {
				if c.is_whitespace() {
					print!("{}", c);
				} else {
					print!(" ");
				}
			} else {
				print!("X");
			}
		}
		println!("^-- {}", message);
	} else {
		println!("After code: {}", message);
	}
}
