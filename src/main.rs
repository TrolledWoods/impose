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

pub mod intrinsic;
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
		ResourceKind::Value(ResourceValue::Value(type_type_handle, 1, (TYPE_TYPE_ID.into_index() as u64).to_le_bytes().into(), vec![])),
	).unwrap();

	let mut insert_type = |name, type_: TypeId| {
		scopes.insert_root_resource(
			&mut resources, 
			ustr::ustr(name), 
			TYPE_TYPE_ID, 
			ResourceKind::Value(ResourceValue::Value(type_type_handle, 1, (type_.into_index() as u64).to_le_bytes().into(), vec![])),
		).unwrap();
	};

	insert_type("U8",    U8_TYPE_ID);
	insert_type("U16",   U16_TYPE_ID);
	insert_type("U32",   U32_TYPE_ID);
	insert_type("U64",   U64_TYPE_ID);
	insert_type("S8",    S8_TYPE_ID);
	insert_type("S16",   S16_TYPE_ID);
	insert_type("S32",   S32_TYPE_ID);
	insert_type("S64",   S64_TYPE_ID);
	insert_type("F32",   F32_TYPE_ID);
	insert_type("F64",   F64_TYPE_ID);
	insert_type("Empty", EMPTY_TYPE_ID);
	insert_type("Bool",  BOOL_TYPE_ID);

	let put_char_type_id = types.insert(Type::new(TypeKind::FunctionPointer {
		args: vec![U8_TYPE_ID],
		returns: EMPTY_TYPE_ID,
	}));
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("put_char"),
		put_char_type_id, 
		ResourceKind::ExternalFunction {
			func: Box::new(|_, args, _| {
				use std::io::Write;
				let arg = args[0];
				std::io::stdout().lock().write(&[arg]).expect("Putchar write failed");
			}),
			n_arg_bytes: 1,
			n_return_bytes: 0,
		}
	).unwrap();

	let flush_stdout_type_id = types.insert(Type::new(TypeKind::FunctionPointer {
		args: vec![],
		returns: EMPTY_TYPE_ID,
	}));
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("flush"),
		flush_stdout_type_id, 
		ResourceKind::ExternalFunction {
			func: Box::new(|_, _, _| {
				use std::io::Write;
				std::io::stdout().lock().flush().unwrap();
			}),
			n_arg_bytes: 0,
			n_return_bytes: 0,
		}
	).unwrap();

	let u8_type_buffer = types.insert(Type::new(TypeKind::Pointer(U8_TYPE_ID)));
	// TODO: When u8's happen, fix this!
	let print_type_id = types.insert(Type::new(TypeKind::FunctionPointer {
		args: vec![U64_TYPE_ID, U64_TYPE_ID],
		returns: u8_type_buffer,
	}));
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("alloc"), 
		print_type_id, 
		ResourceKind::ExternalFunction {
			func: Box::new(|_, args, returns| {
				use std::convert::TryInto;
				let n_elements = usize::from_le_bytes((&args[0..8 ]).try_into().unwrap());
				let align      = usize::from_le_bytes((&args[8..16]).try_into().unwrap());

				let pointer = unsafe { 
					std::alloc::alloc(std::alloc::Layout::from_size_align(n_elements, align)
						.unwrap())
				} as usize;

				returns[0..8].copy_from_slice(&pointer.to_le_bytes());
			}),
			n_arg_bytes: 16,
			n_return_bytes: 8,
		}
	).unwrap();

	// (pointer, size, align)
	let u64_pointer_type = types.insert(Type::new(TypeKind::Pointer(U64_TYPE_ID)));
	let print_type_id = types.insert(Type::new(TypeKind::FunctionPointer {
		args: vec![u64_pointer_type, U64_TYPE_ID, U64_TYPE_ID],
		returns: EMPTY_TYPE_ID,
	}));
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("dealloc"), 
		print_type_id, 
		ResourceKind::ExternalFunction {
			func: Box::new(|_, args, _| {
				if let &[a, b, c, d, e, f, g, h] = &args[0..8] {
					let pointer = usize::from_le_bytes([a, b, c, d, e, f, g, h]);
					if let &[a, b, c, d, e, f, g, h] = &args[8..16] {
						let n_elements = usize::from_le_bytes([a, b, c, d, e, f, g, h]);
						if let &[a, b, c, d, e, f, g, h] = &args[16..24] {
							let align = usize::from_le_bytes([a, b, c, d, e, f, g, h]);
							unsafe { 
								std::alloc::dealloc(
									pointer as *mut u8, 
									std::alloc::Layout::from_size_align(n_elements, align).unwrap(),
								);
							}
						} else { panic!("bad"); }
					} else { panic!("bad"); }
				} else { panic!("bad"); }
			}),
			n_arg_bytes: 24,
			n_return_bytes: 0,
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
		args: vec![F64_TYPE_ID],
		returns: EMPTY_TYPE_ID,
	}));
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("print_f64"), 
		print_type_id, 
		ResourceKind::ExternalFunction {
			func: Box::new(|_, args, _| {
				if let &[a, b, c, d, e, f, g, h] = args {
					print!("{}", f64::from_bits(u64::from_le_bytes([a, b, c, d, e, f, g, h])));
				} else { panic!("bad"); }
			}),
			n_arg_bytes: 8,
			n_return_bytes: 0,
		}
	).unwrap();
	let print_type_id = types.insert(Type::new(TypeKind::FunctionPointer {
		args: vec![F32_TYPE_ID],
		returns: EMPTY_TYPE_ID,
	}));
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("print_f32"), 
		print_type_id, 
		ResourceKind::ExternalFunction {
			func: Box::new(|_, args, _| {
				if let &[a, b, c, d] = args {
					print!("{}", f32::from_bits(u32::from_le_bytes([a, b, c, d])));
				} else { panic!("bad"); }
			}),
			n_arg_bytes: 4,
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
			module_folder: "test".into(),
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
	if let ResourceKind::Value(ResourceValue::Value(_, _, ref value, ref _pointer_members))
		= resources.resource(id).kind
	{
		// TODO: Print pointer stuff out as well.

		if value.len() > 0 {
			println!("\n\n --- RESULT ---");
			print!(" > ");
			for b in value.iter() {
				print!("{:X} ", b);
			}
			println!();
		}

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
