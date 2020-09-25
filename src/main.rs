#![feature(assoc_char_funcs)]
#![feature(drain_filter)]

#![warn(unused_qualifications)]
#![deny(warnings)]

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

lazy_static! {
	static ref INSTANT: std::time::Instant = std::time::Instant::now();
}

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
	scopes.insert_root_resource(
		&mut resources, 
		ustr::ustr("Type"), 
		TYPE_TYPE_ID, 
		ResourceKind::Done((TYPE_TYPE_ID.into_index() as u64).to_le_bytes().into(), vec![]),
	).unwrap();

	let mut insert_type = |name, type_: TypeId| {
		scopes.insert_root_resource(
			&mut resources, 
			ustr::ustr(name), 
			TYPE_TYPE_ID, 
			ResourceKind::Done((type_.into_index() as u64).to_le_bytes().into(), vec![]),
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

	{
		use std::convert::TryInto;
		let buffer_pointer = types.insert(Type::new(TypeKind::BufferPointer(U8_TYPE_ID)));
		let function_kind = resources.create_function(FunctionKind::ExternalFunction {
			func: Box::new(|_, args, _| {
				let string_pointer = usize::from_le_bytes(args[..8].try_into().unwrap()) as *const u8;
				let length = usize::from_le_bytes(args[8..16].try_into().unwrap());

				let slice = unsafe {
					std::slice::from_raw_parts(string_pointer, length)
				};

				print!("{}", std::str::from_utf8(slice).unwrap());
			}), n_arg_bytes: 16, n_return_bytes: 0, });
		scopes.insert_root_resource(&mut resources, ustr::ustr("print"),
			types.insert_function(vec![buffer_pointer], EMPTY_TYPE_ID),
			function_kind,
		).unwrap();
	}

	{
		use std::convert::TryInto;
		let pointer_u8 = types.insert(Type::new(TypeKind::Pointer(U8_TYPE_ID)));
		let function_kind = resources.create_function(FunctionKind::ExternalFunction {
			func: Box::new(|_, args, returns| {
				let size  = usize::from_le_bytes(args[0..8 ].try_into().unwrap());
				let align = usize::from_le_bytes(args[8..16].try_into().unwrap());
				returns.copy_from_slice(
					&(unsafe {
						std::alloc::alloc(std::alloc::Layout::from_size_align(size, align).unwrap())
					} as usize).to_le_bytes()
				);
			}), n_arg_bytes: 16, n_return_bytes: 8, });
		scopes.insert_root_resource(&mut resources, ustr::ustr("alloc"),
			types.insert_function(vec![U64_TYPE_ID, U64_TYPE_ID], pointer_u8),
			function_kind,
		).unwrap();
	}

	{
		use std::convert::TryInto;
		let pointer_u8 = types.insert(Type::new(TypeKind::Pointer(U8_TYPE_ID)));
		let function_kind = resources.create_function(FunctionKind::ExternalFunction {
			func: Box::new(|_, args, _| {
				let pointer = usize::from_le_bytes(args[0..8 ].try_into().unwrap()) as *mut u8;
				let size    = usize::from_le_bytes(args[0..8 ].try_into().unwrap());
				let align   = usize::from_le_bytes(args[8..16].try_into().unwrap());
				unsafe {
					std::alloc::dealloc(pointer, std::alloc::Layout::from_size_align(size, align).unwrap())
				};
			}), n_arg_bytes: 24, n_return_bytes: 0, });
		scopes.insert_root_resource(&mut resources, ustr::ustr("free"),
			types.insert_function(vec![pointer_u8, U64_TYPE_ID, U64_TYPE_ID], EMPTY_TYPE_ID),
			function_kind,
		).unwrap();
	}

	{
		let function_kind = resources.create_function(FunctionKind::ExternalFunction {
			func: Box::new(|_, args, _| {
				use std::io::Write;
				let arg = args[0];
				std::io::stdout().lock().write(&[arg]).expect("Putchar write failed");
			}), n_arg_bytes: 1, n_return_bytes: 0, });
		scopes.insert_root_resource(&mut resources, ustr::ustr("put_char"),
			types.insert_function(vec![U8_TYPE_ID], EMPTY_TYPE_ID),
			function_kind,
		).unwrap();
	}

	{
		let function_kind = resources.create_function(FunctionKind::ExternalFunction {
			func: Box::new(|_, _, _| {
				use std::io::Write;
				std::io::stdout().lock().flush().unwrap();
			}), n_arg_bytes: 0, n_return_bytes: 0, });
		scopes.insert_root_resource(&mut resources, ustr::ustr("flush"),
			types.insert_function(vec![], EMPTY_TYPE_ID), 
			function_kind,
		).unwrap();
	}

	{
		let function_kind = resources.create_function(FunctionKind::ExternalFunction {
			func: Box::new(|_, _, returns| {
				returns.copy_from_slice(&(INSTANT.elapsed().as_nanos() as u64).to_le_bytes());
			}), n_arg_bytes: 0, n_return_bytes: 8, });
		scopes.insert_root_resource(&mut resources, ustr::ustr("current_time_ns"), 
			types.insert_function(vec![], U64_TYPE_ID),
			function_kind,
		).unwrap();
	}

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
	if let ResourceKind::Done(ref value, ref _pointer_members)
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
