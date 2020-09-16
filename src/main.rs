#![feature(assoc_char_funcs)]
#![feature(drain_filter)]

#![warn(unused_qualifications)]

pub const DEBUG: bool = false;

#[macro_use]
extern crate lazy_static;

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
	scopes.insert_root_value(
		&mut resources, 
		ustr::ustr("Type"), 
		TYPE_TYPE_ID, 
		(TYPE_TYPE_ID.into_index() as u64).to_le_bytes().into(),
	);
	scopes.insert_root_value(
		&mut resources, 
		ustr::ustr("U32"), 
		TYPE_TYPE_ID, 
		(U32_TYPE_ID.into_index() as u64).to_le_bytes().into(),
	);
	scopes.insert_root_value(
		&mut resources, 
		ustr::ustr("U64"), 
		TYPE_TYPE_ID, 
		(U64_TYPE_ID.into_index() as u64).to_le_bytes().into(),
	);
	scopes.insert_root_value(
		&mut resources, 
		ustr::ustr("String"), 
		TYPE_TYPE_ID, 
		(STRING_TYPE_ID.into_index() as u64).to_le_bytes().into(),
	);

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
	let code = std::fs::read_to_string("test.im").unwrap();

	let super_scope = scopes.super_scope;
	let ast = match parser::parse_code(&code, &mut resources, &mut scopes, super_scope, true) {
		Ok(value) => value,
		Err(()) => {
			error::print_output(&code);
			return;
		}
	};

	let id = resources.insert(Resource::new(
		ast.nodes[0].loc.clone(),
		ResourceKind::Value(ResourceValue::Defined(ast)),
	));

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

	resources.check_completion();

	error::print_output(&code);

	if let ResourceKind::Value(ResourceValue::Value(_, ref value)) = resources.resource(id).kind {
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
