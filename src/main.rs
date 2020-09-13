#![feature(assoc_char_funcs)]
#![feature(drain_filter)]

pub const DEBUG: bool = false;

mod prelude {
	pub(crate) use crate::{ 
		DEBUG, Location, CodeLoc, Error, Result,
		resource::{ Resource, ResourceKind, Resources, ResourceId, Dependency },
		operator::Operator,
		lexer::{ self, Token, TokenKind }, 
		parser::{ NodeKind, Ast, AstNodeId, Scopes, ScopeMemberId, ScopeMemberKind },
		types::{ self, TypeId, Types, AstTyper, PrimitiveKind, TypeKind, Type },
		id::IdVec,
	};
}

use prelude::*;

#[macro_use]
mod id;

/// This is a macro to allow the compiler line and column to ergonomically be passed
/// inside the errors that are returned(for compiler debugging)
macro_rules! return_error {
	($location:expr, $($format_message:tt)+) => {{
		return Err(Error {
			message: format!($($format_message)+),
			source_code_location: $location.get_location(),
			compiler_location: CodeLoc { 
				line: line!(), 
				column: column!(), 
				file: std::rc::Rc::new(String::from(file!())),
			},
		}.into());
	}}
}

macro_rules! error {
	($location:expr, $($format_message:tt)+) => {{
		Error {
			message: format!($($format_message)+),
			source_code_location: $location.get_location(),
			compiler_location: CodeLoc { 
				line: line!(), 
				column: column!(), 
				file: std::rc::Rc::new(String::from(file!())),
			},
		}
	}}
}

mod operator;
mod lexer;
mod parser;
mod types;
mod code_gen;
mod run;
mod resource;

use std::fmt;

#[derive(Debug, Clone, Copy)]
pub enum Primitive {
	Type(TypeId),
	U64(u64),
	Pointer(ResourceId),
}

fn main() {
	let mut scopes = Scopes::new();
	let mut resources = Resources::new();
	let mut types = Types::new();

	// -- DEFINE STANDARD VALUES --
	fn print_func(resources: &Resources, arguments: &[i64]) -> i64 {
		assert_eq!(arguments.len(), 1);
		use crate::id::Id;
		let resource = resources.resource(ResourceId::create(arguments[0] as u32));
		if let ResourceKind::String(ref value) = resource.kind {
			print!("{}", value);
			use std::io::Write;
			std::io::stdout().lock().flush().unwrap();
			return 0;
		} else {
			panic!("What was passed was not a string resource: {}", arguments[0]);
		}
	}

	let string_type = types.insert(Type::new(TypeKind::String));
	let u64_id = types.u64();
	let func_type = types.insert_function(vec![string_type], u64_id);
	let string_function = resources.insert(Resource::new_with_type(
		CodeLoc {
			file: std::rc::Rc::new(String::from("no_file thanks")),
			line: 1, 
			column: 1,
		},
		ResourceKind::ExternalFunction {
			func: Box::new(print_func),
		},
		func_type,
	));
	scopes.declare_member(
		scopes.super_scope, 
		String::from("print"), 
		None, 
		ScopeMemberKind::Constant(string_function)
	).unwrap();

	fn read_int(_resources: &Resources, arguments: &[i64]) -> i64 {
		assert_eq!(arguments.len(), 0);
		let mut input = String::new();
		std::io::stdin().read_line(&mut input).unwrap();
		return input.trim().parse::<i64>().expect("Expected integer");
	}

	let u64_id = types.u64();
	let func_type = types.insert_function(vec![], u64_id);
	let read_int_function = resources.insert(Resource::new_with_type(
		CodeLoc {
			file: std::rc::Rc::new(String::from("no_file thanks")),
			line: 1, 
			column: 1,
		},
		ResourceKind::ExternalFunction {
			func: Box::new(read_int),
		},
		func_type,
	));
	scopes.declare_member(
		scopes.super_scope, 
		String::from("input_num"), 
		None, 
		ScopeMemberKind::Constant(read_int_function)
	).unwrap();
	
	fn print_num_func(_resources: &Resources, arguments: &[i64]) -> i64 {
		assert_eq!(arguments.len(), 1);
		print!("{}", arguments[0]);
		return arguments[0];
	}

	let func_type = types.insert_function(vec![types::U64_TYPE_ID], types::U64_TYPE_ID);
	let print_num_function = resources.insert(Resource::new_with_type(
		CodeLoc {
			file: std::rc::Rc::new(String::from("no_file thanks")),
			line: 1, 
			column: 1,
		},
		ResourceKind::ExternalFunction {
			func: Box::new(print_num_func),
		},
		func_type,
	));
	scopes.declare_member(
		scopes.super_scope, 
		String::from("print_num"), 
		None, 
		ScopeMemberKind::Constant(print_num_function)
	).unwrap();

	// -- COMPILE STUFF --
	let code = std::fs::read_to_string("test.im").unwrap();

	let super_scope = scopes.super_scope;
	let ast = match parser::parse_code(&code, &mut resources, &mut scopes, super_scope, true) {
		Ok(value) => value,
		Err(err) => {
			print_error(&code, err);
			return;
		}
	};

	let resource_id = resources.insert(Resource::new(
		ast.nodes[0].loc.clone(),
		ResourceKind::Value {
			code: ast,
			typer: None,
			depending_on_type: Vec::new(),
			value: None,
			depending_on_value: Vec::new(),
		}
	));

	while match resources.compute_one(&mut types, &mut scopes) {
		Ok(should_continue) => should_continue,
		Err(err) => {
			print_error(&code, err);
			false
		}
	} {}

	resources.check_completion(&code);
}

fn print_location(code: &str, loc: &CodeLoc, message: &str) {
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

fn print_error(code: &str, error: Error) {
	println!("ERROR at {:?}: {}", error.source_code_location, error.message);

	print_location(code, &error.source_code_location, "");
	println!("Compiler location: {:?}", error.compiler_location);
}

// TODO: Include file location in this.
#[derive(Clone, PartialEq, Eq)]
pub struct CodeLoc {
	pub file: std::rc::Rc<String>,
	pub line: u32, 
	pub column: u32,
}

impl Location for CodeLoc {
	fn get_location(&self) -> CodeLoc { self.clone() }
}

impl fmt::Debug for CodeLoc {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "'{}'({}:{})", self.file, self.line, self.column)
	}
}

#[derive(Debug)]
pub struct Error {	
	pub message: String,
	pub source_code_location: CodeLoc,
	pub compiler_location: CodeLoc,
}

type Result<T> = std::result::Result<T, Error>;

pub trait Location {
	fn get_location(&self) -> CodeLoc;
}

