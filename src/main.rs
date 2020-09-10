#![feature(assoc_char_funcs)]
#![feature(drain_filter)]

mod prelude {
	pub(crate) use crate::{ 
		Location, CodeLoc, Error, Result, Primitive,
		resource::{ Resource, ResourceKind, Resources, ResourceId },
		operator::Operator,
		lexer::{ self, Token, TokenKind }, 
		parser::{ NodeKind, Ast, Scopes, ScopeMemberId, ScopeMemberKind },
		types::{ TypeId, Types, AstTyper, PrimitiveKind, TypeKind, Type },
	};
}

use prelude::*;

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
	let code = std::fs::read_to_string("test.im").unwrap();

	let mut scopes = Scopes::new();
	let mut resources = Resources::new();
	let mut types = Types::new();

	let ast = match parser::parse_code(&code, &mut resources, &mut scopes) {
		Ok(value) => value,
		Err(err) => {
			print_error(&code, err);
			return;
		}
	};

	let resource_id = resources.insert(Resource {
		loc: ast.nodes[0].loc.clone(),
		kind: ResourceKind::Value {
			code: ast,
			type_: None,
			typer: None,
			depending_on_type: Vec::new(),
			value: None,
			depending_on_value: Vec::new(),
		}
	});

	while match resources.compute_one(&mut types, &mut scopes) {
		Ok(should_continue) => should_continue,
		Err(err) => {
			print_error(&code, err);
			false
		}
	}{
		println!("Computed one!");
	}

	let resource = resources.resource(resource_id);

	if let ResourceKind::Value { 
		ref value, 
		.. 
	} = resource.kind {
		println!("\nResult: {:?}", value);
	}else if let ResourceKind::CurrentlyUsed = resource.kind {
		println!("Cannot calculate result because we had an error while calculating it");
	} else {
		unreachable!();
	}
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

