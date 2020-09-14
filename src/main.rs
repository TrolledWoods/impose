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
mod stack_frame;
mod align;

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

	// -- NICE CONSTANTS --
	scopes.insert_root_value(
		&mut resources, 
		ustr::ustr("Type"), 
		types::TYPE_TYPE_ID, 
		(types::TYPE_TYPE_ID.into_index() as u64).to_le_bytes().into(),
	);
	scopes.insert_root_value(
		&mut resources, 
		ustr::ustr("U32"), 
		types::TYPE_TYPE_ID, 
		(types::U32_TYPE_ID.into_index() as u64).to_le_bytes().into(),
	);
	scopes.insert_root_value(
		&mut resources, 
		ustr::ustr("U64"), 
		types::TYPE_TYPE_ID, 
		(types::U64_TYPE_ID.into_index() as u64).to_le_bytes().into(),
	);

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

	let id = resources.insert(Resource::new(
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

	if let ResourceKind::Value { value: Some(ref value), .. } = resources.resource(id).kind {
		print!("Result: ");
		for b in value.iter() {
			print!("{:X} ", b);
		}
		println!();
	} else {
		println!("Don't know the value");
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
