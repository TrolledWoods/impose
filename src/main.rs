#![feature(assoc_char_funcs)]
#![feature(drain_filter)]

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
mod code_gen;
mod run;
use std::fmt;

pub struct Routine {
	declaration: CodeLoc,
	arguments: Vec<parser::ScopeMemberId>,
	code: parser::Ast,
	instructions: Option<(code_gen::Locals, Vec<code_gen::Instruction>)>,
}

fn main() {
	let code = std::fs::read_to_string("test.im").unwrap();

	println!("Source code: ");
	println!("{}", code);
	println!();

	let mut scopes = parser::Scopes::new();

	let mut routines = Vec::new();
	let (_, ast) = match parser::parse_code(&code, &mut scopes, &mut routines) {
		Ok(value) => value,
		Err(err) => {
			print_error(&code, err);
			return;
		}
	};

	for node in ast.nodes.iter() {
		println!("{:?}: {:?} {:?}", node.loc, node.scope, node.kind);
	}

	let (locals, instructions, returns) = code_gen::compile_expression(&ast, &mut scopes);

	println!("Locals: ");
	for (i, local) in locals.locals.iter().enumerate() {
		println!("{}: {:?}", i, local);
		if let Some(member) = local.scope_member {
			print_location(&code, &scopes.member(member).declaration_location, "Declared here");
		}
	}

	println!();
	println!("Instructions: ");
	for instruction in &instructions {
		println!("{:?}", instruction);
	}

	println!("\nResult: {}", run::run_instructions(&locals, &instructions, returns));
}

fn print_location(code: &str, loc: &CodeLoc, message: &str) {
	if let Some(line) = code.lines().nth(loc.line as usize - 1) {
		println!("      |");
		println!("{:>5} | {}", loc.line, line);

		print!("      | ");

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
		println!("      |");
	} else {
		println!("After code: {}", message);
	}
}

fn print_error(code: &str, error: Error) {
	println!("ERROR at {:?}: {}", error.source_code_location, error.message);

	if let Some(line) = code.lines().nth(error.source_code_location.line as usize - 1) {
		println!("      |");
		println!("{:>5} | {}", error.source_code_location.line, line);

		print!("      | ");

		let mut chars = line.chars();
		for _ in 1..error.source_code_location.column {
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
		println!("^--");
		println!("      |");
	}
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

trait Location {
	fn get_location(&self) -> CodeLoc;
}

