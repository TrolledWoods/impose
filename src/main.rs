#![feature(assoc_char_funcs)]

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

mod operator;
mod lexer;
mod parser;
mod code_gen;
use std::fmt;

fn main() {
	let code = r#"{ 
	20; 
	50 + 20 - 600;
	14 - 245;
	14 - 245;
	14 - 245;
	14 - 245;
	14 - 245;
	60; 
	50 - 20 + 10 
}"#;

	println!("Source code: ");
	println!("{}", code);
	println!();

	// TODO: Make parser take source code directly and call lexer in there instead.
	let ast = match parser::parse_code(code) {
		Ok(value) => value,
		Err(err) => {
			print_error(code, err);
			return;
		}
	};

	let last = ast.nodes.len() - 1;
	let (locals, instructions) = code_gen::compile_expression(&ast, last as u32);

	println!("Locals: ");
	for (i, &(locks, uses)) in locals.locals.iter().enumerate() {
		println!("{}: locks {}, uses {}", i, locks, uses);
	}

	println!();
	println!("Instructions: ");
	for instruction in &instructions {
		println!("{:?}", instruction);
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

