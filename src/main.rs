#![feature(assoc_char_funcs)]

/// This is a macro to allow the compiler line and column to ergonomically be passed
/// inside the errors that are returned(for compiler debugging)
macro_rules! return_error {
	($location:expr, $($format_message:tt)+) => {{
		return Err(Error {
			message: format!($($format_message)+),
			source_code_location: $location.get_location(),
			compiler_location: CodeLoc { line: line!(), column: column!() },
		}.into());
	}}
}

mod lexer;
mod parser;
use std::fmt;

fn main() {
	let code = "\
42 + 63 - 23 + print(\"Hello world!\\n\")
	";

	let (last_loc, tokens) = match lexer::lex_code(code) {
		Ok(value) => value,
		Err(err) => {
			println!("ERROR: {}", err.message);
			println!("{}", code);
			println!("{}^", "-".repeat(
				err.source_code_location.column.saturating_sub(1) as usize
			));
			return;
		}
	};

	// TODO: Make parser take source code directly and call lexer in there instead.
	let ast = parser::parse_expression_temporary(&tokens, last_loc);

	println!("{:?}", ast);
}

// TODO: Include file location in this.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct CodeLoc {
	pub line: u32, 
	pub column: u32,
}

impl Location for CodeLoc {
	fn get_location(&self) -> CodeLoc { *self }
}

impl fmt::Debug for CodeLoc {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "({}, {})", self.line, self.column)
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

