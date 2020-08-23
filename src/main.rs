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
use std::fmt;

fn main() {
	let code = r#"
x = p = x + *y.z
	"#;

	let (last_loc, tokens) = match lexer::lex_code(code) {
		Ok(value) => value,
		Err(err) => {
			print_error(code, err);
			return;
		}
	};

	// TODO: Make parser take source code directly and call lexer in there instead.
	let ast = match parser::parse_expression_temporary(&tokens, last_loc) {
		Ok(value) => value,
		Err(err) => {
			print_error(code, err);
			return;
		}
	};

	for node in &ast.nodes {
		println!("{:?}: {:?}", node.loc, node.kind);
	}

	fn recurse(ast: &parser::Ast, node: &parser::Node) {
		match node.kind {
			parser::NodeKind::UnaryOperator  { operator, operand } => {
				print!("{:?} ", operator);
				recurse(ast, ast.get_node(operand));
			}
			parser::NodeKind::BinaryOperator { operator, left, right } => {
				print!("(");
				recurse(ast, ast.get_node(left));
				print!(" {:?} ", operator);
				recurse(ast, ast.get_node(right));
				print!(")");
			}
			parser::NodeKind::Identifier(_, name) => print!("{}", name),
			_ => unimplemented!(),
		}
	}

	recurse(&ast, &ast.nodes.last().unwrap());
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

