// TODO: Include file location in this.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CodeLoc {
	pub line: u32, 
	pub column: u32,
}

impl Location for CodeLoc {
	fn get_location(&self) -> CodeLoc { *self }
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

#[derive(Debug, Clone, Copy)]
pub struct Token<'a> {
	pub loc: CodeLoc,
	pub kind: TokenKind<'a>,
}

impl<'a> Token<'a> {
	fn new(loc: CodeLoc, kind: TokenKind<'a>) -> Self { 
		Token { loc, kind }
	}
}

#[derive(Debug, Clone, Copy)]
pub enum TokenKind<'a> {
	Identifier(&'a str),
	Keyword(&'static str),
	Operator(&'static str),
	Semicolon,
	Comma,
	Bracket(char),
	ClosingBracket(char),
	NumericLiteral(i128), // TODO: Make the numeric literal arbitrarily large.
}

impl Location for Token<'_> {
	fn get_location(&self) -> CodeLoc { self.loc }
}

struct Lexer<'a> {
	chars: std::str::CharIndices<'a>,
	source_code_location: CodeLoc,
}

impl Lexer<'_> {
	fn peek(&self) -> Option<char> {
		self.chars.clone().next().map(|(_, c)| c)
	}

	fn next(&mut self) -> Option<char> {
		self.chars.next().map(|(_, c)| c)
	}

	fn skip_if_starts_with(&mut self, text: &str) -> Option<CodeLoc> {
		let string = self.chars.as_str();
		if string.starts_with(text) {
			self.chars = string[text.len()..].char_indices();
			let old_loc = self.source_code_location;
			self.source_code_location.column += text.chars().count() as u32;
			Some(old_loc)
		} else {
			None
		}
	}
}

impl Location for Lexer<'_> {
	fn get_location(&self) -> CodeLoc { self.source_code_location }
}

fn move_pos_with_char(pos: &mut CodeLoc, character: char) {
	pos.column += 1;

	if character == '\n' {
		pos.line += 1;
		pos.column = 1;
	}
}

pub fn lex_code(code: &str) -> Result<Vec<Token>> {
	let mut lexer = Lexer {
		chars: code.char_indices(),
		source_code_location: CodeLoc { line: 1, column: 1 },
	};

	let mut tokens = Vec::new();

	skip_whitespace(&mut lexer);
	while let Some(c) = lexer.peek() {
		match c {
			'(' | '[' | '{' => {
				tokens.push(Token::new(lexer.source_code_location, TokenKind::Bracket(c)));
				lexer.next();
				lexer.source_code_location.column += 1;
			}
			')' | ']' | '}' => {
				tokens.push(Token::new(lexer.source_code_location, TokenKind::ClosingBracket(c)));
				lexer.next();
				lexer.source_code_location.column += 1;
			}
			';' => {
				tokens.push(Token::new(lexer.source_code_location, TokenKind::Semicolon));
				lexer.next();
				lexer.source_code_location.column += 1;
			}
			',' => {
				tokens.push(Token::new(lexer.source_code_location, TokenKind::Comma));
				lexer.next();
				lexer.source_code_location.column += 1;
			}
			_ if c.is_alphabetic() => {
				let (location, identifier) = lex_identifier(&mut lexer);

				let mut found_keyword = false;
				for &keyword in KEYWORDS {
					if identifier == keyword {
						tokens.push(Token::new(location, TokenKind::Keyword(keyword)));
						found_keyword = true;
					}
				}

				if !found_keyword {
					tokens.push(Token::new(location, TokenKind::Identifier(identifier)));
				}
			}
			_ if c.is_digit(10) => {
				let (loc, number) = lex_numeric_literal(&mut lexer)?;
				tokens.push(Token::new(loc, TokenKind::NumericLiteral(number)));
			}
			c => {
				// Might be an operator
				let mut found_operator = false;
				for operator in OPERATORS {
					if let Some(loc) = lexer.skip_if_starts_with(operator) {
						tokens.push(Token::new(loc, TokenKind::Operator(operator)));
						found_operator = true;
					}
				}

				if !found_operator {
					return_error!(lexer, "Invalid character {}", c);
				}
			}
		}

		skip_whitespace(&mut lexer);
	}

	Ok(tokens)
}

fn skip_whitespace(lexer: &mut Lexer) {
	while let Some(c) = lexer.peek() {
		if c == '#' {
			// Skip comment lines
			while let Some(c) = lexer.next() {
				if c == '\n' { break; }
			}

			lexer.source_code_location.column  = 1;
			lexer.source_code_location.line   += 1;
			continue;
		} 

		if !c.is_whitespace() {
			return;
		} 

		move_pos_with_char(&mut lexer.source_code_location, c);
		lexer.next();
	}
}

fn lex_numeric_literal(lexer: &mut Lexer) -> Result<(CodeLoc, i128)> {
	let location = lexer.source_code_location;
	let mut number: i128 = 0;
	let mut base         = 10;
	let mut has_custom_base = false;
	let mut has_digits = false;

	while let Some(c) = lexer.peek() {
		match c.to_digit(base) {
			Some(digit) => {
				lexer.next();
				lexer.source_code_location.column += 1;

				let (num, overflow_a) = number.overflowing_mul(base  as i128);
				let (num, overflow_b) = num   .overflowing_add(digit as i128);

				if overflow_a || overflow_b {
					return_error!(lexer, "Number too big");
				}

				number = num;
				has_digits = true;
			}
			None if c == '_' => {
				lexer.next();
				lexer.source_code_location.column += 1;
			}
			None if !has_custom_base && c.is_alphabetic() => match c {
				'c' => {
					if number > 36 {
						return_error!(location, "Cannot have a base higher than 36(got {})", number);
					} else if number < 2 {
						return_error!(location, "Cannot have a base less than 2(got {})", number);
					}

					lexer.next();
					lexer.source_code_location.column += 1;

					// This is fine because we know number is between 2 and 46
					base = number as u32; 
					number = 0;
					has_custom_base = true;
					has_digits = false;
				}
				'x' => {
					if number != 0 {
						return_error!(location, "Expected '0' before hexadecimal base specifier, got '{}'", number);
					}

					lexer.next();
					lexer.source_code_location.column += 1;

					base = 16;
					number = 0;
					has_custom_base = true;
					has_digits = false;
				}
				'b' => {
					if number != 0 {
						return_error!(location, "Expected '0' before binary base specifier, got '{}'", number);
					}

					lexer.next();
					lexer.source_code_location.column += 1;

					base = 2;
					number = 0;
					has_custom_base = true;
					has_digits = false;
				}
				_ => {
					return_error!(lexer, "Invalid custom base character in numberic literal.\n\
						If you intended to have an identifier after the number, \
						add a space in between.");
				}
			}
			None if c.is_digit(36) => {
				if c.is_alphabetic() {
					return_error!(
						lexer, 
						"Digit '{}' is not a number in the given base(alphabetic character can be digits too in high bases", c
					);
				} else {
					return_error!(
						lexer,
						"Digit '{}' is not a number in the given base",
						c
					);
				}
			}
			None => break,
		}
	}

	if !has_digits {
		return_error!(lexer, "Number has to have digits");
	}

	Ok((location, number))
}

// TODO: Make this return the code location too
fn lex_identifier<'a>(lexer: &mut Lexer<'a>) -> (CodeLoc, &'a str) {
	let location = lexer.source_code_location;
	let start = lexer.chars.as_str();

	let mut char_indices = start.char_indices();
	for (i, c) in &mut char_indices {
		if !c.is_alphabetic() {
			return (location, &start[..i]);
		} else {
			move_pos_with_char(&mut lexer.source_code_location, c);
			lexer.next();
		}
	}

	// TODO: Error message here? The end of the file should never be
	// an identifier in proper code, but the error message might be better
	// presented elsewhere, like in the parser for example.
	(location, start)
}

const OPERATORS: &[&str] = &["->", ":", "=", "+", "-", "*", "/", "%"];
const KEYWORDS:  &[&str] = &["if", "loop"];
