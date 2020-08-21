#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CodeLoc {
	line: u32, 
	column: u32,
}

#[derive(Debug)]
pub struct Error {	
	message: String,
	source_code_location: CodeLoc,
	compiler_location: CodeLoc,
}

// This is a macro to allow the compiler line and column to ergonomically be passed
// inside
macro_rules! make_error {
	($lexer:expr, $($format_message:tt)+) => {{
		return Err(Error {
			message: format!($($format_message)+),
			source_code_location: $lexer.source_code_location,
			compiler_location: CodeLoc { line: line!(), column: column!() },
		}.into());
	}}
}

#[derive(Debug)]
pub enum Token<'a> {
	Identifier(CodeLoc, &'a str),
	Keyword(CodeLoc, &'static str),
	Operator(CodeLoc, &'static str),
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

fn move_pos_with_char(pos: &mut CodeLoc, character: char) {
	pos.column += 1;

	if character == '\n' {
		pos.line += 1;
		pos.column = 1;
	}
}

pub fn lex_code(code: &str) -> Result<Vec<Token>, Error> {
	let mut lexer = Lexer {
		chars: code.char_indices(),
		source_code_location: CodeLoc { line: 1, column: 1 },
	};

	let mut tokens = Vec::new();

	skip_whitespace(&mut lexer);
	while let Some(c) = lexer.peek() {
		match c {
			_ if c.is_alphabetic() => {
				let identifier = lex_identifier(&mut lexer);

				let mut found_keyword = false;
				for keyword in KEYWORDS {
					if let Some(loc) = lexer.skip_if_starts_with(keyword) {
						tokens.push(Token::Keyword(loc, keyword));
						found_keyword = true;
					}
				}

				if !found_keyword {
					tokens.push(Token::Identifier(lexer.source_code_location, identifier));
				}
			}
			c => {
				// Might be an operator
				let mut found_operator = false;
				for operator in OPERATORS {
					if let Some(loc) = lexer.skip_if_starts_with(operator) {
						tokens.push(Token::Keyword(loc, operator));
						found_operator = true;
					}
				}

				if !found_operator {
					make_error!(lexer, "Invalid character {}", c);
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

			lexer.source_code_location.column += 1;
			lexer.source_code_location.line    = 1;
			continue;
		} 

		if !c.is_whitespace() {
			return;
		} 

		move_pos_with_char(&mut lexer.source_code_location, c);
		lexer.next();
	}
}

fn lex_identifier<'a>(lexer: &mut Lexer<'a>) -> &'a str {
	let start = lexer.chars.as_str();

	let mut char_indices = start.char_indices();
	for (i, c) in &mut char_indices {
		if !c.is_alphabetic() {
			return &start[..i];
		} else {
			move_pos_with_char(&mut lexer.source_code_location, c);
			lexer.next();
		}
	}

	// TODO: Error message here? The end of the file should never be
	// an identifier in proper code, but the error message might be better
	// presented elsewhere, like in the parser for example.
	start
}

const OPERATORS: &[&str] = &["->", ":", "=", "+", "-", "*", "/", "%"];
const KEYWORDS:  &[&str] = &["if", "loop"];
