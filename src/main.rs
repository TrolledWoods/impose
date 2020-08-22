mod lexer;

fn main() {
	let code = "x := 42;";
	match lexer::lex_code(code) {
		Ok(tokens) => {
			println!("{:?}", tokens);
		},
		Err(err) => {
			println!("ERROR: {}", err.message);
			println!("{}", code);
			println!("{}^", "-".repeat(
				err.source_code_location.column.saturating_sub(1) as usize
			));
		}
	};
}
