mod parser;

fn main() {
	let thing = parser::lex_string(r#"
		let x hello # Something is happening here
		asdlkfj uhib sodifj # Something more is happening here
		hallåj

	"#).unwrap();
	println!("Success! {:?}", thing);
}
