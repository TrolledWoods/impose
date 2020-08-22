use crate::{ Location, CodeLoc, Error, Result, lexer::{ Token, TokenKind } };
use std::collections::HashMap;

// TODO: Maybe make this its own type?
type AstNodeId = u32;

#[derive(Debug)]
pub struct Ast<'a> {
	pub nodes: Vec<Node<'a>>,
}

impl<'a> Ast<'a> {
	fn new() -> Self {
		Ast {
			nodes: Vec::new(),
		}
	}

	fn insert_node(&mut self, node: Node<'a>) -> AstNodeId {
		self.nodes.push(node);
		self.nodes.len() as u32 - 1
	}

	pub fn get_node(&self, index: u32) -> &Node {
		&self.nodes[index as usize]
	}

	pub fn get_node_mut(&mut self, index: u32) -> &mut Node<'a> {
		&mut self.nodes[index as usize]
	}
}

#[derive(Debug)]
pub struct Node<'a> {
	pub loc: CodeLoc,
	pub kind: NodeKind<'a>,
}

impl<'a> Node<'a> {
	fn new(location: &impl Location, kind: NodeKind<'a>) -> Self {
		Node { loc: location.get_location(), kind }
	}
}

#[derive(Debug)]
pub enum NodeKind<'a> {
	Number(i128),
	String(String),
	Identifier(ScopeId, &'a str),
	// Operator(&'a str),
	// Declaration { variable_name: &'a str, value: AstNodeId, },
	// Assignment { l_value: AstNodeId, r_value: AstNodeId, },
	// Block {
	// 	contents: Vec<AstNodeId>,
	// }
}

struct TokenStream<'a> {
	tokens: &'a [Token<'a>],
	index: usize,
	last_location: CodeLoc,
}

impl Location for TokenStream<'_> {
	fn get_location(&self) -> CodeLoc {
		self.peek().map_or(self.last_location, |t| t.loc)
	}
}

impl<'a> TokenStream<'a> {
	fn new(tokens: &'a [Token<'a>], last_location: CodeLoc) -> Self { 
		TokenStream { tokens, index: 0, last_location } 
	}

	fn peek(&self) -> Option<&Token<'a>> {
		self.tokens.get(self.index)
	}
	
	fn next(&mut self) -> Option<&Token<'a>> {
		self.index += 1;
		self.tokens.get(self.index - 1)
	}

	fn expect_next(&mut self) -> Result<&Token<'a>> {
		self.index += 1;
		match self.tokens.get(self.index - 1) {
			Some(value) => Ok(value),
			None => return_error!(self, "Premature end of file")
		}
	}
}

fn parse_expression<'a>(
	ast: &mut Ast<'a>,
	scopes: &mut Scopes,
	scope: ScopeId,
	tokens: &mut TokenStream<'a>,
) -> Result<AstNodeId> {
	parse_value(ast, scopes, scope, tokens)
}

fn parse_value<'a>(
	ast: &mut Ast<'a>,
	scopes: &mut Scopes,
	scope: ScopeId,
	tokens: &mut TokenStream<'a>,
) -> Result<AstNodeId> {
	let token = tokens.expect_next()?;
	let id = match token.kind {
		TokenKind::NumericLiteral(number) => {
			ast.insert_node(Node::new(token, NodeKind::Number(number)))
		}
		TokenKind::StringLiteral(ref string) => {
			// TODO: Find a way to get rid of the string cloning here!
			ast.insert_node(Node::new(token, NodeKind::String(string.clone())))
		}
		_ => {
			return_error!(token, "Expected value");
		}
	};
	Ok(id)
}

pub fn parse_expression_temporary<'a>(
	tokens: &'a [Token<'a>], 
	last_loc: CodeLoc,
) -> Result<Ast<'a>> {
	let mut ast = Ast::new();
	let mut scopes = Scopes::new();
	let scope = scopes.create_scope();

	let mut stream = TokenStream::new(tokens, last_loc);
	parse_expression(&mut ast, &mut scopes, scope, &mut stream)?;

	Ok(ast)
}

// TODO: Maybe make this its own type? And also, make this a NonZeroU32 eventually
pub type ScopeId = u32;

#[derive(Default)]
pub struct Scopes {
	pub scopes: HashMap<ScopeId, Scope>,
	scope_id_counter: u32,
}

impl Scopes {
	pub fn new() -> Self { Default::default() }

	pub fn create_scope(&mut self) -> ScopeId {
		let id = self.scope_id_counter;
		self.scope_id_counter += 1;
		self.scopes.insert(id, Default::default());
		id
	}
}

#[derive(Debug, Default)]
pub struct Scope {
	pub parent_scope: ScopeId,
	pub has_locals: bool,
	pub members: HashMap<u32, ScopeMember>,
}

#[derive(Debug)]
pub struct ScopeMember {
	pub declaration_location: CodeLoc,
	pub name: String,
	// pub type_: Option<Type>,
	// pub is_constant: bool,
}
