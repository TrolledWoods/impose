use crate::{ Location, CodeLoc, Error, Result, lexer::{ self, Token, TokenKind } };
use crate::operator::Operator;
use std::collections::HashMap;

// TODO: Make a Context type to pass around instead of all the things.
// We gotta make sure we know what should go into the context first though, and not pass
// too many things in it.

// TODO: Maybe make this its own type?
pub type AstNodeId = u32;

#[derive(Debug)]
// TODO: Remove lifetime here, i.e. make the abstract syntax tree completely
// independent of any borrowed strings from the source code. Force loading all the files to compile
// feels like a bad idea.
pub struct Ast {
	pub nodes: Vec<Node>,
}

impl Ast {
	fn new() -> Self {
		Ast { nodes: Vec::new() }
	}

	fn insert_node(&mut self, node: Node) -> AstNodeId {
		self.nodes.push(node);
		self.nodes.len() as u32 - 1
	}

	pub fn get_node(&self, index: u32) -> &Node {
		&self.nodes[index as usize]
	}

	pub fn get_node_mut(&mut self, index: u32) -> &mut Node {
		&mut self.nodes[index as usize]
	}
}

#[derive(Debug)]
pub struct Node {
	pub loc: CodeLoc,
	pub kind: NodeKind,
}

impl Node {
	fn new(location: &impl Location, kind: NodeKind) -> Self {
		Node { loc: location.get_location(), kind }
	}
}

#[derive(Debug)]
pub enum NodeKind {
	Number(i128),
	String(String),
	Identifier(ScopeMemberId),
	FunctionCall {
		function_pointer: AstNodeId,
		arg_list: Vec<AstNodeId>,
	},
	BinaryOperator {
		operator: Operator,
		left:  AstNodeId,
		right: AstNodeId,
	},
	UnaryOperator {
		operator: Operator,
		operand: AstNodeId,
	},
	Declaration { variable_name: ScopeMemberId, value: AstNodeId, },
	// Assignment { l_value: AstNodeId, r_value: AstNodeId, },
	Block {
		contents: Vec<AstNodeId>,
	}
}

struct TokenStream<'a> {
	tokens: &'a [Token<'a>],
	index: usize,
	last_location: CodeLoc,
}

impl Location for TokenStream<'_> {
	fn get_location(&self) -> CodeLoc {
		self.peek().map_or(self.last_location.clone(), |t| t.loc.clone())
	}
}

impl<'a> TokenStream<'a> {
	fn new(tokens: &'a [Token<'a>], last_location: CodeLoc) -> Self { 
		TokenStream { tokens, index: 0, last_location } 
	}

	fn peek(&self) -> Option<&'a Token<'a>> {
		self.tokens.get(self.index)
	}

	fn peek_kind(&self) -> Option<&'a TokenKind<'a>> {
		self.tokens.get(self.index).map(|v| &v.kind)
	}

	fn next(&mut self) -> Option<&'a Token<'a>> {
		self.index += 1;
		self.tokens.get(self.index - 1)
	}

	fn expect_next<'b, D: std::fmt::Display>(&'b mut self, message: impl FnOnce() -> D) 
		-> Result<&'a Token<'a>> 
	{
		self.index += 1;
		match self.tokens.get(self.index - 1) {
			Some(value) => Ok(value),
			None => return_error!(self, "{}", message())
		}
	}
}

fn parse_expression<'a>(
	ast: &mut Ast,
	scopes: &mut Scopes,
	scope: ScopeId,
	tokens: &mut TokenStream<'a>,
) -> Result<AstNodeId> {
	parse_expression_rec(ast, scopes, scope, tokens, 0)
}

/// Parse an expression recursively
fn parse_expression_rec<'a>(
	ast: &mut Ast,
	scopes: &mut Scopes,
	scope: ScopeId,
	tokens: &mut TokenStream<'a>,
	min_priority: u32, 
) -> Result<AstNodeId> {
	let mut a = parse_value(ast, scopes, scope, tokens)?;
	
	while let Some(&Token { kind: TokenKind::Operator(operator), ref loc }) = tokens.peek() {
		let (priority, _, left_to_right) = operator.data();

		let priority = match priority {
			Some(priority) => priority,
			None => return_error!(
				loc, 
				"Operator is used as a binary operator, but it's not a binary operator"
			),
		};

		if (priority + if left_to_right { 0 } else { 1 }) > min_priority {
			// Skip the operator
			tokens.next();

			let b = parse_expression_rec(ast, scopes, scope, tokens, priority)?;
			
			a = ast.insert_node(Node::new(
				tokens, 
				NodeKind::BinaryOperator { operator, left: a, right: b }
			));
		} else {
			break;
		}
	}

	Ok(a)
}

fn parse_value<'a>(
	ast: &mut Ast,
	scopes: &mut Scopes,
	scope: ScopeId,
	tokens: &mut TokenStream<'a>,
) -> Result<AstNodeId> {
	let token = tokens.expect_next(|| "Expected value")?;
	let mut id = match token.kind {
		TokenKind::Operator(operator) => {
			let (_, unary_priority, _) = operator.data();

			if let Some(unary_priority) = unary_priority {
				let operand = parse_expression_rec(ast, scopes, scope, tokens, unary_priority)?;
				ast.insert_node(Node::new(token, NodeKind::UnaryOperator { operator, operand }))
			} else {
				return_error!(token, "Operator is not a unary operator, but it's used as one");
			}
		}
		TokenKind::NumericLiteral(number) => {
			ast.insert_node(Node::new(token, NodeKind::Number(number)))
		}
		TokenKind::StringLiteral(ref string) => {
			// TODO: Find a way to get rid of the string cloning here!
			// Possibly by making TokenStream own its data
			ast.insert_node(Node::new(token, NodeKind::String(string.clone())))
		}
		TokenKind::Identifier(name) => {
			match scopes.find_member(scope, name) {
				Some(member) => ast.insert_node(Node::new(token, NodeKind::Identifier(member))),
				None => return_error!(token, "Unrecognised name"),
			}
		}
		TokenKind::Bracket('(') => {
			let value = parse_expression(ast, scopes, scope, tokens)?;
			
			match tokens.next() {
				Some(Token { kind: TokenKind::ClosingBracket(')'), .. }) => (),
				_ => return_error!(&token, "Parenthesis is not closed properly"),
			}

			value
		}
		_ => {
			return_error!(token, "Expected value");
		}
	};

	while let Some((location, arg_list)) = try_parse_list(
		ast, scopes, scope, tokens, parse_expression, 
		&TokenKind::Bracket('('), &TokenKind::ClosingBracket(')')
	)? {
		id = ast.insert_node(Node::new(&location, NodeKind::FunctionCall {
			function_pointer: id,
			arg_list,
		}));
	}

	Ok(id)
}

fn try_parse_list<'a, V>(
	ast: &mut Ast,
	scopes: &mut Scopes,
	scope: ScopeId,
	tokens: &mut TokenStream<'a>,
	mut parse_value: 
		impl for <'b> FnMut(&'b mut Ast, &'b mut Scopes, ScopeId, &'b mut TokenStream<'a>
			) -> Result<V>,
	start_bracket: &TokenKind,
	close_bracket: &TokenKind,
) -> Result<Option<(CodeLoc, Vec<V>)>> {
	if Some(start_bracket) != tokens.peek_kind() {
		return Ok(None);
	}
	let location = tokens.next().unwrap().loc.clone();
	
	let mut contents = Vec::new();
	loop {
		if match tokens.peek_kind() {
			Some(kind) => kind,
			None => return_error!(location, "List is not closed"),
		} == close_bracket {
			tokens.next();
			break;
		}

		contents.push(parse_value(ast, scopes, scope, tokens)?);

		let next = tokens.next();
		match next.map(|t| &t.kind) {
			Some(TokenKind::Comma) => (),
			Some(something) if something == close_bracket => break,
			Some(_) => return_error!(next.unwrap(), "Expected ',' to separate items in list"),
			None => return_error!(location, "List is not closed"),
		}
	}

	Ok(Some((location, contents)))
}

pub fn parse_code(
	code: &str,
) -> Result<Ast> {
	let (last_loc, tokens) = lexer::lex_code(code)?;
	let mut ast = Ast::new();
	let mut scopes = Scopes::new();
	let scope = scopes.create_scope(None);

	let mut stream = TokenStream::new(&tokens, last_loc);
	parse_expression(&mut ast, &mut scopes, scope, &mut stream)?;

	Ok(ast)
}

// TODO: Maybe make this its own type? And also, make this a NonZeroU32 eventually
pub type ScopeId = u32;
pub type ScopeMemberId = (u32, u32);

#[derive(Default)]
pub struct Scopes {
	pub scopes: HashMap<ScopeId, Scope>,
	scope_id_counter: u32,
}

impl Scopes {
	pub fn new() -> Self { Default::default() }

	pub fn create_scope(&mut self, parent: Option<ScopeId>) -> ScopeId {
		let id = self.scope_id_counter;
		self.scope_id_counter += 1;
		self.scopes.insert(id, Scope { parent, .. Default::default() });
		id
	}

	fn member(&self, member: ScopeMemberId) -> &ScopeMember {
		self.scopes.get(&member.0).unwrap().members.get(&member.1).unwrap()
	}

	fn find_member(&self, scope_id: ScopeId, name: &str) -> Option<ScopeMemberId> {
		let mut scope = self.scopes.get(&scope_id).unwrap();

		loop {
			for (key, value) in scope.members.iter() {
				if value.name == name {
					return Some((scope_id, *key));
				}
			}

			scope = self.scopes.get(&scope.parent?).unwrap();
		}
	}

	fn declare_member(
		&mut self, 
		scope: ScopeId, 
		name: String, 
		loc: &CodeLoc,
	) -> Result<ScopeMemberId> {
		if let Some(old) = self.find_member(scope, &name) {
			// TODO: When I add info things, make sure to add some info here!
			return_error!(
				self.member(old).declaration_location, 
				"Scope member already declared here"
			);
		}

		let member = ScopeMember { 
			declaration_location: loc.clone(), 
			name,
			storage_location: None,
		};

		let scope = self.scopes.get_mut(&scope).unwrap();
		let id = (self.scope_id_counter, scope.member_ctr);
		scope.members.insert(id.1, member);
		self.scope_id_counter += 1;
		scope.member_ctr += 1;
		
		Ok(id)
	}
}

#[derive(Debug, Default)]
pub struct Scope {
	pub parent: Option<ScopeId>,
	pub has_locals: bool,
	// TODO: Maybe just make members a Vec?
	members: HashMap<u32, ScopeMember>,
	member_ctr: u32,
}

#[derive(Debug)]
pub struct ScopeMember {
	pub declaration_location: CodeLoc,
	pub name: String,
	pub storage_location: Option<crate::code_gen::Value>,
	// pub type_: Option<Type>,
	// pub is_constant: bool,
}
