use crate::{ Location, CodeLoc, Error, Result, lexer::{ self, Token, TokenKind } };
use crate::operator::Operator;
use std::collections::HashMap;

struct Context<'a, 't> {
	ast: &'a mut Ast, 
	scopes: &'a mut Scopes, 
	scope: ScopeId, 
	tokens: &'a mut TokenStream<'t>,
}

impl<'a, 't> Context<'a, 't> {
	fn borrow<'b>(&'b mut self) -> Context<'b, 't> {
		Context {
			ast: self.ast,
			scopes: self.scopes,
			scope: self.scope,
			tokens: self.tokens,
		}
	}

	fn sub_scope<'b>(&'b mut self) -> Context<'b, 't> {
		let sub_scope = self.scopes.create_scope(Some(self.scope));
		Context {
			ast: self.ast,
			scopes: self.scopes,
			scope: sub_scope,
			tokens: self.tokens,
		}
	}
}

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

	// TODO: Remove this
	#[allow(unused)]
	pub fn get_node(&self, index: u32) -> &Node {
		&self.nodes[index as usize]
	}

	// TODO: Remove this
	#[allow(unused)]
	pub fn get_node_mut(&mut self, index: u32) -> &mut Node {
		&mut self.nodes[index as usize]
	}
}

#[derive(Debug)]
pub struct Node {
	pub loc: CodeLoc,
	pub scope: ScopeId,
	pub kind: NodeKind,
}

impl Node {
	fn new(location: &impl Location, scope: ScopeId, kind: NodeKind) -> Self {
		Node { loc: location.get_location(), kind, scope }
	}
}

#[derive(Debug)]
pub enum NodeKind {
	Number(i128),
	String(String),
	EmptyLiteral,
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
	Block {
		contents: Vec<AstNodeId>,
		label: Option<ScopeMemberId>,
	},
	Skip {
		label: ScopeMemberId,
		value: Option<AstNodeId>,
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

	// fn peek_nth(&self, n: usize) -> Option<&'a Token<'a>> {
	// 	self.tokens.get(self.index + n)
	// }

	fn peek_nth_kind(&self, n: usize) -> Option<&'a TokenKind<'a>> {
		self.tokens.get(self.index + n).map(|v| &v.kind)
	}

	fn expect_peek<'b, D: std::fmt::Display>(&'b mut self, message: impl FnOnce() -> D) 
		-> Result<&'a Token<'a>> 
	{
		self.tokens.get(self.index).ok_or_else(|| error!(self, "{}", message()))
	}

	fn peek_kind(&self) -> Option<&'a TokenKind<'a>> {
		self.tokens.get(self.index).map(|v| &v.kind)
	}

	fn next(&mut self) -> Option<&'a Token<'a>> {
		self.index += 1;
		self.tokens.get(self.index - 1)
	}

	fn next_kind(&mut self) -> Option<&'a TokenKind<'a>> {
		self.index += 1;
		self.tokens.get(self.index - 1).map(|v| &v.kind)
	}

	// TODO: Remove the function or use it somewhere
	#[allow(unused)]
	fn expect_next<'b, D: std::fmt::Display>(&'b mut self, message: impl FnOnce() -> D) 
		-> Result<&'a Token<'a>> 
	{
		self.index += 1;
		self.tokens.get(self.index - 1)
			.ok_or_else(|| error!(self, "{}", message()))
	}
}

fn try_parse_create_label(
	context: Context,
) -> Result<Option<ScopeMemberId>> {
	if let Some(TokenKind::Colon) = context.tokens.peek_kind() {
		context.tokens.next();
		let loc = context.tokens.get_location();
		match context.tokens.next_kind() {
			Some(TokenKind::Identifier(name)) => {
				let id = context.scopes.declare_member(
					context.scope, 
					name.to_string(),
					&loc,
					ScopeMemberKind::Label,
				)?;
				Ok(Some(id))
			}
			_ => return_error!(loc, "Expected label name"),
		}
	} else {
		Ok(None)
	}
}

fn try_parse_label(
	context: Context,
) -> Result<Option<ScopeMemberId>> {
	if let Some(TokenKind::Colon) = context.tokens.peek_kind() {
		context.tokens.next();
		let loc = context.tokens.get_location();
		match context.tokens.next_kind() {
			Some(TokenKind::Identifier(name)) => {
				let id = context.scopes.find_member(
					context.scope, 
					name,
				).ok_or_else(|| error!(loc, "Unknown label"))?;

				if context.scopes.member(id).kind != ScopeMemberKind::Label {
					return_error!(
						loc, 
						"Expected label, got variable or constant"
					);
				}

				Ok(Some(id))
			}
			_ => return_error!(loc, "Expected label name"),
		}
	} else {
		Ok(None)
	}
}

fn parse_block(mut context: Context) 
	-> Result<AstNodeId>
{
	let loc = context.tokens.get_location();
	match context.tokens.next() {
		Some(Token { kind: TokenKind::Bracket('{'), .. }) => (),
		_ => return_error!(loc, "Expected '{{' to start block"),
	}

	let mut context = context.sub_scope();

	let label = try_parse_create_label(context.borrow())?;

	let mut commands = Vec::new();
	loop {
		match context.tokens.peek() {
			Some(Token { loc, kind: TokenKind::ClosingBracket('}') }) => {
				commands.push(context.ast.insert_node(Node::new(loc, context.scope, NodeKind::EmptyLiteral)));
				context.tokens.next();
				break;
			}
			_ => (),
		}

		let mut is_other = false;
		if let Some(TokenKind::Identifier(name)) = context.tokens.peek_kind() {
			if let Some(TokenKind::Operator(Operator::Declare)) = context.tokens.peek_nth_kind(1) 
			{
				let ident_loc   = &context.tokens.next().unwrap().loc; 
				let declare_loc = &context.tokens.next().unwrap().loc;

				// We have a declaration
				let variable_name = context.scopes.declare_member(context.scope, name.to_string(), ident_loc, ScopeMemberKind::LocalVariable)?;
				let value = parse_expression(context.borrow())?;
				commands.push(context.ast.insert_node(Node::new(declare_loc, context.scope, NodeKind::Declaration {
					variable_name, value,
				})));
				is_other = true;
			}
		}

		if !is_other {
			let expr = parse_expression(context.borrow())?;
			commands.push(expr);
		}

		let loc = context.tokens.get_location();
		match context.tokens.next() {
			Some(Token { kind: TokenKind::ClosingBracket('}'), .. }) => break,
			Some(Token { kind: TokenKind::Semicolon, .. }) => (),
			_ => return_error!(loc, "Expected ';' or '}}'"),
		}
	}

	Ok(context.ast.insert_node(Node::new(&loc, context.scope, NodeKind::Block { contents: commands, label } )))
}

#[inline]
fn parse_expression(
	context: Context,
) -> Result<AstNodeId> {
	parse_expression_rec(context, 0)
}

/// Parse an expression recursively
fn parse_expression_rec(
	mut context: Context,
	min_priority: u32, 
) -> Result<AstNodeId> {
	let mut a = parse_value(context.borrow())?;
	
	while let Some(&Token { kind: TokenKind::Operator(operator), ref loc }) = context.tokens.peek() {
		let (priority, _, left_to_right) = operator.data();

		let priority = priority.ok_or_else(
			|| error!(loc, "Operator is used as a binary operator, but it's not a binary operator")
		)?;

		if (priority + if left_to_right { 0 } else { 1 }) > min_priority {
			context.tokens.next();
			let b = parse_expression_rec(context.borrow(), priority)?;
			
			a = context.ast.insert_node(Node::new(
				context.tokens, 
				context.scope,
				NodeKind::BinaryOperator { operator, left: a, right: b }
			));
		} else {
			break;
		}
	}

	Ok(a)
}

fn parse_value(
	mut context: Context,
) -> Result<AstNodeId> {
	let token = context.tokens.expect_peek(|| "Expected value")?;
	let mut id = match token.kind {
		TokenKind::Operator(operator) => {
			context.tokens.next();
			let (_, unary_priority, _) = operator.data();

			let unary_priority = unary_priority.ok_or_else(
				|| error!(token, "Operator is not a unary operator, but it's used as one")
			)?;

			let operand = parse_expression_rec(context.borrow(), unary_priority)?;
			context.ast.insert_node(Node::new(token, context.scope, NodeKind::UnaryOperator { operator, operand }))
		}
		TokenKind::NumericLiteral(number) => {
			context.tokens.next();
			context.ast.insert_node(Node::new(token, context.scope, NodeKind::Number(number)))
		}
		TokenKind::StringLiteral(ref string) => {
			context.tokens.next();
			// TODO: Find a way to get rid of the string cloning here!
			// Possibly by making TokenStream own its data
			context.ast.insert_node(Node::new(token, context.scope, NodeKind::String(string.clone())))
		}
		TokenKind::Identifier(name) => {
			context.tokens.next();
			match context.scopes.find_member(context.scope, name) {
				Some(member) => {
					if context.scopes.member(member).kind == ScopeMemberKind::Label {
						return_error!(token, "Tried using label as a variable or a constant");
					}
					context.ast.insert_node(Node::new(token, context.scope, NodeKind::Identifier(member)))
				}
				None => return_error!(token, "Unrecognised name"),
			}
		}
		TokenKind::Bracket('{') => {
			parse_block(context.borrow())?
		}
		TokenKind::Bracket('(') => {
			context.tokens.next();
			let value = parse_expression(context.borrow())?;
			
			match context.tokens.next() {
				Some(Token { kind: TokenKind::ClosingBracket(')'), .. }) => (),
				_ => return_error!(&token, "Parenthesis is not closed properly"),
			}

			value
		}
		TokenKind::Keyword("skip") => {
			context.tokens.next();

			let loc = context.tokens.get_location();
			let label = try_parse_label(context.borrow())?.ok_or_else(
				|| error!(loc, "Expected label ':label_name'")
			)?;

			// There may be some argument to the break
			let value = if let Some(TokenKind::Bracket('(')) = context.tokens.peek_kind() {
				context.tokens.next();
				let value = parse_value(context.borrow())?;

				let loc = context.tokens.get_location();
				match context.tokens.next_kind() {
					Some(TokenKind::ClosingBracket(')')) => (),
					_ => return_error!(loc, "Expected closing ')'"),
				}

				Some(value)
			} else {
				None
			};

			context.ast.insert_node(Node::new(token, context.scope, NodeKind::Skip { label, value }))
		}
		_ => {
			return_error!(token, "Expected value");
		}
	};

	while let Some((location, arg_list)) = try_parse_list(
		context.borrow(), parse_expression, 
		&TokenKind::Bracket('('), &TokenKind::ClosingBracket(')')
	)? {
		id = context.ast.insert_node(Node::new(&location, context.scope, NodeKind::FunctionCall {
			function_pointer: id,
			arg_list,
		}));
	}

	Ok(id)
}

fn try_parse_list<'t, V>(
	mut context: Context<'_, 't>,
	mut parse_value: 
		impl for <'b> FnMut(Context<'b, 't>) -> Result<V>,
	start_bracket: &TokenKind,
	close_bracket: &TokenKind,
) -> Result<Option<(CodeLoc, Vec<V>)>> {
	if Some(start_bracket) != context.tokens.peek_kind() {
		return Ok(None);
	}
	let location = context.tokens.next().unwrap().loc.clone();
	
	let mut contents = Vec::new();
	loop {
		if &context.tokens.expect_peek(|| "List is not closed")?.kind == close_bracket {
			context.tokens.next();
			break;
		}

		contents.push(parse_value(context.borrow())?);

		let next = context.tokens.next();
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
	scopes: &mut Scopes,
) -> Result<(ScopeId, Ast)> {
	let (last_loc, tokens) = lexer::lex_code(code)?;
	let mut ast = Ast::new();
	let scope = scopes.create_scope(None);

	let mut stream = TokenStream::new(&tokens, last_loc);

	let context = Context {
		scopes,
		ast: &mut ast,
		scope,
		tokens: &mut stream,
	};
	parse_expression(context)?;

	Ok((scope, ast))
}

// TODO: Maybe make this its own type? And also, make this a NonZeroU32 eventually
pub type ScopeId = u32;
pub type ScopeMemberId = (u32, u32);

#[derive(Default, Debug)]
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

	pub fn member(&self, member: ScopeMemberId) -> &ScopeMember {
		self.scopes.get(&member.0).unwrap().members.get(&member.1).unwrap()
	}

	pub fn member_mut(&mut self, member: ScopeMemberId) -> &mut ScopeMember {
		self.scopes.get_mut(&member.0).unwrap().members.get_mut(&member.1).unwrap()
	}

	pub fn members(&mut self, scope: ScopeId) 
		-> impl Iterator<Item = &ScopeMember> 
	{
		self.scopes.get(&scope).unwrap().members.values()
	}

	fn find_member(&self, mut scope_id: ScopeId, name: &str) -> Option<ScopeMemberId> {
		let mut scope;

		loop {
			scope = self.scopes.get(&scope_id).unwrap();

			for (key, value) in scope.members.iter() {
				if value.name == name {
					return Some((scope_id, *key));
				}
			}

			scope_id = scope.parent?;
		}
	}

	pub fn declare_member(
		&mut self, 
		scope: ScopeId, 
		name: String, 
		loc: &CodeLoc,
		kind: ScopeMemberKind,
	) -> Result<ScopeMemberId> {
		for value in self.members(scope) {
			if value.name == name {
				return_error!(
					loc,
					"Name is already taken in the same scope"
				);
			}
		}

		let member = ScopeMember { 
			declaration_location: loc.clone(), 
			name,
			storage_location: None,
			kind,
		};

		let scope_instance = self.scopes.get_mut(&scope).unwrap();
		let id = (scope, scope_instance.member_ctr);
		scope_instance.members.insert(id.1, member);
		scope_instance.member_ctr += 1;
		
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

#[derive(Debug, PartialEq, Eq)]
pub enum ScopeMemberKind {
	LocalVariable,
	Label,
}

#[derive(Debug)]
pub struct ScopeMember {
	pub declaration_location: CodeLoc,
	pub name: String,
	pub kind: ScopeMemberKind,
	pub storage_location: Option<crate::code_gen::Value>,
	// pub type_: Option<Type>,
	// pub is_constant: bool,
}
