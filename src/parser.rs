use crate::{ Location, CodeLoc, Error, Result, lexer::{ self, Token, TokenKind }, Routine };
use crate::operator::Operator;
use std::num::NonZeroU32;

struct Context<'a, 't> {
	ast: &'a mut Ast, 
	scope: ScopeId, 
	tokens: &'a mut TokenStream<'t>,
	routines: &'a mut Vec<Routine>,
}

impl<'a, 't> Context<'a, 't> {
	fn borrow<'b>(&'b mut self) -> Context<'b, 't> {
		Context {
			ast: self.ast,
			scope: self.scope,
			tokens: self.tokens,
			routines: self.routines,
		}
	}

	fn sub_scope<'b>(&'b mut self) -> Context<'b, 't> {
		let sub_scope = self.ast.scopes.create_scope(Some(self.scope));
		Context {
			ast: self.ast,
			scope: sub_scope,
			tokens: self.tokens,
			routines: self.routines,
		}
	}
}

// TODO: Maybe make this its own type?
pub type AstNodeId = u32;

#[derive(Debug)]
pub struct Ast {
	pub scopes: Scopes,
	pub nodes: Vec<Node>,
}

impl Ast {
	fn new() -> Self {
		Ast { 
			nodes: Vec::new(),
			scopes: Scopes::new(),
		}
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
	pub is_lvalue: bool,
}

impl Node {
	fn new(location: &impl Location, scope: ScopeId, kind: NodeKind) -> Self {
		Node { 
			loc: location.get_location(), 
			kind, 
			scope, 
			is_lvalue: false, 
		}
	}
}

impl Location for Node {
	fn get_location(&self) -> CodeLoc {
		self.loc.clone()
	}
}

#[derive(Debug)]
pub enum NodeKind {
	Number(i128),
	String(String),
	EmptyLiteral,
	Identifier(ScopeMemberId),
	FunctionDeclaration {
		routine_id: usize,
	},
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

	fn expect_next<'b, D: std::fmt::Display>(&mut self, message: impl FnOnce() -> D) 
		-> Result<&'a Token<'a>> 
	{
		self.index += 1;
		self.tokens.get(self.index - 1).ok_or_else(|| error!(self, "{}", message()))
	}

	fn next_kind(&mut self) -> Option<&'a TokenKind<'a>> {
		self.index += 1;
		self.tokens.get(self.index - 1).map(|v| &v.kind)
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
				let id = context.ast.scopes.declare_member(
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
				let id = context.ast.scopes.find_member(
					context.scope, 
					name,
				).ok_or_else(|| error!(loc, "Unknown label"))?;

				if context.ast.scopes.member(id).kind != ScopeMemberKind::Label {
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
				let value = parse_expression(context.borrow())?;
				let variable_name = context.ast.scopes.declare_member(context.scope, name.to_string(), ident_loc, ScopeMemberKind::LocalVariable)?;
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
	mut context: Context,
) -> Result<AstNodeId> {
	let token = context.tokens.expect_peek(|| "Expected expression")?;
	if let TokenKind::Operator(Operator::BitwiseOrOrLambda) = token.kind {
		// Lambda definition
		let mut ast = Ast::new();
		let mut args = Vec::new();
		let sub_scope = ast.scopes.create_scope(None);
		try_parse_list(
			context.borrow(), 
			|context| {
				let value = context.tokens.expect_next(|| "Expected function argument name")?;
				if let Token { loc, kind: TokenKind::Identifier(name) } = value {
					args.push(context.ast.scopes.declare_member(
						sub_scope, 
						name.to_string(), 
						&loc,
						ScopeMemberKind::FunctionArgument,
					)?);
					Ok(())
				} else {
					Err(error!(value, "Expected function argument name"))
				}
			},
			&TokenKind::Operator(Operator::BitwiseOrOrLambda),
			&TokenKind::Operator(Operator::BitwiseOrOrLambda),
		)?;
		let mut sub_context = Context {
			ast: &mut ast,
			scope: sub_scope,
			tokens: context.tokens,
			routines: context.routines,
		};

		// Parse the function body.
		parse_expression(sub_context.borrow())?;

		let id = context.routines.len();
		context.routines.push(Routine {
			declaration: token.loc.clone(),
			arguments: args,
			code: ast,
			instructions: None,
		});

		return Ok(context.ast.insert_node(Node::new(
			token, 
			context.scope, 
			NodeKind::FunctionDeclaration { routine_id: id }
		)));
	}

	parse_expression_rec(context, 0)
}

/// Parse an expression recursively
fn parse_expression_rec(
	mut context: Context,
	min_priority: u32, 
) -> Result<AstNodeId> {
	let lvalue_starting_node = context.ast.nodes.len();
	let mut a = parse_value(context.borrow())?;
	
	while let Some(&Token { kind: TokenKind::Operator(operator), ref loc }) = context.tokens.peek() {
		let (priority, _, left_to_right) = operator.data();

		let priority = priority.ok_or_else(
			|| error!(loc, "Operator is used as a binary operator, but it's not a binary operator")
		)?;

		if operator == Operator::Assign {
			// The left side of the assignment is an lvalue
			for node in &mut context.ast.nodes[lvalue_starting_node..] {
				node.is_lvalue = true;
			}
		}

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
		TokenKind::Operator(Operator::BitwiseOrOrLambda) => {
			return_error!(token, "Function declarations can only be the first thing in an expression");
		}
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
			match context.ast.scopes.find_member(context.scope, name) {
				Some(member) => {
					if context.ast.scopes.member(member).kind == ScopeMemberKind::Label {
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
				let value = parse_expression(context.borrow())?;

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
	routines: &mut Vec<Routine>,
) -> Result<Ast> {
	let (last_loc, tokens) = lexer::lex_code(code)?;
	let mut ast = Ast::new();
	let scope = ast.scopes.create_scope(None);

	let mut stream = TokenStream::new(&tokens, last_loc);

	let context = Context {
		ast: &mut ast,
		scope,
		tokens: &mut stream,
		routines,
	};
	parse_expression(context)?;

	Ok(ast)
}

// TODO: Make a macro to auto-generate these kinds of id:s
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(NonZeroU32);

impl ScopeId {
	fn new(id: usize) -> Self {
		Self(NonZeroU32::new(id as u32 + 1).unwrap())
	}

	fn get(self) -> usize {
		self.0.get() as usize - 1
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeMemberId(NonZeroU32);

impl ScopeMemberId {
	fn new(id: usize) -> Self {
		Self(NonZeroU32::new(id as u32 + 1).unwrap())
	}

	fn get(self) -> usize {
		self.0.get() as usize - 1
	}
}

/// A buffer that stores some data 'T' for every member in the
/// scope.
pub struct ScopeBuffer<T> {
	data: Vec<T>,
}

impl<T> ScopeBuffer<T> {
	pub fn member(&self, member_id: ScopeMemberId) -> &T {
		&self.data[member_id.get()]
	}

	pub fn member_mut(&mut self, member_id: ScopeMemberId) -> &mut T {
		&mut self.data[member_id.get()]
	}
}

/// Scopes contains all the scopes for a routine. A single routine has its own local scope,
/// because that makes it easy to duplicate the scope data for polymorphism and such.
/// 
/// This means however that we may need a separate system for constants, because those
/// are not ordered and all that. But we may have needed a separate system for those anyway,
/// so I'm not too worried about it.
#[derive(Default, Debug)]
pub struct Scopes {
	scopes: Vec<Scope>,
	members: Vec<ScopeMember>,
}

impl Scopes {
	pub fn new() -> Self { Default::default() }

	pub fn create_buffer<T>(&self, mut default: impl FnMut() -> T) -> ScopeBuffer<T> {
		ScopeBuffer {
			data: (0..self.members.len())
				.map(|_| default())
				.collect(),
		}
	}

	pub fn create_scope(&mut self, parent: Option<ScopeId>) -> ScopeId {
		let id = self.scopes.len();
		self.scopes.push(Scope { parent, .. Default::default() });
		ScopeId::new(id)
	}

	pub fn member(&self, member: ScopeMemberId) -> &ScopeMember {
		&self.members[member.get()]
	}

	pub fn member_mut(&mut self, member: ScopeMemberId) -> &mut ScopeMember {
		&mut self.members[member.get()]
	}

	pub fn members(&mut self, scope: ScopeId) 
		-> impl Iterator<Item = &ScopeMember> 
	{
		self.members.iter()
	}

	fn find_member(&self, mut scope_id: ScopeId, name: &str) -> Option<ScopeMemberId> {
		let mut scope;

		loop {
			scope = &self.scopes[scope_id.get()];

			for (i, value) in scope.members.iter().enumerate() {
				if self.member(*value).name == name {
					return Some(ScopeMemberId::new(i));
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
			kind,
		};

		let scope_instance = &mut self.scopes[scope.get()];
		let id = ScopeMemberId::new(scope_instance.members.len());
		self.members.push(member);
		scope_instance.members.push(id);
		
		Ok(id)
	}
}

#[derive(Debug, Default)]
pub struct Scope {
	pub parent: Option<ScopeId>,
	pub has_locals: bool,
	members: Vec<ScopeMemberId>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ScopeMemberKind {
	LocalVariable,
	FunctionArgument,
	Label,
}

#[derive(Debug)]
pub struct ScopeMember {
	pub name: String,
	pub kind: ScopeMemberKind,
	pub declaration_location: CodeLoc,
}
