use crate::prelude::*;
use crate::operator::Operator;

struct Context<'a, 't> {
	ast: &'a mut Ast, 
	scopes: &'a mut Scopes,
	scope: ScopeId, 
	tokens: &'a mut TokenStream<'t>,
	resources: &'a mut Resources,
}

impl<'a, 't> Context<'a, 't> {
	fn borrow<'b>(&'b mut self) -> Context<'b, 't> {
		Context {
			ast: self.ast,
			scopes: self.scopes,
			scope: self.scope,
			tokens: self.tokens,
			resources: self.resources,
		}
	}

	fn sub_scope<'b>(&'b mut self) -> Context<'b, 't> {
		let sub_scope = self.scopes.create_scope(Some(self.scope));
		Context {
			ast: self.ast,
			scopes: self.scopes,
			scope: sub_scope,
			tokens: self.tokens,
			resources: self.resources,
		}
	}
}

// TODO: Maybe make this its own type?
pub type AstNodeId = u32;

#[derive(Debug)]
pub struct Ast {
	pub nodes: Vec<Node>,
	pub is_typed: bool,
}

impl Ast {
	fn new() -> Self {
		Ast { 
			nodes: Vec::new(),
			is_typed: false,
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
	/// Meta data is for typing and other things to use, and shouldn't be included
	/// in the actual code output.
	pub is_meta_data: bool,
}

impl Node {
	fn new(location: &impl Location, scope: ScopeId, kind: NodeKind) -> Self {
		Node { 
			loc: location.get_location(), 
			kind, 
			scope, 
			is_lvalue: false, 
			is_meta_data: false,
		}
	}

	fn new_meta(location: &impl Location, scope: ScopeId, kind: NodeKind) -> Self {
		Node { 
			loc: location.get_location(), 
			kind, 
			scope, 
			is_lvalue: false, 
			is_meta_data: true,
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
	Type(TypeKind),
	EmptyLiteral,
	Identifier(ScopeMemberId),
	Resource(ResourceId),
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
	DeclareFunctionArgument { variable_name: ScopeMemberId, type_node: AstNodeId },
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
				let id = context.scopes.declare_member(
					context.scope, 
					name.to_string(),
					Some(&loc),
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

fn parse_block(mut context: Context, expect_brackets: bool) 
	-> Result<AstNodeId>
{
	let loc = context.tokens.get_location();
	if expect_brackets {
		match context.tokens.next() {
			Some(Token { kind: TokenKind::Bracket('{'), .. }) => (),
			_ => return_error!(loc, "Expected '{{' to start block"),
		}
	}

	let mut context = context.sub_scope();

	let label = try_parse_create_label(context.borrow())?;

	let mut commands = Vec::new();
	loop {
		match context.tokens.peek() {
			Some(Token { loc, kind: TokenKind::ClosingBracket('}') }) if expect_brackets => {
				commands.push(context.ast.insert_node(Node::new(loc, context.scope, NodeKind::EmptyLiteral)));
				context.tokens.next();
				break;
			}
			None if !expect_brackets => {
				commands.push(context.ast.insert_node(Node::new(context.tokens, context.scope, NodeKind::EmptyLiteral)));
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
				let variable_name = context.scopes.declare_member(
					context.scope, 
					name.to_string(), 
					Some(ident_loc), 
					ScopeMemberKind::LocalVariable
				)?;
				commands.push(context.ast.insert_node(
					Node::new(declare_loc, context.scope, NodeKind::Declaration {
						variable_name, value,
					})
				));
				is_other = true;
			}
		}

		if !is_other {
			let expr = parse_expression(context.borrow())?;
			commands.push(expr);
		}

		let loc = context.tokens.get_location();
		match context.tokens.next() {
			Some(Token { kind: TokenKind::ClosingBracket('}'), .. }) if expect_brackets => break,
			Some(Token { kind: TokenKind::Semicolon, .. }) => (),
			None if !expect_brackets => break,
			_ => return_error!(loc, 
				"Expected ';' or '}}', did you forget a semicolon or did you forget an operator?"),
		}
	}

	Ok(context.ast.insert_node(Node::new(&loc, context.scope, NodeKind::Block { contents: commands, label } )))
}

fn parse_function(
	parent_context: Context
) -> Result<ResourceId> {
	// Lambda definition
	let mut ast = Ast::new();
	let mut args = Vec::new();
	let sub_scope = parent_context.scopes.create_scope(None);

	let mut context = Context {
		ast: &mut ast,
		scopes: parent_context.scopes,
		scope: sub_scope,
		tokens: parent_context.tokens,
		resources: parent_context.resources,
	};

	let token = context.tokens.peek().expect("Don't call parse_function without a '|' to start");
	if let TokenKind::Operator(Operator::BitwiseOrOrLambda) = token.kind {
		try_parse_list(
			context.borrow(), 
			|context| {
				let value = context.tokens.expect_next(|| "Expected function argument name")?;
				if let Token { loc, kind: TokenKind::Identifier(name) } = value {
					let arg = context.scopes.declare_member(
						sub_scope,
						name.to_string(),
						Some(loc),
						ScopeMemberKind::FunctionArgument,
					)?;
					args.push(arg);

					let node_id = context.ast.insert_node(
						Node::new_meta(loc, sub_scope, NodeKind::Type(TypeKind::Primitive(PrimitiveKind::U64)))
					);
					context.ast.insert_node(Node::new(loc, sub_scope, 
						NodeKind::DeclareFunctionArgument {
							variable_name: arg,
							type_node: node_id,
						}
					));

					Ok(())
				} else {
					Err(error!(value, "Expected function argument name"))
				}
			},
			&TokenKind::Operator(Operator::BitwiseOrOrLambda),
			&TokenKind::Operator(Operator::BitwiseOrOrLambda),
		)?;
	} else {
		assert_eq!(context.tokens.next().unwrap().kind, TokenKind::Operator(Operator::Or));
	}

	// Parse the function body.
	parse_expression(context.borrow())?;

	let id = parent_context.resources.insert(Resource {
		loc: token.get_location(),
		type_: None,
		kind: ResourceKind::Function {
			arguments: args,
			code: ast,
			instructions: None,
			typer: None,
		}
	});

	Ok(id)
}

fn parse_expression(
	mut context: Context,
) -> Result<AstNodeId> {
	let token = context.tokens.expect_peek(|| "Expected expression")?;
	if let TokenKind::Operator(Operator::BitwiseOrOrLambda) 
		| TokenKind::Operator(Operator::Or) = token.kind 
	{
		let id = parse_function(context.borrow())?;
		return Ok(context.ast.insert_node(Node::new(
			token, 
			context.scope, 
			NodeKind::Resource(id),
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
			let id = context.resources.insert(Resource {
				loc: token.get_location(),
				type_: Some(types::STRING_TYPE_ID),
				kind: ResourceKind::String(string.clone()),
			});
			context.ast.insert_node(Node::new(token, context.scope, NodeKind::Resource(id)))
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
			parse_block(context.borrow(), true)?
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
	resources: &mut Resources,
	scopes: &mut Scopes,
) -> Result<Ast> {
	let (last_loc, tokens) = lexer::lex_code(code)?;
	let mut ast = Ast::new();
	let scope = scopes.create_scope(None);

	let mut stream = TokenStream::new(&tokens, last_loc);

	let context = Context {
		ast: &mut ast,
		scopes,
		scope,
		tokens: &mut stream,
		resources,
	};
	parse_block(context, false)?;

	Ok(ast)
}

create_id!(ScopeId);
create_id!(ScopeMemberId);

/// Scopes contains all the scopes in the entire program.
#[derive(Debug)]
pub struct Scopes {
	scopes: IdVec<Scope, ScopeId>,
	members: IdVec<ScopeMember, ScopeMemberId>,
	/// The super_scope is stuff that is contained within all the things.
	pub super_scope: ScopeId,
}

impl Scopes {
	pub fn new() -> Self {
		let mut scopes = IdVec::new();
		let super_scope = scopes.push(Default::default());
		Scopes {
			scopes,
			members: IdVec::new(),
			super_scope,
		}
	}

	pub fn create_scope(&mut self, parent: Option<ScopeId>) -> ScopeId {
		self.scopes.push(Scope { 
			parent: Some(parent.unwrap_or(self.super_scope)), 
			.. Default::default()
		})
	}

	pub fn member(&self, member: ScopeMemberId) -> &ScopeMember {
		self.members.get(member)
	}

	pub fn member_mut(&mut self, member: ScopeMemberId) -> &mut ScopeMember {
		self.members.get_mut(member)
	}

	fn find_member(&self, mut scope_id: ScopeId, name: &str) -> Option<ScopeMemberId> {
		loop {
			for member_id in self.scopes.get(scope_id).members.iter() {
				if self.members.get(*member_id).name == name {
					return Some(*member_id);
				}
			}

			scope_id = self.scopes.get(scope_id).parent?;
		}
	}

	pub fn declare_member(
		&mut self, 
		scope: ScopeId, 
		name: String, 
		loc: Option<&CodeLoc>,
		kind: ScopeMemberKind,
	) -> Result<ScopeMemberId> {
		if let Some(_) = self.find_member(scope, &name) {
			if let Some(loc) = loc {
				// TODO: Show where it was taken before.
				return_error!(
					loc,
					"Name is already taken"
				);
			} else {
				panic!("Non code based identifier name clash");
			}
		}

		let member = ScopeMember { 
			declaration_location: loc.cloned(), 
			name,
			kind,
			type_: None,
			storage_loc: None,
		};

		let scope_instance = self.scopes.get_mut(scope);
		let id = self.members.push(member);
		scope_instance.members.push(id);
		
		Ok(id)
	}
}

#[derive(Debug, Default)]
pub struct Scope {
	pub parent: Option<ScopeId>,
	// TODO: Make this better
	pub has_locals: bool,
	members: Vec<ScopeMemberId>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ScopeMemberKind {
	LocalVariable,
	FunctionArgument,
	Label,
	Constant(ResourceId),
}

#[derive(Debug)]
pub struct ScopeMember {
	pub name: String,
	pub kind: ScopeMemberKind,
	pub declaration_location: Option<CodeLoc>,
	pub type_: Option<TypeId>,
	pub storage_loc: Option<crate::code_gen::LocalId>,
}
