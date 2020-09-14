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
	// TODO: Only nodes that need the scope should have it, so put this into the NodeKind enum 
	// later.
	pub scope: ScopeId,
	pub kind: NodeKind,
	pub type_: Option<TypeId>,
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
			type_: None,
		}
	}

	fn new_meta(location: &impl Location, scope: ScopeId, kind: NodeKind) -> Self {
		Node { 
			loc: location.get_location(), 
			kind, 
			scope, 
			is_lvalue: false, 
			is_meta_data: true,
			type_: None,
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
	Temporary,
	/// A Member of some other node, to allow for more specific behaviour
	Member {
		child_of: AstNodeId,
		contains: AstNodeId,
		id: u8,
	},
	MemberAccess(AstNodeId, ustr::Ustr),
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
	/// # Members
	/// 0: Condition member
	/// 1: Body
	If {
		condition: AstNodeId,
		body: AstNodeId,
	},
	/// # Members
	/// 0: Condition member
	/// 1: True body
	/// 2: False body
	IfWithElse {
		condition : AstNodeId,
		true_body : AstNodeId,
		false_body: AstNodeId,
	},

	LocationMarker,
	Loop {
		body: AstNodeId,
		start_location: AstNodeId,
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
	},

	/// Returns the type of a type expression as a value instead of a type.
	GetType(AstNodeId),

	// Type expressions
	// Type expressions have all their data in their types, and are never turned into bytecode.
	// The 'type' that they have is not the type of the value, but the value itself. I.e.,
	// the type of a TypeIdentifier produced from U64 is U64, as opposed to
	// Identifier from U64 which would be of type Type.
	//
	// GetType makes the type of a typeexpression node into a constant value, to make it
	// usable for other nodes.
	/// Exactly the same as an identifier but it is a type expression.
	TypeIdentifier(ScopeMemberId),
	TypeFunctionPointer {
		arg_list: Vec<AstNodeId>,
		return_type: Option<AstNodeId>,
	},
}

struct TokenStream<'a> {
	tokens: &'a [Token],
	index: usize,
	last_location: CodeLoc,
}

impl Location for TokenStream<'_> {
	fn get_location(&self) -> CodeLoc {
		self.peek().map_or(self.last_location.clone(), |t| t.loc.clone())
	}
}

impl<'a> TokenStream<'a> {
	fn new(tokens: &'a [Token], last_location: CodeLoc) -> Self { 
		TokenStream { tokens, index: 0, last_location } 
	}

	fn peek(&self) -> Option<&'a Token> {
		self.tokens.get(self.index)
	}

	// fn peek_nth(&self, n: usize) -> Option<&'a Token> {
	// 	self.tokens.get(self.index + n)
	// }

	fn peek_nth_kind(&self, n: usize) -> Option<&'a TokenKind> {
		self.tokens.get(self.index + n).map(|v| &v.kind)
	}

	fn expect_peek<'b, D: std::fmt::Display>(&'b mut self, message: impl FnOnce() -> D) 
		-> Result<&'a Token> 
	{
		self.tokens.get(self.index).ok_or_else(|| error!(self, "{}", message()))
	}

	fn peek_kind(&self) -> Option<&'a TokenKind> {
		self.tokens.get(self.index).map(|v| &v.kind)
	}

	fn next(&mut self) -> Option<&'a Token> {
		self.index += 1;
		self.tokens.get(self.index - 1)
	}

	fn expect_next<'b, D: std::fmt::Display>(&mut self, message: impl FnOnce() -> D) 
		-> Result<&'a Token> 
	{
		self.index += 1;
		self.tokens.get(self.index - 1).ok_or_else(|| error!(self, "{}", message()))
	}

	fn next_kind(&mut self) -> Option<&'a TokenKind> {
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
				let (mut depenendants, id) = context.scopes.declare_member(
					context.scope, 
					ustr::ustr(name),
					Some(&loc),
					ScopeMemberKind::Label,
				)?;
				context.resources.resolve_dependencies(&mut depenendants);
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
					*name,
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

fn parse_block(mut context: Context, expect_brackets: bool, is_runnable: bool) 
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

				if !is_runnable {
					return_error!(ident_loc, "This scope is not runnable, so the only thing you can do is declare constants");
				}

				// We have a declaration
				let value = parse_expression(context.borrow())?;
				let (mut dependants, variable_name) = context.scopes.declare_member(
					context.scope, 
					ustr::ustr(name), 
					Some(ident_loc), 
					ScopeMemberKind::LocalVariable
				)?;
				context.resources.resolve_dependencies(&mut dependants);
				commands.push(context.ast.insert_node(
					Node::new(declare_loc, context.scope, NodeKind::Declaration {
						variable_name, value,
					})
				));
				is_other = true;
			}
		}

		if let Some(TokenKind::Identifier(name)) = context.tokens.peek_kind() {
			if let Some(TokenKind::Operator(Operator::ConstDecl)) = context.tokens.peek_nth_kind(1) 
			{
				let ident_loc   = &context.tokens.next().unwrap().loc; 
				context.tokens.next().unwrap();

				// We have a constant declaration
				let mut ast = Ast::new();
				let sub_scope = context.scopes.create_scope(Some(context.scope));

				let mut sub_context = Context {
					ast: &mut ast,
					scopes: context.scopes,
					scope: sub_scope,
					tokens: context.tokens,
					resources: context.resources,
				};

				parse_expression(sub_context.borrow())?;

				let resource_id = context.resources.insert(Resource::new(
					ident_loc.clone(),
					ResourceKind::Value {
						code: ast,
						typer: None,
						depending_on_type: vec![],
						value: None,
						depending_on_value: vec![],
					},
				));

				context.scopes.declare_member(
					context.scope, 
					*name,
					Some(ident_loc), 
					ScopeMemberKind::Constant(resource_id)
				)?;
				is_other = true;
			}
		}

		if !is_other {
			if is_runnable {
				let expr = parse_expression(context.borrow())?;
				commands.push(expr);
			} else {
				return_error!(context.tokens, "This scope is not runnable, so the only thing you can do is declare constants");
			}
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

fn parse_type_expr_value(
	mut context: Context
) -> Result<AstNodeId> {
	let token = context.tokens.expect_peek(|| "Expected type expression")?;
	match token.kind {
		TokenKind::Identifier(name) => {
			context.tokens.next();
			let member = context.scopes.find_or_create_temp(context.scope, name)?;
			Ok(context.ast.insert_node(Node::new(
				token, 
				context.scope, 
				NodeKind::TypeIdentifier(member),
			)))
		}
		TokenKind::Operator(Operator::BitwiseOrOrLambda) 
		| TokenKind::Operator(Operator::Or) => 
			parse_type_expr_function_ptr(context),
		_ => return_error!(token, "Expected type expression!"),
	}
}

fn parse_type_expr_function_ptr(
	mut context: Context
) -> Result<AstNodeId> {
	// Parse the function arguments.
	let token = context.tokens.peek().unwrap();
	let (loc, args) = if token.kind == TokenKind::Operator(Operator::Or) {
		(token.loc.clone(), vec![])
	} else {
		try_parse_list(
			context.borrow(),
			parse_type_expr_value,
			&TokenKind::Operator(Operator::BitwiseOrOrLambda),
			&TokenKind::Operator(Operator::BitwiseOrOrLambda),
		)?.ok_or_else(|| error!(token, "Expected parameter list"))?
	};

	// Do we have a return type?
	let return_type = if let Some(Token { loc: _, kind: TokenKind::Operator(Operator::Function) }) =
		context.tokens.peek() 
	{
		context.tokens.next();
		Some(parse_type_expr_value(context.borrow())?)
	} else {
		None
	};


	Ok(context.ast.insert_node(Node::new(
		token, 
		context.scope, 
		NodeKind::TypeFunctionPointer {
			arg_list: args,
			return_type,
		},
	)))
}

fn parse_function(
	parent_context: Context
) -> Result<ResourceId> {
	// Lambda definition
	let mut ast = Ast::new();
	let mut args = Vec::new();
	let sub_scope = parent_context.scopes.create_scope(Some(parent_context.scope));

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
					let (mut dependants, arg) = context.scopes.declare_member(
						sub_scope,
						ustr::ustr(name),
						Some(loc),
						ScopeMemberKind::FunctionArgument,
					)?;
					context.resources.resolve_dependencies(&mut dependants);
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

	let id = parent_context.resources.insert(Resource::new(
		token.get_location(),
		ResourceKind::Function {
			arguments: args,
			code: ast,
			instructions: None,
			typer: None,
		}
	));

	Ok(id)
}

fn parse_expression(
	mut context: Context,
) -> Result<AstNodeId> {
	let token = context.tokens.expect_peek(|| "Expected expression")?;

	// We sometime have special behaviour at the beginning of an expression. For example,
	// type expressions and function declarations can only occur here, at the root of an expression.
	match token.kind {
		TokenKind::Operator(Operator::BitwiseOrOrLambda) 
		| TokenKind::Operator(Operator::Or) => {
			let id = parse_function(context.borrow())?;
			Ok(context.ast.insert_node(Node::new(
				token, 
				context.scope, 
				NodeKind::Resource(id),
			)))
		}
		TokenKind::Keyword("type") => {
			context.tokens.next();
			let id = parse_type_expr_value(context.borrow())?;
			
			Ok(context.ast.insert_node(Node::new(
				token, 
				context.scope, 
				NodeKind::GetType(id),
			)))
		}
		_ => parse_expression_rec(context, 0),
	}
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

			// Do '.' member access. We have to write special code here, because this does not
			// become an Operator node, it because a MemberAccess node.
			if operator == Operator::Member {
				let identifier = match context.tokens
					.expect_next(|| "Expected an identifier for the . operator")?
				{
					Token { loc, kind: TokenKind::Identifier(name) } => *name,
					Token { loc, .. } => return_error!(loc, 
						"Expected an identifier for the . operator"),
				};

				a = context.ast.insert_node(Node::new(
					loc,
					context.scope,
					NodeKind::MemberAccess(a, identifier),
				));
				continue;
			}

			let b = parse_expression_rec(context.borrow(), priority)?;
			
			a = context.ast.insert_node(Node::new(
				loc,
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
			let id = context.resources.insert(
				Resource::new_with_type(
					token.loc.clone(),
					ResourceKind::String(string.clone()),
					types::STRING_TYPE_ID
				)
			);
			context.ast.insert_node(Node::new(token, context.scope, NodeKind::Resource(id)))
		}
		TokenKind::Keyword("loop") => {
			context.tokens.next();

			let start_location = context.ast.insert_node(
				Node::new(token, context.scope, NodeKind::LocationMarker)
			);
			let body = parse_expression(context.borrow())?;

			context.ast.insert_node(Node::new(token, context.scope, NodeKind::Loop {
				body,
				start_location,
			}))
		}
		TokenKind::Keyword("if") => {
			context.tokens.next();

			let condition = parse_expression(context.borrow())?;
			let condition_marker = 
				context.ast.insert_node(Node::new(token, context.scope, NodeKind::Temporary));

			let true_body = parse_block(context.borrow(), true, true)?;
			let true_body_marker =
				context.ast.insert_node(Node::new(token, context.scope, NodeKind::Temporary));

			if let Some(TokenKind::Keyword("else")) = context.tokens.peek_kind() {
				context.tokens.next();

				let false_body = parse_block(context.borrow(), true, true)?;
				let false_body_marker = 
					context.ast.insert_node(Node::new(token, context.scope, NodeKind::Temporary));

				let if_statement = context.ast.insert_node(
					Node::new(token, context.scope, NodeKind::IfWithElse {
						condition: condition_marker,
						true_body: true_body_marker,
						false_body: false_body_marker,
					})
				);

				context.ast.nodes[condition_marker as usize].kind = NodeKind::Member {
					child_of: if_statement,
					contains: condition,
					id: 0,
				};
				context.ast.nodes[true_body_marker as usize].kind = NodeKind::Member {
					child_of: if_statement,
					contains: true_body,
					id: 1,
				};
				context.ast.nodes[false_body_marker as usize].kind = NodeKind::Member {
					child_of: if_statement,
					contains: false_body,
					id: 2,
				};

				if_statement
			} else {
				let if_statement = context.ast.insert_node(
					Node::new(token, context.scope, NodeKind::If {
						condition: condition_marker,
						body: true_body_marker,
					})
				);

				context.ast.nodes[condition_marker as usize].kind = NodeKind::Member {
					child_of: if_statement,
					contains: condition,
					id: 0,
				};
				context.ast.nodes[true_body_marker as usize].kind = NodeKind::Member {
					child_of: if_statement,
					contains: true_body,
					id: 1,
				};

				if_statement
			}
		}
		TokenKind::Identifier(name) => {
			context.tokens.next();
			let member = context.scopes.find_or_create_temp(context.scope, name)?;

			context.ast.insert_node(Node::new(token, context.scope, NodeKind::Identifier(member)))
		}
		TokenKind::Bracket('{') => {
			parse_block(context.borrow(), true, true)?
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
	mut scope: ScopeId,
	is_value: bool,
) -> Result<Ast> {
	let (last_loc, tokens) = lexer::lex_code(code)?;
	let mut ast = Ast::new();


	if is_value {
		scope = scopes.create_scope(Some(scope));
	}

	let mut stream = TokenStream::new(&tokens, last_loc);

	let context = Context {
		ast: &mut ast,
		scopes,
		scope,
		tokens: &mut stream,
		resources,
	};
	parse_block(context, false, is_value)?;

	Ok(ast)
}

create_id!(ScopeId);

create_id!(
	/// NOTE: Even if 2 ScopeMemberId:s are different, doesn't mean that they point to different
	/// variables. This is because we use a system to temorarily place scope members when making constants,
	/// but that may create duplicates. For example:
	///
	/// ```impose
	/// {
	/// 	print(MY_CONSTANT);
	/// 	// Here, a temporary scope member called 'MY_CONSTANT' is created
	/// }
	/// {
	/// 	print(MY_CONSTANT);
	/// 	// Here, another temporary scope member called 'MY_CONSTANT' is created
	/// }
	///
	/// MY_CONSTANT :: "Hello, World!";
	/// // This MY_CONSTANT looks into subscopes, finds out that there are 2 temporaries that should
	/// // point to this constant. Hence, we have 2 id:s that point to MY_CONSTANT even though there
	/// // is only one constant
	/// ```
	ScopeMemberId
);

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

	pub fn insert_root_value(
		&mut self, 
		resources: &mut Resources,
		name: ustr::Ustr, 
		type_: TypeId, 
		value: crate::stack_frame::ConstBuffer,
	) {
		let loc = CodeLoc { file: std::rc::Rc::new(format!("no")), line: 0, column: 0 };
		let mut ast = Ast::new();
		ast.is_typed = true;
		let id = resources.insert_done(Resource::new_with_type(
			loc.clone(),
			ResourceKind::Value {
				code: ast,
				typer: None,
				depending_on_type: Vec::new(),
				value: Some(value),
				depending_on_value: Vec::new(),
			},
			type_,
		));

		let scope = self.super_scope;
		self.declare_member(scope, name, None, ScopeMemberKind::Constant(id));
	}

	#[allow(unused)]
	pub fn debug(&self, scope_id: ScopeId, indent: usize) {
		println!("{}Scope {:?}:", "\t".repeat(indent), scope_id);
		for member in self.scopes.get(scope_id).members.iter() {
			println!("{}Member {}: {:?}", "\t".repeat(indent), 
				self.members.get(*member).name, self.members.get(*member).kind);
		}

		for scope in self.scopes.get(scope_id).sub_scopes.iter() {
			self.debug(*scope, indent + 1);
		}
	}

	pub fn create_scope(&mut self, parent: Option<ScopeId>) -> ScopeId {
		let parent = parent.unwrap_or(self.super_scope);
		let id = self.scopes.push(Scope { 
			parent: Some(parent), 
			.. Default::default()
		});

		self.scopes.get_mut(parent).sub_scopes.push(id);

		id
	}

	pub fn member(&self, mut member: ScopeMemberId) -> &ScopeMember {
		// Because an indirect never points to another indirect(because then we can just redirect
		// to the thing that redirects), we can just do an if here.
		if let ScopeMemberKind::Indirect(indirect) = self.members.get(member).kind {
			member = indirect;
		}
		self.members.get(member)
	}

	pub fn member_mut(&mut self, mut member: ScopeMemberId) -> &mut ScopeMember {
		if let ScopeMemberKind::Indirect(indirect) = self.members.get(member).kind {
			member = indirect;
		}
		self.members.get_mut(member)
	}

	fn find_member(&self, mut scope_id: ScopeId, name: ustr::Ustr) -> Option<ScopeMemberId> {
		loop {
			for member_id in self.scopes.get(scope_id).members.iter() {
				// This does not use the ``member`` function on purpose, because the member function
				// uses indirection, while this does not use it.
				if self.members.get(*member_id).name == name {
					return Some(*member_id);
				}
			}

			scope_id = self.scopes.get(scope_id).parent?;
		}
	}

	fn get_members_in_subscopes_with_name(
		&self,
		scope_id: ScopeId,
		name: &str,
		// TODO: Use TinyVec or something to not allocate with few elements.
		buffer: &mut Vec<(ScopeId, ScopeMemberId)>,
	) {
		// If we find a member in this scope, there cannot possibly be a member in a subscope,
		// because that would be a name collision. However, there can be several different members
		// with the same name in different subscopes.
		for member_id in self.scopes.get(scope_id).members.iter().cloned() {
			if self.member(member_id).name == name {
				buffer.push((scope_id, member_id));
				// There is no way for another thing in a subscope to have the same name because 
				// that would be a name collision.
				return;
			}
		}

		// Not in this scope, so it may be in a subscope
		for sub_scope_id in self.scopes.get(scope_id).sub_scopes.iter().cloned() {
			self.get_members_in_subscopes_with_name(sub_scope_id, name, buffer);
		}
	}

	pub fn find_or_create_temp(&mut self, scope: ScopeId, name: ustr::Ustr) -> Result<ScopeMemberId> {
		if let Some(member_id) = self.find_member(scope, name) {
			return Ok(member_id);
		} else {
			let (mut dependants, id) = self.declare_member(scope, name, None, ScopeMemberKind::UndefinedDependency(Vec::new()))?;
			if let ScopeMemberKind::UndefinedDependency(ref mut vec) = self.member_mut(id).kind {
				vec.append(&mut dependants);
			} else { unreachable!(); }

			Ok(id)
		}
	}

	pub fn declare_member(
		&mut self, 
		scope: ScopeId, 
		// TODO: Make this a slice, not a string, because a temporary may already have an 
		// allocated string for the name
		name: ustr::Ustr, 
		loc: Option<&CodeLoc>,
		kind: ScopeMemberKind,
	) -> Result<(Vec<ResourceId>, ScopeMemberId)> {
		let mut same_names_in_sub_scopes = Vec::new();
		self.get_members_in_subscopes_with_name(scope, &name, &mut same_names_in_sub_scopes);

		let mut declared_member_id = None;

		let mut dependants_on_variable = Vec::new();

		// Member that we want to declare
		let mut member_we_are_declaring = Some(ScopeMember { 
			declaration_location: loc.cloned(), 
			name,
			kind,
			type_: None,
			storage_loc: None,
		});

		// TODO: If I get around to multithreading, we have to change this completely, because
		// anything can happen an that point.

		for (same_name_scope, same_name_id) in same_names_in_sub_scopes {
			// Check that the member is a temporary and not something else
			let member = self.members.get_mut(same_name_id);
			if let ScopeMemberKind::UndefinedDependency(ref mut dependants) = member.kind {
				dependants_on_variable.append(dependants);

				if let Some((_, declared_member_id)) = declared_member_id {
					// The member we have declared is already in a scope, however, 
					member.kind = ScopeMemberKind::Indirect(declared_member_id);
				} else {
					println!("Changing declaration point");

					// Swap the UndefinedDependency here with the thing we are going to declare,
					// and change the scope of it.

					*member = member_we_are_declaring.take().unwrap();

					// Change the scope
					let declared_member_scope = self.scopes.get_mut(same_name_scope);
					let index = declared_member_scope.members.iter()
						.position(|&member| member == same_name_id)
						.expect("Scope should contain member");
					declared_member_scope.members.swap_remove(index);
					self.scopes.get_mut(scope).members.push(same_name_id);

					declared_member_id = Some((same_name_scope, same_name_id));
				}
			} else {
				if let Some(ref loc) = self.member(same_name_id).declaration_location {
					// TODO: Show where it was taken before.
					return_error!(
						loc,
						"Name is already taken"
					);
				} else {
					panic!("Non code based identifier name clash");
				}
			}
		}

		let declared_member_id = match declared_member_id {
			Some((_, declared_member_id)) => {
				(dependants_on_variable, declared_member_id)
			}
			None => {
				// There is no way for us to have depenendants if there were no UndefinedDependencies,
				// because if there were a depenendant already, we would have one of those.
				assert_eq!(dependants_on_variable.len(), 0);
				let scope_instance = self.scopes.get_mut(scope);
				let id = self.members.push(member_we_are_declaring.take().unwrap());
				scope_instance.members.push(id);
				(dependants_on_variable, id)
			}
		};
		
		Ok(declared_member_id)
	}
}

#[derive(Debug, Default)]
pub struct Scope {
	// TODO: Add stack frame id:s to scopes, so that we can check if a local is from the current
	// stack frame and not some other stack frame, which can cause very weird behaviour.
	pub parent: Option<ScopeId>,
	// TODO: Make this better
	pub has_locals: bool,
	members: Vec<ScopeMemberId>,
	sub_scopes: Vec<ScopeId>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ScopeMemberKind {
	UndefinedDependency(Vec<ResourceId>),
	/// Redirects to another scope member. Used if 2 temporaries are created for the same variable,
	/// in which case on of them has to become a "false" temporary and point to the other one,
	/// because the things depending on them have different id:s.
	Indirect(ScopeMemberId),

	LocalVariable,
	FunctionArgument,
	Label,
	Constant(ResourceId),
}

#[derive(Debug)]
pub struct ScopeMember {
	pub name: ustr::Ustr,
	pub kind: ScopeMemberKind,
	pub declaration_location: Option<CodeLoc>,
	pub type_: Option<TypeId>,
	pub storage_loc: Option<crate::stack_frame::LocalHandle>,
}
