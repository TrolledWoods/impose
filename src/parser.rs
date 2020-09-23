use crate::operator::Operator;

use crate::intrinsic::*;
use crate::error::*;
use crate::scopes::*;
use crate::resource::*;
use crate::types::*;
use crate::code_loc::*;

mod lexer;
use lexer::*;

struct Context<'a, 't> {
	ast: &'a mut Ast, 
	scopes: &'a mut Scopes,
	types: &'a mut Types,
	scope: ScopeId, 
	tokens: &'a mut TokenStream<'t>,
	resources: &'a mut Resources,
	is_meta: bool,
	folder: ustr::Ustr,
}

impl<'a, 't> Context<'a, 't> {
	fn new_stackframe<'b>(&'b mut self, ast: &'b mut Ast, scope: ScopeId) -> Context<'b, 't> {
		Context {
			ast,
			scopes: self.scopes,
			scope,
			tokens: self.tokens,
			resources: self.resources,
			is_meta: self.is_meta,
			folder: self.folder,
			types: self.types,
		}
	}

	fn borrow<'b>(&'b mut self) -> Context<'b, 't> {
		Context {
			ast: self.ast,
			scopes: self.scopes,
			scope: self.scope,
			tokens: self.tokens,
			resources: self.resources,
			is_meta: self.is_meta,
			folder: self.folder,
			types: self.types,
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
			is_meta: self.is_meta,
			folder: self.folder,
			types: self.types,
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
	pub fn new() -> Self {
		Ast { 
			nodes: Vec::new(),
			is_typed: false,
		}
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
	fn new(context: &Context, location: &impl Location, scope: ScopeId, kind: NodeKind) -> Self {
		Node { 
			loc: location.get_location(), 
			kind, 
			scope, 
			is_lvalue: false, 
			is_meta_data: context.is_meta,
			type_: None,
		}
	}
}

impl Location for Node {
	fn get_location(&self) -> CodeLoc {
		self.loc.clone()
	}
}

#[derive(Debug, Clone, Copy)]
pub enum MarkerKind {
	IfCondition(AstNodeId),
	IfElseTrueBody(AstNodeId),
	LoopHead,
}

#[derive(Debug)]
pub enum NodeKind {
	Temporary,
	Marker(MarkerKind),
	MemberAccess(AstNodeId, ustr::Ustr),
	Number(i128),

	IntrinsicTwo(IntrinsicKindTwo),

	EmptyLiteral,
	Identifier
	{
		source: ScopeMemberId, 
		const_members: smallvec::SmallVec<[ustr::Ustr; 3]>,
		is_type: bool,
	},

	BitCast {
		into_type: AstNodeId,
		value: AstNodeId,
	},

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

	Loop(AstNodeId),

	Struct {
		members: Vec<(ustr::Ustr, AstNodeId)>,
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

	HeapClone(AstNodeId),
	StackClone(AstNodeId),

	// Type expressions
	// Type expressions have all their data in their types, and are never turned into bytecode.
	// The 'type' that they have is not the type of the value, but the value itself. I.e.,
	// the type of a TypeIdentifier produced from U64 is U64, as opposed to
	// Identifier from U64 which would be of type Type.
	//
	// GetType makes the type of a typeexpression node into a constant value, to make it
	// usable for other nodes.
	/// Exactly the same as an identifier but it is a type expression.
	TypeFunctionPointer {
		arg_list: Vec<AstNodeId>,
		return_type: Option<AstNodeId>,
	},
	TypeStruct {
		args: Vec<(ustr::Ustr, AstNodeId)>,
	},
	TypePointer(AstNodeId),
	TypeBufferPointer(AstNodeId),
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
		TokenStream { tokens: tokens, index: 0, last_location } 
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
		-> Result<&'a Token, ()> 
	{
		self.tokens.get(self.index).ok_or_else(|| error_value!(self, "{}", message()))
	}

	fn peek_kind(&self) -> Option<&'a TokenKind> {
		self.tokens.get(self.index).map(|v| &v.kind)
	}

	fn next(&mut self) -> Option<&'a Token> {
		self.index += 1;
		self.tokens.get(self.index - 1)
	}

	fn expect_next<'b, D: std::fmt::Display>(&mut self, message: impl FnOnce() -> D) 
		-> Result<&'a Token, ()> 
	{
		self.index += 1;
		self.tokens.get(self.index - 1).ok_or_else(|| error_value!(self, "{}", message()))
	}

	fn next_kind(&mut self) -> Option<&'a TokenKind> {
		self.index += 1;
		self.tokens.get(self.index - 1).map(|v| &v.kind)
	}
}

fn try_parse_create_label(
	context: Context,
) -> Result<Option<ScopeMemberId>, ()> {
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
			_ => {
				return error!(loc, "Expected label name");
			}
		}
	} else {
		Ok(None)
	}
}

fn try_parse_label(
	context: Context,
) -> Result<Option<ScopeMemberId>, ()> {
	if let Some(TokenKind::Colon) = context.tokens.peek_kind() {
		context.tokens.next();
		let loc = context.tokens.get_location();
		match context.tokens.next_kind() {
			Some(TokenKind::Identifier(name)) => {
				let id = context.scopes.find_member(
					context.scope, 
					*name,
				).ok_or_else(|| error_value!(loc, "Unknown label"))?;

				if context.scopes.member(id).kind != ScopeMemberKind::Label {
					return error!(
						loc, 
						"Expected label, got variable or constant"
					);
				}

				Ok(Some(id))
			}
			_ => {
				return error!(loc, "Expected label name");
			}
		}
	} else {
		Ok(None)
	}
}

fn parse_block(mut context: Context, expect_brackets: bool, is_runnable: bool) 
	-> Result<AstNodeId, ()>
{
	let loc = context.tokens.get_location();
	if expect_brackets {
		match context.tokens.next() {
			Some(Token { kind: TokenKind::Bracket('{'), .. }) => (),
			_ => {
				return error!(loc, "Expected '{{' to start block");
			}
		}
	}

	let mut context = context.sub_scope();

	let label = try_parse_create_label(context.borrow())?;

	let mut commands = Vec::new();
	loop {
		match context.tokens.peek() {
			Some(Token { loc, kind: TokenKind::ClosingBracket('}') }) if expect_brackets => {
				commands.push(context.ast.insert_node(Node::new(&context, loc, context.scope, NodeKind::EmptyLiteral)));
				context.tokens.next();
				break;
			}
			None if !expect_brackets => {
				commands.push(context.ast.insert_node(Node::new(&context, context.tokens, context.scope, NodeKind::EmptyLiteral)));
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
					return error!(ident_loc, "This scope is not runnable, so the only thing you can do is declare constants");
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
					Node::new(&context, declare_loc, context.scope, NodeKind::Declaration {
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

				let sub_scope = 
					context.scopes.create_scope_that_is_maybe_thin(Some(context.scope), true);
				let mut sub_context = context.new_stackframe(&mut ast, sub_scope);

				parse_expression(sub_context.borrow())?;

				let resource_id = context.resources.insert(Resource::new_with_scope(
					ident_loc.clone(),
					sub_scope,
					ResourceKind::Value(ResourceValue::Defined(ast)),
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
				return error!(context.tokens, "This scope is not runnable, so the only thing you can do is declare constants");
			}
		}

		let loc = context.tokens.get_location();
		match context.tokens.next() {
			Some(Token { kind: TokenKind::ClosingBracket('}'), .. }) if expect_brackets => break,
			Some(Token { kind: TokenKind::Semicolon, .. }) => (),
			None if !expect_brackets => break,
			_ => {
				return error!(loc, 
					"Expected ';' or '}}', did you forget a semicolon or did you forget an operator?");
			}
		}
	}

	Ok(context.ast.insert_node(Node::new(&context, &loc, context.scope, NodeKind::Block { contents: commands, label } )))
}

fn parse_type_expr_value(
	mut context: Context
) -> Result<AstNodeId, ()> {
	let token = context.tokens.expect_peek(|| "Expected type expression")?;
	match token.kind {
		TokenKind::Operator(Operator::BitAndOrPointer) => {
			context.tokens.next();
			let sub_type = parse_type_expr_value(context.borrow())?;
			Ok(context.ast.insert_node(Node::new(&context, 
				token,
				context.scope, 
				NodeKind::TypePointer(sub_type),
			)))
		}
		TokenKind::Operator(Operator::BufferPointer) => {
			context.tokens.next();
			let sub_type = parse_type_expr_value(context.borrow())?;
			Ok(context.ast.insert_node(Node::new(&context, 
				token,
				context.scope, 
				NodeKind::TypeBufferPointer(sub_type),
			)))
		}
		TokenKind::Identifier(_) => {
			let old_meta = context.is_meta;
			context.is_meta = true;
			let id = parse_identifier(context.borrow(), true)?;
			context.is_meta = old_meta;
			Ok(id)
		}
		TokenKind::Bracket('{') => parse_type_expr_struct(context),
		TokenKind::Bracket('(') => parse_type_expr_function_ptr(context),
		_ => {
			return error!(token, "Expected type expression!");
		}
	}
}

fn parse_identifier(
	context: Context,
	is_type: bool,
) -> Result<AstNodeId, ()> {
	let token = context.tokens.next().unwrap();
	match token.kind {
		TokenKind::Identifier(name) => {
			let member = context.scopes.find_or_create_temp(context.scope, name)?;

			let mut sub_members = smallvec::SmallVec::new();
			while let Some(Token { kind: TokenKind::ConstMember, .. }) = context.tokens.peek() {
				context.tokens.next();
				match context.tokens.next() {
					Some(Token { kind: TokenKind::Identifier(name), .. }) => {
						sub_members.push(*name);
					}
					_ => {
						return error!(context.tokens, "Expected member identifier");
					}
				}
			}

			Ok(context.ast.insert_node(Node::new(&context, token, context.scope, 
				NodeKind::Identifier {
					source: member,
					const_members: sub_members,
					is_type,
				})))
		}
		_ => unreachable!("Only call parse_identifier when you have an identifier"),
	}
}

fn parse_type_expr_struct(
	mut context: Context
) -> Result<AstNodeId, ()> {
	let token = context.tokens.peek().unwrap();
	let (_, args) = try_parse_list(
		context.borrow(),
		|mut context| {
			// TODO: Try to unify named list parsing somehow.
			let value = context.tokens.expect_next(|| "Expected struct member name")?;
			if let Token { loc: _, kind: TokenKind::Identifier(name) } = *value {
				let colon = context.tokens.next();
				if matches!(colon, Some(Token { kind: TokenKind::Colon, .. })) {
					let type_node = parse_type_expr_value(context.borrow())?;

					Ok((name, type_node))
				} else {
					return error!(value, "Expected ':' for struct member type");
				}
			} else {
				return error!(value, "Expected struct member name");
			}
		},
		&TokenKind::Bracket('{'),
		&TokenKind::ClosingBracket('}'),
	)?.ok_or_else(|| error_value!(token, "Expected parameter list"))?;

	
	Ok(context.ast.insert_node(Node::new(&context,
		token,
		context.scope,
		NodeKind::TypeStruct {
			args,
		},
	)))
}

fn parse_type_expr_function_ptr(
	mut context: Context
) -> Result<AstNodeId, ()> {
	// Parse the function arguments.
	let token = context.tokens.peek().unwrap();
	let (_, args) = try_parse_list(
		context.borrow(),
		parse_type_expr_value,
		&TokenKind::Bracket('('),
		&TokenKind::ClosingBracket(')'),
	)?.ok_or_else(|| error_value!(token, "Expected parameter list"))?;

	// Do we have a return type?
	let return_type = if let Some(Token { loc: _, kind: TokenKind::Operator(Operator::Function) }) =
		context.tokens.peek() 
	{
		context.tokens.next();
		Some(parse_type_expr_value(context.borrow())?)
	} else {
		None
	};

	Ok(context.ast.insert_node(Node::new(&context, 
		token, 
		context.scope, 
		NodeKind::TypeFunctionPointer {
			arg_list: args,
			return_type,
		},
	)))
}

fn parse_function(
	mut parent_context: Context
) -> Result<ResourceId, ()> {
	// Lambda definition
	let mut ast = Ast::new();
	let mut args = Vec::new();
	let sub_scope = parent_context.scopes.create_scope(Some(parent_context.scope));

	let mut context = parent_context.new_stackframe(&mut ast, sub_scope);

	let token = context.tokens.peek().expect("Don't call parse_function without a '|' to start");
	if let TokenKind::Operator(Operator::BitwiseOrOrLambda) = token.kind {
		try_parse_list(
			context.borrow(), 
			|mut context| {
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

					let colon = context.tokens.next();
					if matches!(colon, Some(Token { kind: TokenKind::Colon, .. })) {
						let type_node = parse_type_expr_value(context.borrow())?;

						context.ast.insert_node(Node::new(&context, loc, sub_scope, 
							NodeKind::DeclareFunctionArgument {
								variable_name: arg,
								type_node,
							}
						));

						Ok(())
					} else {
						error!(value, "Expected ':' for function argument type")?
					}
				} else {
					error!(value, "Expected function argument name")?
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
		ResourceKind::Function(ResourceFunction::Defined(ast, args)),
	));

	Ok(id)
}

fn parse_expression(
	mut context: Context,
) -> Result<AstNodeId, ()> {
	let token = context.tokens.expect_peek(|| "Expected expression")?;

	// We sometime have special behaviour at the beginning of an expression. For example,
	// type expressions and function declarations can only occur here, at the root of an expression.
	match token.kind {
		TokenKind::Operator(Operator::BitwiseOrOrLambda) 
		| TokenKind::Operator(Operator::Or) => {
			let id = parse_function(context.borrow())?;
			Ok(context.ast.insert_node(Node::new(&context, 
				token, 
				context.scope, 
				NodeKind::Resource(id),
			)))
		}
		TokenKind::Keyword("type") => {
			context.tokens.next();
			let id = parse_type_expr_value(context.borrow())?;
			
			Ok(context.ast.insert_node(Node::new(&context, 
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
) -> Result<AstNodeId, ()> {
	let lvalue_starting_node = context.ast.nodes.len();
	let mut a = parse_value(context.borrow())?;
	
	while let Some(&Token { kind: TokenKind::Operator(operator), ref loc }) = context.tokens.peek() {
		let (priority, _, left_to_right) = operator.data();

		let priority = priority.ok_or_else(
			|| error_value!(loc, "Operator is used as a binary operator, but it's not a binary operator")
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
					Token { kind: TokenKind::Identifier(name), .. } => *name,
					Token { loc, .. } => {
						return error!(loc, "Expected an identifier for the . operator");
					}
				};

				a = context.ast.insert_node(Node::new(&context, 
					loc,
					context.scope,
					NodeKind::MemberAccess(a, identifier),
				));
				continue;
			}

			let b = parse_expression_rec(context.borrow(), priority)?;
			
			a = context.ast.insert_node(Node::new(&context, 
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
) -> Result<AstNodeId, ()> {
	let token = context.tokens.expect_peek(|| "Expected value")?;
	let mut id = match token.kind {
		TokenKind::Operator(Operator::BitwiseOrOrLambda) => {
			return error!(token, "Function declarations can only be the first thing in an expression");
		}
		TokenKind::Operator(operator) => {
			context.tokens.next();
			let (_, unary_priority, _) = operator.data();

			let unary_priority = unary_priority.ok_or_else(
				|| error_value!(token, "Operator is not a unary operator, but it's used as one")
			)?;

			let operand = parse_expression_rec(context.borrow(), unary_priority)?;
			context.ast.insert_node(Node::new(&context, token, context.scope, NodeKind::UnaryOperator { operator, operand }))
		}
		TokenKind::NumericLiteral(number) => {
			context.tokens.next();
			context.ast.insert_node(Node::new(&context, token, context.scope, NodeKind::Number(number)))
		}
		TokenKind::StringLiteral(ref string) => {
			context.tokens.next();

			// TODO: Find a way to get rid of the string cloning here!
			// Possibly by making TokenStream own its data

			let string_bytes = string.as_bytes();
			let n_bytes = string_bytes.len();
			let buffer_id = context.resources.insert_done(Resource::new_with_type(
				token.loc.clone(),
				ResourceKind::Value(ResourceValue::Value(
					context.types.handle(U8_TYPE_ID),
					n_bytes,
					string.as_bytes().into(),
					vec![],
				)),
				U8_TYPE_ID,
			));

			let [a, b, c, d, e, f, g, h] = n_bytes.to_le_bytes();

			let string_type = context.types.insert(Type::new(TypeKind::BufferPointer(U8_TYPE_ID)));
			let id = context.resources.insert_done(
				Resource::new_with_type(
					token.loc.clone(),
					ResourceKind::Value(ResourceValue::Value(
						context.types.handle(string_type),
						1,
						smallvec![0, 0, 0, 0, 0, 0, 0, 0, a, b, c, d, e, f, g, h],
						vec![(0, buffer_id, context.types.handle(U8_TYPE_ID))],
					)),
					string_type,
				)
			);

			context.ast.insert_node(Node::new(&context, token, context.scope, NodeKind::Resource(id)))
		}
		TokenKind::Keyword("heap_clone") => {
			context.tokens.next();

			let id = parse_value(context.borrow())?;

			context.ast.insert_node(
				Node::new(&context, token, context.scope, NodeKind::HeapClone(id))
			)
		}
		TokenKind::Keyword("stack_clone") => {
			context.tokens.next();

			let id = parse_value(context.borrow())?;

			context.ast.insert_node(
				Node::new(&context, token, context.scope, NodeKind::StackClone(id))
			)
		}
		TokenKind::Keyword("struct") => {
			context.tokens.next();
			let (_, members) = try_parse_list(
				context.borrow(),
				|mut context| {
					// TODO: Try to unify named list parsing somehow.
					let value = context.tokens.expect_next(|| "Expected struct member name")?;
					if let Token { loc: _, kind: TokenKind::Identifier(name) } = *value {
						let colon = context.tokens.next();
						if matches!(colon, Some(Token { kind: TokenKind::Colon, .. })) {
							let expression = parse_expression(context.borrow())?;

							Ok((name, expression))
						} else {
							return error!(value, "Expected ':' for struct member");
						}
					} else {
						return error!(value, "Expected struct member name");
					}
				},
				&TokenKind::Bracket('{'),
				&TokenKind::ClosingBracket('}'),
			)?.ok_or_else(|| error_value!(token, "Expected struct members"))?;


			context.ast.insert_node(Node::new(&context,
				token,
				context.scope,
				NodeKind::Struct {
					members,
				},
			))
		}
		TokenKind::Keyword("loop") => {
			context.tokens.next();

			context.ast.insert_node(
				Node::new(&context, token, context.scope, NodeKind::Marker(MarkerKind::LoopHead))
			);
			let body = parse_expression(context.borrow())?;

			context.ast.insert_node(Node::new(&context, token, context.scope,
				NodeKind::Loop(body)
			))
		}
		TokenKind::Keyword("if") => {
			context.tokens.next();

			let condition = parse_expression(context.borrow())?;
			let condition_marker = context.ast.insert_node(Node::new(&context, token, context.scope,
				NodeKind::Marker(MarkerKind::IfCondition(condition))
			));

			let true_body = parse_block(context.borrow(), true, true)?;

			if let Some(TokenKind::Keyword("else")) = context.tokens.peek_kind() {
				context.tokens.next();

				let true_body_marker = context.ast.insert_node(
					Node::new(&context, token, context.scope,
						NodeKind::Marker(MarkerKind::IfElseTrueBody(true_body))
				));

				let false_body = parse_block(context.borrow(), true, true)?;

				let if_statement = context.ast.insert_node(
					Node::new(&context, token, context.scope, NodeKind::IfWithElse {
						condition: condition_marker,
						true_body: true_body_marker,
						false_body: false_body,
					})
				);

				if_statement
			} else {
				let if_statement = context.ast.insert_node(
					Node::new(&context, token, context.scope, NodeKind::If {
						condition: condition_marker,
						body: true_body,
					})
				);

				if_statement
			}
		}
		TokenKind::Keyword("bit_cast") => {
			context.tokens.next();

			let into_type = parse_type_expr_value(context.borrow())?;

			match context.tokens.next() {
				Some(Token { kind: TokenKind::Bracket('('), .. }) => (),
				_ => {
					return error!(context.tokens, "Expected '(' for argument in bit_cast");
				}
			}

			let value = parse_expression(context.borrow())?;

			match context.tokens.next() {
				Some(Token { kind: TokenKind::ClosingBracket(')'), .. }) => (),
				_ => {
					return error!(context.tokens, "Expected ')' for argument in bit_cast");
				}
			}

			context.ast.insert_node(Node::new(&context, 
				token, 
				context.scope, 
				NodeKind::BitCast { into_type, value },
			))
		}
		TokenKind::Identifier(_) => parse_identifier(context.borrow(), false)?,
		TokenKind::Bracket('{') => {
			parse_block(context.borrow(), true, true)?
		}
		TokenKind::Bracket('(') => {
			context.tokens.next();
			let value = parse_expression(context.borrow())?;
			
			match context.tokens.next() {
				Some(Token { kind: TokenKind::ClosingBracket(')'), .. }) => (),
				_ => {
					return error!(&token, "Parenthesis is not closed properly");
				}
			}

			value
		}
		TokenKind::Keyword("import") => {
			context.tokens.next();

			if let Some(Token { kind: TokenKind::StringLiteral(module_name), loc }) 
				= context.tokens.next()
			{
				if module_name.contains('\\') {
					return error!(loc, "Module name cannot contain '\\'");
				}

				let mut file_pos = String::new();
				file_pos.push_str(&context.folder);
				file_pos.push('\\');
				file_pos.push_str(module_name);

				let id = context.resources.insert(Resource::new(
					*loc,
					ResourceKind::Value(ResourceValue::File {
						scope: context.scope,
						module_folder: file_pos.as_str().into(),
						file: file_pos.as_str().into(),
					}),
				));

				context.ast.insert_node(Node::new(&context, 
					token, 
					context.scope, 
					NodeKind::Resource(id),
				))
			} else {
				return error!(context.tokens, "Expected file to import");
			}
		}
		TokenKind::Keyword("skip") => {
			context.tokens.next();

			let loc = context.tokens.get_location();
			let label = try_parse_label(context.borrow())?.ok_or_else(
				|| error_value!(loc, "Expected label ':label_name'")
			)?;

			// There may be some argument to the break
			let value = if let Some(TokenKind::Bracket('(')) = context.tokens.peek_kind() {
				context.tokens.next();
				let value = parse_expression(context.borrow())?;

				let loc = context.tokens.get_location();
				match context.tokens.next_kind() {
					Some(TokenKind::ClosingBracket(')')) => (),
					_ => {
						return error!(loc, "Expected closing ')'");
					}
				}

				Some(value)
			} else {
				None
			};

			context.ast.insert_node(Node::new(&context, token, context.scope, NodeKind::Skip { label, value }))
		}
		_ => {
			return error!(token, "Expected value");
		}
	};

	while let Some((location, arg_list)) = try_parse_list(
		context.borrow(), parse_expression, 
		&TokenKind::Bracket('('), &TokenKind::ClosingBracket(')')
	)? {
		id = context.ast.insert_node(Node::new(&context, &location, context.scope, NodeKind::FunctionCall {
			function_pointer: id,
			arg_list,
		}));
	}

	Ok(id)
}

fn try_parse_list<'t, V>(
	mut context: Context<'_, 't>,
	mut parse_value: 
		impl for <'b> FnMut(Context<'b, 't>) -> Result<V, ()>,
	start_bracket: &TokenKind,
	close_bracket: &TokenKind,
) -> Result<Option<(CodeLoc, Vec<V>)>, ()> {
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
			Some(_) => {
				return error!(next.unwrap(), "Expected ',' to separate items in list");
			}
			None => {
				return error!(location, "List is not closed");
			}
		}
	}

	Ok(Some((location, contents)))
}

pub fn parse_code(
	folder: ustr::Ustr,
	file: ustr::Ustr,
	code: &str,
	resources: &mut Resources,
	scopes: &mut Scopes,
	types: &mut Types,
	scope: ScopeId,
	is_value: bool,
) -> Result<Ast, ()> {
	let (last_loc, tokens) = lex_code(file, code)?;
	let mut ast = Ast::new();

	let mut stream = TokenStream::new(&tokens, last_loc);
	let context = Context {
		ast: &mut ast,
		scopes,
		scope,
		types,
		tokens: &mut stream,
		resources,
		is_meta: false,
		folder,
	};
	parse_block(context, false, is_value)?;

	Ok(ast)
}
