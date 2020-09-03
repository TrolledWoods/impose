macro_rules! create_operators {
	($($name:ident; $token:expr, $left_to_right:expr, $priority:expr, $unary_priority:expr),*,) => {
		pub const OPERATORS: &[(&str, Operator)] = &[
			$(($token, Operator::$name)),*
		];

		#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
		pub enum Operator { $($name),* }

		impl Operator {
			pub fn data(&self) -> (Option<u32>, Option<u32>, bool) {
				match self {
					$(
						Operator::$name => (
							if $priority == 0 { None } else { Some($priority) }, 
							if $unary_priority == 0 { None } else { Some($unary_priority) },
							$left_to_right
						)
					),*
				}
			}
		}
	}
}

// TODO: Maybe separate unary and binary operators? This would require the operator enum to be
// engaged in the parsing stage and not here, but that might be fine? Not sure....
// Name; Token, LeftToRight, Binary Priority(0 if not binary), Unary Priority(0 if not unary)
create_operators! {
	// Boolean comparisons
	Equ ;       "==",  true,   5, 0,
	NEqu;       "!=",  true,   5, 0,
	LessEqu;    "<=" , true,   5, 0,
	GreaterEqu; ">=" , true,   5, 0,
	Less;       "<" ,  true,   5, 0,
	Greater;    ">" ,  true,   5, 0,
	Not;        "!" ,  true,   0, u32::MAX,

	// Assignment and declaration
	Declare;    ":=",  false,  3, 0,
	Function;   "->",  false,  2, 0,
	Assign;     "=",   false,  3, 0,

	// Boolean operators 
	// TODO: Make these different priorities, people are probably used to and having a lower priority
	And;        "&&",  true,   4, 0,
	Or ;        "||",  true,   4, 0,

	// Bitwise operators
	BitwiseOrOrLambda; "|", true, 5, 0,

	// Standard math operators
	Add;        "+",   true,   6, 0,
	Sub;        "-",   true,   6, 0,

	MulOrDeref; "*",   true,   7, 8,
	Div;        "/",   true,   7, 0,
	Mod;        "%",   true,   7, 0,

	// Special operators that are cool
	Member;     ".",   true,   9, 0,
}
