macro_rules! create_operators {
	($($name:ident; $token:expr, $left_to_right:expr, $priority:expr),*,) => {
		pub const OPERATORS: &[(&str, Operator)] = &[
			$(($token, Operator::$name)),*
		];

		#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
		pub enum Operator { $($name),* }

		impl Operator {
			pub fn data(&self) -> (u32, bool) {
				match self {
					$(
						Operator::$name => ($priority, $left_to_right)
					),*
				}
			}
		}
	}
}

// Name; Token, LeftToRight, Priority
create_operators! {
	// Boolean comparisons
	Equ ;       "==", true, 5,
	NEqu;       "!=", true, 5,
	LessEqu;    "<=" , true, 5,
	GreaterEqu; ">=" , true, 5,
	Less;       "<" , true, 5,
	Greater;    ">" , true, 5,

	// Assignment and declaration
	Declare; ":=", false, 3,
	Assign;  "=", false, 3,

	// Boolean operators
	And; "&&", true, 4,
	Or ; "||", true, 4,

	Add; "+", true, 6,
	Sub; "-", true, 6,

	Mul; "*", true, 7,
	Div; "/", true, 7,
	Mod; "%", true, 7,
}
