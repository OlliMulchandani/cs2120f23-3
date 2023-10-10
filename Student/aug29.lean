#check (String → String) → String → String

def crazy (f: String → String) (a : String) : String := (f a) --body of function to right of ":=", in this case just an application term
--def function_name (argument_name : argument_type) (argument2_name : argument2_type) : return_type := body_of_function
-- f could be append "Hello", a could be "Lean", crazy applies append "Hello" to Lean and evaluates to/returns "Hello Lean"

def crazy2 : (String → String) → String → String
| f, a → (f a)
--first argument (which is a function) passed gets assigned to f, second gets assigned to a, they will always be sequentially assigned if it is undefined
--unless if you used defined values, then Lean will pattern match (if, then, else)
--as seen here:

def xor : Bool → Bool → Bool
| true, true => false
| true, false => true
| false, true => true
| false, false => false

#check xor false

def id_nat: Nat → Nat
| n => n

def id_bool: Bool → Bool
| true => true
| false => false

def id_bool2 (b : Bool) : Bool := b

def id_string: String → String
| s => s

def polymorphic_id (T : Type) : T → T:
| t, v => v

#eval polymorphic_id Bool true
