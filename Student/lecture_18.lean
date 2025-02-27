import Mathlib.Init.Set

/-!
## Predicates

You've seen that in predicate logic, a proposition is a
declarative statement that asserts that some state of affairs
holds in some domain of discourse. For example, *the natural
number, four, is an even* is a proposition. We've seen one
way to formalize such a proposition using the mod operator.
-/

#check 4 % 2 = 0

/-!
### Families of Propositions

Indeed, there is an infinite family of propositions, all just
like this one except for the particular number we plug in instead
of four. As another example, *the natural number, five, is even*
is also a proposition. And there's one such proposition for each
and every natural number.

We can write this family of propositions by *abstracting* the value,
four, to a variable: e.g., *the natural number, n, is even*, where
*n* can be any natural number. Now we have a predicate. Applying it
to a specific number then returns a proposition about that number.

We could say that applying the predicate, *the natural number, n,
is even*, to the specific number, four, returns the *proposition*,
*the natural number, four, is even.*

In Lean and related logics, we represent a predicate as a
*function:* from one or more parameter values to propositions.
Here's our simple example reformulated.
-/

def is_even : Nat → Prop := λ n => n % 2 = 0

/-!
You can see that is_even is a predicate by checking its type.
Indeed, it's a function from a natural number to a proposition
*about* that number: namely that the given number mod two is
zero. The type of our predicate is thus *Nat → Prop*.
-/
#check (is_even)      -- Nat → Prop

/-!
### Applying a Predicate to Arguments Yields a Proposition

Given a predicate we derive a proposition by *applying* it to one
or more arguments of the specified types. The *is_even* predicate
is appliable to a natural number as an argument. Here are two examples
applying the is_even predicate.
-/

#check is_even 4
#check is_even 5
/-!
Note that Lean reduced n%2 in each case to 0 or 1, leaving us
with simpler propositions involving just 0 and 1.
-/

/-!
### To Satisfy a Predicate
We will say that specific parameter values *satisfy* a predicate
if they yield a proposition that is true. In a sense, a proposition
thus specifies a *property* (such as that of being even) that a value
might or might not have. For example, four has the property of being
even but five doesn't.

"4 (an argument) satisfies the is_even predicate"

### Predicates Specify Properties

In this way a predicate picks out the subset of parameter values with
a specified *property*. As an example, we can make a list of natural
numbers from 0 to 5, apply *is_even* to each, determine which resulting
propositions are true, and thus *pick out* the natural numbers with the
property of being even.
-/

#reduce is_even 0   -- ✓
#reduce is_even 1   -- ×
#reduce is_even 2   -- ✓
#reduce is_even 3   -- ×
#reduce is_even 4   -- ✓
#reduce is_even 5   -- ×

/-!
Indeed, as we'll see in more depth shortly, we can understand
the *set* of all objects having a particular property as those
objects that satisfy the predicate that specifies the property.
In Lean, we can specify the set of even numbers as follows, and
*evens* here becomes nothing but a shorthand for is_even. We'll
see more of this top when we get to lectures on set theory.
-/

def evens : Set Nat := { n | is_even n } -- the set of objects n such that n is even, not a datatype, just a predicate
#reduce evens 4
#reduce evens 5
--#reduce evens

/-!
### Predicates of Multiple Arguments

Predicates can take any number of arguments. Here are some examples.
-/

/-!
#### Ordered pairs of numbers and their squares
-/

def square_pair : Nat × Nat → Prop
| (n1, n2) => n2 = n1^2

#reduce square_pair (1, 1)   -- ✓
#reduce square_pair (2, 4)   -- ✓
#reduce square_pair (3, 9)   -- ✓
#reduce square_pair (5, 20)  -- ×

def square_pairs : Set (Nat × Nat) := { p : Nat × Nat | square_pair (p.1, p.2) }
#reduce square_pairs (3,9)
#reduce (3, 9) ∈ square_pairs -- a proposition that this argument satisfies this predicate. it is a member of this set

/-!
#### Pythagorean triples
-/

def pythagorean_triple : Nat → Nat → Nat → Prop
| h, x, y => h^2 = x^2 + y^2


def pythagorean_triples : Set (Nat × Nat × Nat) := { t | t.1^2 = t.2.1^2 + t.2.2^2}
#reduce pythagorean_triples (5,4,3)

/-!
### Exercises

- Write a predicate for the property of being an even-length string
- Write an expression for the set of all even length strings
-/

def ev_len (s : String) : Prop := is_even (s.length)
#reduce ev_len "Hello"
def ev_len_strs : Set String := {s | ev_len s}


def one_and_two : Set Nat := { n | n = 1 ∨ n = 2}
#reduce 3 ∈ one_and_two

/-!
## Quantifiers

Quantifiers are part of the syntax of predicate logic. They allow one
to assert that every object (∀) of some type has some property, or that
there exists (∃) (there is) at least one object of a given type with a
specified property. The syntax of such propositions is as follows:

- ∀ (x : T), P x -- every object x of type T satisfies predicate P
- ∃ (x : T), P x -- there exists at least one object x of type T that satisfies predicate P

Every dog is friendly
∀ (d : Dog), Friendly d

Everyone loves everyone
∀ (p q : Person), Loves p q

Everyone loves someone
∀ (p : Person), ∃ (q : Person), Loves p q

### Universal Quantification

The first proposition can be read as asserting that every value *x* of
type *T* satisfies predicate *P*. Another way to say this is that for
every *x* there is a proof of the proposition, *P x*. Another way to
say that is that there's a function that when given any *x* returns a
proof of *P x*. Indeed, that's how we prove such a proposition: show
that if given any *x* you can produce and return a proof of *P x*.
-/

/-!
### ∀ (for all)
-/
def zornz (n : Nat) : n = 0 ∨ n ≠ 0 :=
match n with
  | 0       => Or.inl rfl   -- proves an equality
  | n' + 1  => Or.inr (fun _ => nomatch n')

/-!
### ∃ (there exists)
-/

def sl5 : ∃ (s : String), s.length = 5 := ⟨"Hello", rfl ⟩

--L∃∀N

/-!
## Homework

(1) Define a predicate, ev_len_str, expressing the property
of a string of being of an even-length.
-/

-- Here
def ev_len_str : String → Prop := λ s => s.length % 2 = 0

/-
(2) Use #check to typecheck an expression for the set of all
even length strings.
-/

-- Here
#check {s : String | s.length % 2 = 0}
#check {s : String | ev_len_str s}

/-
(3) Define a predicate, str_eq_len, applicable to any
String value, s, and to any Nat value, n, that is satisfied
just in those cases where s.length equals n.
-/

-- Here
def str_eq_len : String → Nat → Prop
| s, n => s.length = n




/-
(4) Define str_eq_lens : set String × Nat, to be the *set*
of all ordered pairs, p = ⟨ s, n ⟩, such that n = s.length.
-/

-- Here
def str_eq_lens : Set (String × Nat) := {p | p.1.length = p.2}


/-
(5) Use "example" in Lean to state and prove the proposition
that ⟨ "I love Logic!", 13 ⟩ ∈ str_eq_lens.
-/

-- Here
example : Prop := ⟨ "I love Logic!", 13 ⟩ ∈ str_eq_lens
example : ⟨ "I love Logic!", 13 ⟩ ∈ str_eq_lens := rfl


/-
(6) Use "example" in Lean again to state and prove that
⟨ "I love Logic!", 1 ⟩ ∉ str_eq_lens. That's shorthand
notation for ¬("I love Logic!", 1⟩ ∈ str_eq_lens. And you
know what that means.
-/

-- Here

axiom em : ∀ (P : Prop), P ∨ ¬P

example : ¬⟨"I love Logic!", 1⟩ ∈ str_eq_lens :=
let prop := em (⟨"I love Logic!", 1⟩ ∈ str_eq_lens)
match prop with
| Or.inl is => nomatch is
| Or.inr isnt => isnt


example : ⟨"I love Logic!", 1⟩ ∉ str_eq_lens :=
λ (t : ⟨"I love Logic!", 1⟩ ∈ str_eq_lens) => nomatch t
