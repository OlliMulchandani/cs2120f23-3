/-!
# Propositional Logic: Review and Practice
-/

/-!
## Specification of Propositional Logic

We begin by reproducing our formal specification
of the syntax and semantics of propositional logic,
without distracting implementation alternatives. 
-/

/-!
### Abstract Syntax
-/

structure var : Type := 
(n: Nat)

inductive unary_op : Type
| not

inductive binary_op : Type
| and
| or
| imp
| iff

inductive Expr : Type
| var_exp (v : var)
| un_exp (op : unary_op) (e : Expr)
| bin_exp (op : binary_op) (e1 e2 : Expr)

/-!
### Concrete Syntax
-/

notation "{"v"}" => Expr.var_exp v
prefix:max "¬" => Expr.un_exp unary_op.not 
infixr:35 " ∧ " => Expr.bin_exp binary_op.and  
infixr:30 " ∨ " => Expr.bin_exp binary_op.or 
infixr:25 " ⇒ " =>  Expr.bin_exp binary_op.imp
infixr:20 " ⇔ " => Expr.bin_exp binary_op.iff 

/-!
Semantics
-/

def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not

def implies: Bool → Bool → Bool
| true, false => false
| _, _ => true

def biimplies: Bool → Bool → Bool
| true, true => true
| false, false => true
| _, _ => false

def eval_bin_op : binary_op → (Bool → Bool → Bool)
| binary_op.and => and
| binary_op.or => or
| binary_op.imp => implies
| binary_op.iff => biimplies

def Interp := var → Bool  

def eval_expr : Expr → Interp → Bool 
| (Expr.var_exp v),        i => i v
| (Expr.un_exp op e),      i => (eval_un_op op) (eval_expr e i)
| (Expr.bin_exp op e1 e2), i => (eval_bin_op op) (eval_expr e1 i) (eval_expr e2 i)



/-!
## Review and Practice

### Propositions

A proposition is an expression that asserts that
some *state of affairs* holds in some world, real 
or imaginary. It makes sense to ask whether a given
proposition is true or false in some world.

Here's an example of a proposition: "The red block 
is on top of the blue block." It makes sense to ask,
"Is it true that the red block is on top of the blue
block?" However, to answer thisthe question, we also
have to specify a *world* in which we are to evaluate
it truth or falsity.

For example, imagine two children, say Bob and Sally,
each playing with blocks. We can ask "Is it true that
the red block is on top of the blue block *in Sally's
world?*" We can ask "Is it true that the red block is
on top of the blue block in Bob's world?*" And we may
well get different answers. We evaluate the truth of 
a proposition in a specified world.

### Propositional Logic

There are many different logics. Each provides a
*language* of propositions, different kinds of worlds,
and formal methods for assessing the truth of a given 
proposition in a given world.

Propositional logic is an especially simple logic.
It provides a language of *atomic propositions* and
of larger propositions formed by combining smaller
ones using the not (¬), and (∧), or (∨), implies
(⇒), and equivalence (↔) connectives.

### Variables Represent Atomic Propositions

In propositional logic, one represents an atomic 
proposition as using a variable name. For example,
one could represent the atomic proposition, *The 
red block is on top of the blue block* using the
variable, *red_block_on_blue_block*. Similarly,
one could represent the atomic proposition, *The
yellow block is on the red block" using the rather
verbose variable *yellow_block_on_red_block*. 

### Larger Propositions Are Built Using Connectives

We could then write the larger proposition, *The red
block is on the blue block *and* the yellow block
is on the red block* as *red_block_on_blue_block
∧ yellow_block_on_red_block*. More generally, we
can form larger propositions by applying logical
*connectives* such as ¬, ∧, and ∨, each to the
correct number of smaller propositions, ending
at atomic propositions.  

### Abstracting to Short Variable Names

However, using long and expressive variable names
makes larger propositions hard to write and read. 
The usual practice, then is to use single character 
variable names to represent atomic propositions. 

Here for example we might just use *r* to represent 
the *red on blue* proposition and *y* to represent
the *yellow on red* proposition. Now we can write 
the concise, formal expression, *r ∧ y*, to stand
for the proposition that *The red block is on the 
blue block *and* the yellow block is on the red 
block*. In practice one could provide a translation
table linking short, formal propositional variable
names to their intended meanings expressed in a
natural language. 

| variable |      intended meaning        |
|----------|------------------------------|
|    r     |  red block is on blue block  |
|    y     | yellow block is on red block |

### Abstracting from Real-World Meanings 

The underlying purpose of a logic is to provide a
way to express propositions in such a way that we
can then reason about their truth or falsity without
further reference to the real or imaginary worlds
that their variables refer to. We translate natural
thoughts into mathematical representations then use
the mathematics to reason further, translating the
final results back into natural world meanings only
at the end of the process.

### Validity and Unsatisfiability

Furthermore, when studying logic, we are often 
interested in whether a given proposition in true
or false *independent of the meanings of its parts*.
For example, in propositional logic, the proposition,
*r ∧ ¬r* cannot be true no matter what natural language
proposition *r* means, as a proposition cannot be true 
and false. We call such a proposition *unsatisfiable.*

Similarly, the proposition, *r ∨ ¬r* is always true
in propositional logic, as a proposition can *only*
be true or false, and in either case one of the two
sub-expressions will be true, so the overall one will
be true as well. We call such a proposition *valid*.

For numerous reasons, then, we'll usually use single
letters to represent (natural language) propositions,
and moreover, we'll often do so without referring to
any particular natural language translations. That is,
we'll study logic *in the abstract*. 


## HOMEWORK: 

Refer to each of the problems in HW5, Part 1. 
For each one, express the proposition that each function
type represents using our formal notation for propositional
logic. We'll take you through this exercise in steps. 
-/

/-!
### #1. Propositional Variables

First, define *b, c,* *j,* and *a* as propositional variables
(of type *var*). We'll use *b* for *bread* or *beta*,* *c* for 
*cheese,* *j* for *jam,* and *a* for α*. 
-/

def b := var.mk 0
def j := var.mk 1
def c := var.mk 2
def a := var.mk 3

-- get the index out of the c structure
#eval c.n
#eval var.n c


/-!
### #2. Atomic Propositions

Define B, C, J and A as corresponding atomic propositions,
of type *Expr*. 
-/

def B := {b}     
def C := {c}
def J := {j}
def A := {a}

/-!
### #3. Compound Propositions

Now define the variables, e0 through e3, as expressions
in propositional logic using the concrete syntax we've 
defined.
-/

-- #1. ((no jam) ⊕ (no cheese)) → (no (jam × cheese)) 
def e0 := (¬J ∨ ¬C) ⇒ ¬(J ∧ C)

-- YOU DO THE REST

--((α → Empty) ⊕ (β → Empty)) → (α × β → Empty)  
def e1 := (¬A ∨ ¬B) ⇒ ¬(A ∧ B)

--(α ⊕ β → Empty) → ((α → Empty) × (β → Empty))
def e2 := ¬(A ∨ B) ⇒ (¬A ∧ ¬B)

--((α → Empty) × (β → Empty)) → ((α ⊕ β) → Empty)  
def e3 := (¬A ∧ ¬B) ⇒ ¬(A ∨ B)


/-!
### #4. Implement Syntax and Semantics for Implies and Biimplication
Next go back and extend our formalism to support the implies connective.
Do the same for biimplication while you're at it. This is already done 
for *implies*. Your job is to do the same for bi-implication, which
Lean does not implement natively. 
-/

-- ⇔

/-!
### #5. Evaluate Propositions in Various Worlds

Now evaluate each of these expressions under the all_true and all_false
interpretations. These are just two of the possible interpretations so
we won't have complete proofs of validity, but at least we expect them
to evaluate to true under both the all_true and all_false interpretations.
-/

#eval eval_expr e0 (λ _ => false) -- expect true
#eval eval_expr e0 (λ _ => true)  -- expect true

#eval eval_expr e1 (λ _ => false) -- expect true
#eval eval_expr e1 (λ _ => true)  -- expect true

#eval eval_expr e2 (λ _ => false) -- expect true
#eval eval_expr e2 (λ _ => true)  -- expect true

#eval eval_expr e3 (λ _ => false) -- expect true
#eval eval_expr e3 (λ _ => true)  -- expect true



/-!
### #6. Evaluate the Expressions Under Some Other Interpretation

Other than these two, evaluate the propositions under your new
interpretation, and confirm that they still evaluate to true.
Your interpretation should assign various true and false values
to *j, c, b,* and *a.* An interpretation has to give values to
all (infinitely many) variables. You can do case analysis by
pattern matching on a few specific variables (by index) then 
use wildcard matching to handle all remaining cases.
-/

-- Answer here

def my_interp : var → Bool
| var.mk 0 => true
| var.mk 1 => false
| var.mk 2 => true
| var.mk 3 => false
| _ => false


#eval eval_expr e0 my_interp -- expect true
#eval eval_expr e1 my_interp  -- expect true
#eval eval_expr e2 my_interp  -- expect true
#eval eval_expr e3 my_interp  -- expect true