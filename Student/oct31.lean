
-- inductive Empty : Type

inductive Chaos : Type

def from_empty (e : Empty) : Chaos := nomatch e

#check Empty
#check False -- uninhabited Prop, no proofs

def from_false {P : Prop} (p : False) : P := False.elim p
-- False.elim is the equivalent of nomatch for Prop universe
-- If you have a contradiction then anything goes, if false exists (it doesn't) then we can prove anything

def from_false_true_is_false (p : False) : True = False := False.elim p

#check from_false_true_is_false



-- Unit type has one value
-- True has one proof, Prop version of Unit
#check True
#check True.intro -- proof of true
-- no elimination rule, it's fairly useless

def proof_of_true : True := True.intro

def false_implies_true : False → True := λ f => False.elim f
def false_implies_true' : False → True := λ f => True.intro

-- Prod is a conjunction, a polymorphic type
#check Prod
#check And -- takes two propositions as arguments and returns a proposition

-- The constructors for both
#check Prod.mk -- α × β
#check And.intro -- a ∧ b

inductive Birds_chirping : Prop
| yep
| boo -- are these constructors (proofs) equal?


inductive Sky_blue : Prop
| yep

#check (And Birds_chirping Sky_blue)

theorem both_and : And Birds_chirping Sky_blue := And.intro Birds_chirping.yep Sky_blue.yep
#check both_and

theorem proof_equal : Birds_chirping.boo = Birds_chirping.yep := by trivial

-- In Prop all proofs are equivalent
-- Choice of values in Prop can't influence computations


-- Sum contains one of two types ==> Or
#check Sum.inl
#check Or.inl -- polymorphic in the propositions in connects together

theorem one_or_other : Or Birds_chirping Sky_blue := Or.inl Birds_chirping.yep

example : Or Birds_chirping (0=1) := Or.inl Birds_chirping.yep
example : (0=1) ∨ (1=2) := _ -- false proposition, no proof exists

theorem or_comm {P Q : Prop} : P ∨ Q → Q ∨ P := -- proving that or is commutative
λ d => -- d for disjunction, our P ∨ Q proposition
  match d with -- d can be crafted one of two ways
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q -- if it's made either way, we return it backwards


-- We called Not no
def no (α : Type) := α → Empty

#check Not -- Not P is defined to be P → False

example : no Chaos := λ c => nomatch c -- c is of type Chaos, which is uninhabited, so nomatch appplies
example : Not False := λ f => False.elim f

inductive Raining : Prop -- uninhabited Prop

example : Not Raining := λ r => nomatch r
