axiom em : ∀ (P : Prop), P ∨ ¬P

example (A B : Prop) : ¬(A ∧ B) -> ¬A ∨ ¬B :=
λ (nab) =>
let aornota := em A
let bornotb := em B
match aornota, bornotb with
| Or.inl a, Or.inl b => nomatch nab ⟨a, b⟩
| Or.inl a, Or.inr nb => Or.inr nb
| Or.inr na, Or.inl b => Or.inl na
| Or.inr na, Or.inr nb => Or.inl na -- could also do Or.inr nb
