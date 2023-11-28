/-!
Homework: Due Tuesday before class: Formalize the following logical arguments.
Hint: use the variable command to introduce assumed types and such, as we did in class.
Use #check to express the informal propositions that follow in the formal logic of Lean.

1. Every dog likes some cat.

2. If any dog, d, likes any dog, g, and that dog, g, likes any dog, w, then d likes w.

3. If any cat, c, likes any cat, d, then d also likes c.

4. Every cat, c, likes itself.

5. If every cat likes every other cat, and c and d are cats, then c likes d.

Finally, give a formal proof in Lean of the proposition in problem #5.

-/

variable
 (Cat : Type)
 (Dog : Type)
 (Likes_dc : Dog → Cat → Prop)
 (Likes_dd : Dog → Dog → Prop)
 (Likes_cc : Cat → Cat → Prop)

-- 1
#check ∀ (everydog : Dog), ∃ (somecat : Cat), Likes_dc everydog somecat

-- 2
--#check (∃ (d : Dog), ∃ (g : Dog), Likes_dd d g) ∧ () →
--#check (∃ (d : Dog), ∃ (g : Dog), ∃ (w : Dog),  (Likes_dd d g ∧ Likes_dd g w) → (Likes_dd d w))
#check (∀ (d g w : Dog),  (Likes_dd d g ∧ Likes_dd g w) → (Likes_dd d w))

-- 3
#check ∀ (c : Cat), ∀ (d : Cat), Likes_cc c d → Likes_cc d c

-- 4
#check ∀ (c : Cat), Likes_cc c c

-- 5
#check ∃ (c d : Cat), (∀ (everycat everyothercat: Cat), Likes_cc everycat everyothercat) → Likes_cc c d

example : (∃ (c d : Cat), (∀ (everycat everyothercat: Cat), Likes_cc everycat everyothercat)) → Likes_cc c d
| ⟨ _, ⟨ _, everycat_likes_everyothercat⟩ ⟩ => (everycat_likes_everyothercat c d)
