def override : Interp → var → Bool → Interp
| old_interp, var, new_val => 
  (λ v => if (v.n == var.n)     -- when applied to var
          then new_val          -- return new value
          else old_interp v)  -- else retur old value

def v₀ := var.mk 0
def v₁ := var.mk 1
def v₂ := var.mk 2

def all_false : Interp := λ _ => false

#eval all_false v₀  -- expect false
#eval all_false v₁  -- expect false
#eval all_false v₂  -- expect false