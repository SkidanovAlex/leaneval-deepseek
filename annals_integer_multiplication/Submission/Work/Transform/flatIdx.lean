import Mathlib
import Submission.Work.Transform.Defs

/-!
# The flat index `(a,c) ↦ a*r + c` for `Fin (ts'.prod) → Fin r → ·`

Paper Prop 3.5 identifies the flat index of `⊗ᵢ C̃tᵢ` with the pair (multi-index of the first
`d-1` axes, last-axis index).  `flatIdx ts' r a c` is the element of `Fin ((ts' ++ [r]).prod)`
with value `a * r + c`; its value, quotient and remainder are the ones used to rewrite
`digits`, `subIdx`, `phiArrL` and `psiFlatL`.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- The flat index `(a,c) ↦ a * r + c` of the pair `(a : Fin ts'.prod, c : Fin r)`. -/
def flatIdx (ts' : List ℕ) (r : ℕ) (a : Fin ts'.prod) (c : Fin r) : Fin ((ts' ++ [r]).prod) :=
  ⟨(a : ℕ) * r + (c : ℕ), by
    have h1 : (a : ℕ) * r + (c : ℕ) < ((a : ℕ) + 1) * r := by
      rw [Nat.succ_mul]; exact Nat.add_lt_add_left c.isLt _
    have h2 : ((a : ℕ) + 1) * r ≤ ts'.prod * r :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt a.isLt)
    have h3 : ts'.prod * r = (ts' ++ [r]).prod := by simp
    omega⟩

@[simp] lemma flatIdx_val (ts' : List ℕ) (r : ℕ) (a : Fin ts'.prod) (c : Fin r) :
    (flatIdx ts' r a c : ℕ) = (a : ℕ) * r + (c : ℕ) := rfl

lemma flatIdx_div (ts' : List ℕ) (r : ℕ) (hr : 0 < r) (a : Fin ts'.prod) (c : Fin r) :
    (flatIdx ts' r a c : ℕ) / r = (a : ℕ) := by
  rw [flatIdx_val, Nat.mul_comm (a:ℕ) r, Nat.mul_add_div hr, Nat.div_eq_of_lt c.isLt,
    Nat.add_zero]

lemma flatIdx_mod (ts' : List ℕ) (r : ℕ) (hr : 0 < r) (a : Fin ts'.prod) (c : Fin r) :
    (flatIdx ts' r a c : ℕ) % r = (c : ℕ) := by
  rw [flatIdx_val, Nat.mul_comm (a:ℕ) r, Nat.mul_add_mod, Nat.mod_eq_of_lt c.isLt]

end Work.Transform
