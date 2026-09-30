import Mathlib
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.card_multIdx

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The cardinality of the equation-index set: `|s| ≤ S` and `t₀ + ∑ t ≤ T`, i.e.
`(2S+1) · (T+r choose r)`. -/
theorem card_AuxEqnIdx (r S T : ℕ) (hr : 1 ≤ r) :
    Fintype.card (AuxEqnIdx r S T) = (2 * S + 1) * (T + r).choose r := by
  rw [Fintype.card_prod, card_multIdx r T hr, Fintype.card_coe, Int.card_Icc]
  congr 1
  omega

/-- `(T+r choose r) · r! ≤ (T+r)^r`: the falling factorial `(T+r)(T+r-1)···(T+1)` has `r`
factors, each at most `T+r`. -/
theorem choose_mul_factorial_le_pow (r T : ℕ) :
    ((T + r).choose r : ℝ) * (r.factorial : ℝ) ≤ (((T + r : ℕ) : ℝ)) ^ r := by
  have h2 : (T + r).descFactorial r ≤ (T + r) ^ r := Nat.descFactorial_le_pow _ _
  have h3 : ((T + r).descFactorial r : ℕ) = r.factorial * (T + r).choose r :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have h4 : (((T + r).descFactorial r : ℕ) : ℝ) ≤ (((T + r) ^ r : ℕ) : ℝ) := by
    exact_mod_cast h2
  calc ((T + r).choose r : ℝ) * (r.factorial : ℝ)
      = (((T + r).descFactorial r : ℕ) : ℝ) := by rw [h3]; push_cast; ring
    _ ≤ (((T + r) ^ r : ℕ) : ℝ) := h4
    _ = (((T + r : ℕ) : ℝ)) ^ r := by push_cast; ring

theorem card_AuxEqnIdx_mul_factorial_le (r S T : ℕ) (hr : 1 ≤ r) :
    (Fintype.card (AuxEqnIdx r S T) : ℝ) * (r.factorial : ℝ)
      ≤ ((2 * S + 1 : ℕ) : ℝ) * ((T : ℝ) + (r : ℝ)) ^ r := by
  rw [card_AuxEqnIdx r S T hr]
  calc ((2 * S + 1) * (T + r).choose r : ℕ) * r.factorial
      = ((2 * S + 1 : ℕ) : ℝ) * (((T + r).choose r : ℝ) * (r.factorial : ℝ)) := by
        push_cast; ring
    _ ≤ ((2 * S + 1 : ℕ) : ℝ) * ((((T + r : ℕ) : ℝ)) ^ r) :=
        mul_le_mul_of_nonneg_left (choose_mul_factorial_le_pow r T) (by positivity)
    _ = ((2 * S + 1 : ℕ) : ℝ) * ((T : ℝ) + (r : ℝ)) ^ r := by push_cast; ring

end Work.BW
