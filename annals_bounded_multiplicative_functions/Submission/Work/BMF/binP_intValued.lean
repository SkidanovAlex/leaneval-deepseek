import Mathlib
import Submission.Work.BMF.intval_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `binP j` is integer-valued on `ℤ`

`binP j = C(X, j) = X(X-1)⋯(X-j+1)/j!` is the `j`-th binomial-coefficient polynomial.  We show
that its values at *all* integers (not merely at naturals) are integers.

The proof goes through the binomial ring structure on `ℤ`: for `n : ℤ` the value `C(n, j)` is the
element `Ring.choose n j` of the binomial ring `ℤ`, and
`descPochhammer_eq_factorial_smul_choose` identifies `n(n-1)⋯(n-j+1) = j! · Ring.choose n j`.
-/

namespace Work.BMF

open Polynomial

theorem binP_intValued (j : ℕ) (n : ℤ) : ∃ m : ℤ, Polynomial.eval (n : ℝ) (Work.BMF.binP j) = (m : ℝ) := by
  refine ⟨Ring.choose n j, ?_⟩
  have hfacR : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have h1 : Polynomial.eval (n : ℝ) (Work.BMF.binP j)
      = (j.factorial : ℝ)⁻¹ * Polynomial.eval (n : ℝ) (descPochhammer ℝ j) := by
    rw [Work.BMF.binP, Polynomial.eval_mul, Polynomial.eval_C]
  rw [h1]
  have h2 := (descPochhammer_eval_cast (R := ℝ) j n).symm
  rw [h2]
  have h3 : eval n (descPochhammer ℤ j) = (j.factorial : ℤ) * Ring.choose n j := by
    rw [eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  rw [h3]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hfacR, one_mul]

end Work.BMF
