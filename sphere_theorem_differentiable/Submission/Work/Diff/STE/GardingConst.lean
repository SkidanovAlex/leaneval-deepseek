import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The explicit, coefficient-independent Gårding constant

For the elliptic-operator Gårding estimate on the flat torus with ellipticity constant `lam` and
first-derivative bound `K₁` on the coefficient matrix, the constant produced by
`Work.Diff.STE.garding_estimate` is

  `C = max K₁ 0 * n ^ 2 * (max K₁ 0 * n + 1) / (2 * lam)`,   `n = card ι`,

i.e. it depends on the coefficient matrix `A` only through `lam`, `K₁` and the number of
coordinates.  This file records that explicit constant (and its nonnegativity) so that the
Gårding estimate can be stated with a constant that is *uniform in the coefficient matrix*; see
`Work.Diff.STE.ga_const_bound` (the scalar estimate with this explicit constant) and
`Work.Diff.STE.garding_vec_uniform` (the multi-index version).
-/

namespace Work.Diff.STE

/-- The explicit Gårding constant: uniform in the coefficient matrix, depending only on the
number of coordinates `n`, the ellipticity constant `lam` and the first-derivative bound `K₁`. -/
noncomputable def gardingConst (n : ℕ) (lam K₁ : ℝ) : ℝ :=
  max K₁ 0 * (n : ℝ) ^ 2 * (max K₁ 0 * (n : ℝ) + 1) / (2 * lam)

/-- The explicit Gårding constant is nonnegative for positive `lam`. -/
lemma gardingConst_nonneg {n : ℕ} {lam K₁ : ℝ} (hlam : 0 < lam) :
    0 ≤ gardingConst n lam K₁ := by
  rw [gardingConst]
  have hK : 0 ≤ max K₁ 0 := le_max_right _ _
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hD : 0 ≤ max K₁ 0 * (n : ℝ) + 1 := by linarith [mul_nonneg hK hn]
  have hnum : 0 ≤ max K₁ 0 * (n : ℝ) ^ 2 * (max K₁ 0 * (n : ℝ) + 1) :=
    mul_nonneg (mul_nonneg hK (sq_nonneg _)) hD
  exact div_nonneg hnum (by linarith)

end Work.Diff.STE
