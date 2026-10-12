import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Integral

open MeasureTheory Set
open scoped BigOperators

/-- **The linear change of variables along the Euclidean norm**: for `a > 0`,
`∫_{ℝⁿ} F(a·‖u‖) du = a^{-n} ∫_{ℝⁿ} F(‖q‖) dq`, where `‖u‖` is the
**Euclidean** norm `√(Σ_j u_j²)` (NOT the product/Pi sup norm) and `volume` is
the product Lebesgue measure on `Fin n → ℝ`.  (Substitute `q = a • u`; the
Jacobian of `u ↦ a • u` is `a^n`, `a > 0`.) -/
theorem integral_comp_smul_euclidean {n : ℕ} {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hint : Integrable (fun u : Fin n → ℝ => F (a * Real.sqrt (∑ i, (u i) ^ 2)))
      volume) :
    ∫ u : Fin n → ℝ, F (a * Real.sqrt (∑ i, (u i) ^ 2))
      = ((a ^ n))⁻¹ * ∫ q : Fin n → ℝ, F (Real.sqrt (∑ i, (q i) ^ 2)) := by
  have _ := hint
  have hsqrt : ∀ u : Fin n → ℝ,
      Real.sqrt (∑ i, ((a • u) i) ^ 2) = a * Real.sqrt (∑ i, (u i) ^ 2) := by
    intro u
    have h1 : ∑ i, ((a • u) i) ^ 2 = a ^ 2 * ∑ i, (u i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [h1, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  have hcomp : (fun u : Fin n → ℝ => F (a * Real.sqrt (∑ i, (u i) ^ 2)))
      = fun u : Fin n → ℝ =>
          (fun q : Fin n → ℝ => F (Real.sqrt (∑ i, (q i) ^ 2))) (a • u) := by
    funext u
    show F (a * Real.sqrt (∑ i, (u i) ^ 2))
      = F (Real.sqrt (∑ i, ((a • u) i) ^ 2))
    rw [hsqrt u]
  rw [hcomp]
  have key := MeasureTheory.Measure.integral_comp_smul_of_nonneg
    (volume : Measure (Fin n → ℝ))
    (fun q : Fin n → ℝ => F (Real.sqrt (∑ i, (q i) ^ 2))) (R := a) (hR := ha.le)
  rw [key, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, smul_eq_mul]

end Commons.Analysis.Integral