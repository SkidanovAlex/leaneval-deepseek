import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped ENNReal

/-- **Squared Cauchy–Schwarz / Hölder with `p = q = 2` for `ℝ≥0∞`-valued lintegrals.**
For a.e.-measurable `f g : α → ℝ≥0∞`,

    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * (∫⁻ a, g a ^ 2 ∂μ).

This is `ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2`, both sides squared
(the half-powers `(x ^ (2 : ℝ)) ^ (1 / 2)` collapse back to `x` by
`ENNReal.rpow_inv_natCast_pow`, which also covers `x = 0` and `x = ⊤`). -/
private lemma sq_lintegral_mul_le_aux {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * (∫⁻ a, g a ^ 2 ∂μ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  refine (pow_le_pow_left' h 2).trans (le_of_eq ?_)
  rw [mul_pow, show (1 : ℝ) / 2 = ((2 : ℕ) : ℝ)⁻¹ by norm_num,
    ENNReal.rpow_inv_natCast_pow (show (2 : ℕ) ≠ 0 by norm_num),
    ENNReal.rpow_inv_natCast_pow (show (2 : ℕ) ≠ 0 by norm_num)]
  simp

/-- **Cauchy–Schwarz for the Bochner integral of a conjugate product of complex functions,**
in `enorm` (`ℝ≥0∞`-valued) form:

    ‖∫ z, conj (v z) * Λ z ∂μ‖ₑ ^ 2 ≤ (∫⁻ z, ‖v z‖ₑ ^ 2 ∂μ) * (∫⁻ z, ‖Λ z‖ₑ ^ 2 ∂μ).

No integrability or boundedness hypothesis is needed: the right-hand side is `⊤` whenever
the two functions are not (a.e.-) square-integrable, and the left-hand side is the square of
the modulus of the Bochner integral. -/
theorem enorm_integral_conj_mul_sq_le {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {v Λ : α → ℂ}
    (hv : AEMeasurable v μ) (hΛ : AEMeasurable Λ μ) :
    ‖∫ z, (starRingEnd ℂ) (v z) * Λ z ∂μ‖ₑ ^ 2
      ≤ (∫⁻ z, ‖v z‖ₑ ^ 2 ∂μ) * (∫⁻ z, ‖Λ z‖ₑ ^ 2 ∂μ) := by
  -- the integrand's `enorm` is the product of the two `enorm`s
  have hpt : ∀ z : α, ‖(starRingEnd ℂ) (v z) * Λ z‖ₑ = ‖v z‖ₑ * ‖Λ z‖ₑ := by
    intro z
    simp [enorm_eq_nnnorm]
  -- `‖∫ ·‖ₑ ≤ ∫⁻ ‖·‖ₑ`, then rewrite the integrand
  have h1 : ‖∫ z, (starRingEnd ℂ) (v z) * Λ z ∂μ‖ₑ
      ≤ ∫⁻ z, ‖v z‖ₑ * ‖Λ z‖ₑ ∂μ := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    exact lintegral_congr (fun z => hpt z)
  -- square, and apply the `L²`-Cauchy–Schwarz to the two `enorm`s
  calc ‖∫ z, (starRingEnd ℂ) (v z) * Λ z ∂μ‖ₑ ^ 2
      ≤ (∫⁻ z, ‖v z‖ₑ * ‖Λ z‖ₑ ∂μ) ^ 2 := pow_le_pow_left' h1 2
    _ ≤ (∫⁻ z, ‖v z‖ₑ ^ 2 ∂μ) * (∫⁻ z, ‖Λ z‖ₑ ^ 2 ∂μ) :=
        sq_lintegral_mul_le_aux μ hv.enorm hΛ.enorm

end Work.BoseBoxFock
