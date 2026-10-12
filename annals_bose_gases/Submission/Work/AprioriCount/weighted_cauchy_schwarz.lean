import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AprioriCount

open MeasureTheory

-- The hypothesis `0 ≤ᵐ[μ] G` of `weighted_cauchy_schwarz` is part of the requested interface but is
-- not needed by the proof (only `0 ≤ᵐ[μ] F` is), so `hG` appears unused; silence the linter.
set_option linter.unusedVariables false

/-- If `A ≥ 0` and the quadratic polynomial `t ↦ A t² - 2 B t + C` is nonnegative on all of `ℝ`,
then `B² ≤ A C`.  (For `A > 0` this is the nonnegativity of the polynomial at its vertex `B/A`;
for `A = 0` nonnegativity forces `B = 0`.) -/
lemma sq_le_mul_of_quadratic_nonneg {A B C : ℝ} (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ A * t ^ 2 - 2 * B * t + C) : B ^ 2 ≤ A * C := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · -- degenerate case: `A = 0`; nonnegativity at `t = (C+1)/(2B)` rules out `B ≠ 0`
    have hB : B = 0 := by
      by_contra hBne
      have hval := h ((C + 1) / (2 * B))
      have hthis : A * ((C + 1) / (2 * B)) ^ 2 - 2 * B * ((C + 1) / (2 * B)) + C = -1 := by
        rw [← hA0]
        field_simp
        ring
      rw [hthis] at hval
      linarith
    subst hA0
    rw [hB]
    norm_num
  · -- nondegenerate case: evaluate at the vertex `B / A`
    have hval := h (B / A)
    have hthis : A * (B / A) ^ 2 - 2 * B * (B / A) + C = C - B ^ 2 / A := by
      field_simp
      ring
    rw [hthis] at hval
    have h2 : B ^ 2 / A ≤ C := by linarith
    calc B ^ 2 = A * (B ^ 2 / A) := by field_simp
      _ ≤ A * C := mul_le_mul_of_nonneg_left h2 (le_of_lt hApos)

/-- **Weighted Cauchy–Schwarz.**  For nonnegative a.e. functions `F`, `G` such that
`F`, `F * G` and `F * G ^ 2` are integrable,
`(∫ F G)² ≤ (∫ F) (∫ F G²)`.

The proof integrates the pointwise nonnegative quantity `F (G - t)²` for every real `t`.  Writing
`A = ∫ F`, `B = ∫ F G`, `C = ∫ F G²`, this yields `0 ≤ A t² - 2 B t + C` for all `t`, whence
`B² ≤ A C` by `sq_le_mul_of_quadratic_nonneg` (with `A = ∫ F ≥ 0`).  (Only `F ≥ 0` is used; the
hypothesis `0 ≤ᵐ[μ] G` is part of the requested interface.) -/
theorem weighted_cauchy_schwarz {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {F G : α → ℝ}
    (hF : 0 ≤ᵐ[μ] F) (hG : 0 ≤ᵐ[μ] G)
    (hFi : MeasureTheory.Integrable F μ) (hFGi : MeasureTheory.Integrable (fun x => F x * G x) μ)
    (hFG2i : MeasureTheory.Integrable (fun x => F x * G x ^ 2) μ) :
    (∫ x, F x * G x ∂μ) ^ 2 ≤ (∫ x, F x ∂μ) * (∫ x, F x * G x ^ 2 ∂μ) := by
  have hquad : ∀ t : ℝ, 0 ≤ (∫ x, F x ∂μ) * t ^ 2 - 2 * (∫ x, F x * G x ∂μ) * t
      + (∫ x, F x * G x ^ 2 ∂μ) := by
    intro t
    have h1 : Integrable (fun x => (2 * t) * (F x * G x)) μ := hFGi.const_mul (2 * t)
    have h2 : Integrable (fun x => t ^ 2 * F x) μ := hFi.const_mul (t ^ 2)
    have hAB : Integrable (fun x => F x * G x ^ 2 - (2 * t) * (F x * G x)) μ := hFG2i.sub h1
    have hcongr : (fun x => F x * (G x - t) ^ 2) =ᵐ[μ]
        (fun x => (F x * G x ^ 2 - (2 * t) * (F x * G x)) + t ^ 2 * F x) :=
      Filter.Eventually.of_forall fun x => by ring
    have hInt : ∫ x, F x * (G x - t) ^ 2 ∂μ
        = (∫ x, F x ∂μ) * t ^ 2 - 2 * (∫ x, F x * G x ∂μ) * t
          + (∫ x, F x * G x ^ 2 ∂μ) := by
      rw [integral_congr_ae hcongr]
      rw [integral_add hAB h2]
      rw [integral_sub hFG2i h1]
      rw [integral_const_mul, integral_const_mul]
      ring
    rw [← hInt]
    exact integral_nonneg_of_ae (hF.mono fun x hx => mul_nonneg hx (sq_nonneg _))
  exact sq_le_mul_of_quadratic_nonneg (integral_nonneg_of_ae hF) hquad

end Work.AprioriCount
