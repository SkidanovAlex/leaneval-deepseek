import Mathlib.MeasureTheory.Integral.MeanInequalities
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cauchy–Schwarz for the Lebesgue integral over a restricted measure

`(∫⁻ x, f x ∂(μ.restrict s)) ^ 2 ≤ μ s * ∫⁻ x, (f x) ^ 2 ∂(μ.restrict s)`

This is Cauchy–Schwarz (Hölder with conjugate exponents `p = q = 2`) applied to the pair
`(f, 1)` on the measure `μ.restrict s`, together with `(μ.restrict s) univ = μ s`.  No
integrability hypothesis on `f` is needed: everything is stated in `ℝ≥0∞`.
-/

namespace Work.BoseFixB1.Core

open MeasureTheory
open scoped ENNReal

/-- `(√x)² = x` in `ℝ≥0∞`, with `√x = x ^ (1/2)`. -/
private lemma sq_rpow_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem sq_setLintegral_le_mul {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s : Set α}
    (hs : MeasurableSet s) {f : α → ENNReal} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂(μ.restrict s)) ^ 2 ≤ μ s * ∫⁻ x, (f x) ^ 2 ∂(μ.restrict s) := by
  have hfν : AEMeasurable f (μ.restrict s) := hf.mono_measure Measure.restrict_le_self
  -- Hölder (`p = q = 2`) applied to `f` and the constant function `1`.
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict s) Real.HolderConjugate.two_two hfν
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have hmul : ∫⁻ a, f a * (1 : ℝ≥0∞) ∂(μ.restrict s) = ∫⁻ a, f a ∂(μ.restrict s) :=
    lintegral_congr fun a => mul_one _
  have hconst : (∫⁻ a, ((1 : ℝ≥0∞)) ^ 2 ∂(μ.restrict s)) = μ s := by
    have h1 : (∫⁻ a, ((1 : ℝ≥0∞)) ^ 2 ∂(μ.restrict s)) =
        ∫⁻ a, (1 : ℝ≥0∞) ∂(μ.restrict s) := lintegral_congr fun a => by norm_num
    rw [h1, lintegral_one, Measure.restrict_apply' hs, Set.univ_inter]
  have h' : ∫⁻ a, f a * (1 : ℝ≥0∞) ∂(μ.restrict s) ≤
      (∫⁻ a, (f a) ^ 2 ∂(μ.restrict s)) ^ (1 / 2 : ℝ) *
        (∫⁻ a, ((1 : ℝ≥0∞)) ^ 2 ∂(μ.restrict s)) ^ (1 / 2 : ℝ) := by
    simpa [Pi.mul_apply, ENNReal.rpow_natCast] using h
  rw [hmul, hconst] at h'
  -- Square both sides.
  refine (pow_le_pow_left' h' 2).trans ?_
  rw [mul_pow, sq_rpow_half, sq_rpow_half, mul_comm]

end Work.BoseFixB1.Core
