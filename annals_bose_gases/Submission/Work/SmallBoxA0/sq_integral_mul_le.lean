import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory

/-- Cauchy–Schwarz for the Bochner integral of two real `L²` functions:
`(∫ f g)² ≤ (∫ f²) (∫ g²)`. -/
lemma sq_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    {f g : α → ℝ} (hf : MeasureTheory.MemLp f 2 μ) (hg : MeasureTheory.MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  -- Hölder with conjugate exponents `2` and `2`
  have hhold := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g)
      Real.HolderConjugate.two_two hf' hg'
  have hAf : ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ = ∫ x, (f x) ^ 2 ∂μ := by
    simp_rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hBg : ∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ = ∫ x, (g x) ^ 2 ∂μ := by
    simp_rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hA0 : 0 ≤ ∫ x, (f x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hB0 : 0 ≤ ∫ x, (g x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hhold' : ∫ x, ‖f x‖ * ‖g x‖ ∂μ
      ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
    rw [hAf, hBg, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hhold
    exact hhold
  have h1 : |∫ x, f x * g x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    simpa [abs_mul, Real.norm_eq_abs] using
      abs_integral_le_integral_abs (μ := μ) (f := fun x => f x * g x)
  have h2 : (0 : ℝ) ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ :=
    integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hstep1 : (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ^ 2 := by
    refine sq_le_sq.mpr ?_
    rw [abs_of_nonneg h2]
    exact h1
  have hstep2 : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ^ 2
      ≤ (Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ)) ^ 2 := by
    refine sq_le_sq.mpr ?_
    rw [abs_of_nonneg h2,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact hhold'
  have hstep3 : (Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ)) ^ 2
      = (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
    rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  exact le_trans hstep1 (le_trans hstep2 (le_of_eq hstep3))

end Work.SmallBoxA0
