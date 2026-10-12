import Mathlib.MeasureTheory.Integral.MeanInequalities
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.MollifyAux

open MeasureTheory
open scoped ENNReal

/-- `√x * √x = x` for `x : ℝ≥0∞`, with `√x = x ^ (1/2)`. -/
lemma rpow_half_mul_self (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_add_of_nonneg (1 / 2) (1 / 2) (by norm_num) (by norm_num)]
  norm_num

/-- `(√x)^2 = x` for `x : ℝ≥0∞`. -/
lemma sq_rpow_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy–Schwarz (squared form) for the Lebesgue integral of `ℝ≥0∞`-valued functions. -/
lemma lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * (∫⁻ a, g a ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hg
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ a, g a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' h 2
    _ = (∫⁻ a, f a ^ (2 : ℝ) ∂μ) * (∫⁻ a, g a ^ (2 : ℝ) ∂μ) := by
        rw [mul_pow, sq_rpow_half, sq_rpow_half]
    _ = (∫⁻ a, f a ^ 2 ∂μ) * (∫⁻ a, g a ^ 2 ∂μ) := by simp

/-- Weighted Cauchy–Schwarz: for a weight `ρ` with `∫ ρ = 1`,
`(∫ ρ g)^2 ≤ ∫ ρ g^2`. -/
theorem sq_lintegral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ g : α → ℝ≥0∞} (hρ : AEMeasurable ρ μ) (hg : AEMeasurable g μ)
    (hρ1 : ∫⁻ a, ρ a ∂μ = 1) :
    (∫⁻ a, ρ a * g a ∂μ) ^ 2 ≤ ∫⁻ a, ρ a * (g a) ^ 2 ∂μ := by
  set f : α → ℝ≥0∞ := fun a => ρ a ^ (1 / 2 : ℝ) with hfdef
  have hf : AEMeasurable f μ := hρ.pow_const _
  have hfg : AEMeasurable (fun a => f a * g a) μ := hf.mul hg
  have key := lintegral_mul_sq_le (μ := μ) (f := f) (g := fun a => f a * g a) hf hfg
  have e1 : ∫⁻ a, ρ a * g a ∂μ = ∫⁻ a, f a * (f a * g a) ∂μ := by
    refine lintegral_congr fun a => ?_
    simp only [hfdef]
    rw [← mul_assoc, rpow_half_mul_self]
  have e2 : ∫⁻ a, ρ a * (g a) ^ 2 ∂μ = ∫⁻ a, (f a * g a) ^ 2 ∂μ := by
    refine lintegral_congr fun a => ?_
    simp only [hfdef]
    rw [mul_pow, sq_rpow_half]
  have e3 : ∫⁻ a, ρ a ∂μ = ∫⁻ a, f a ^ 2 ∂μ := by
    refine lintegral_congr fun a => ?_
    simp only [hfdef]
    exact (sq_rpow_half (ρ a)).symm
  calc (∫⁻ a, ρ a * g a ∂μ) ^ 2
      = (∫⁻ a, f a * (f a * g a) ∂μ) ^ 2 := by rw [e1]
    _ ≤ (∫⁻ a, f a ^ 2 ∂μ) * (∫⁻ a, (f a * g a) ^ 2 ∂μ) := key
    _ = (∫⁻ a, ρ a ∂μ) * (∫⁻ a, ρ a * (g a) ^ 2 ∂μ) := by rw [← e3, ← e2]
    _ = ∫⁻ a, ρ a * (g a) ^ 2 ∂μ := by rw [hρ1, one_mul]

end Work.BoseSym.MollifyAux
