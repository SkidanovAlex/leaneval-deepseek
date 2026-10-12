import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem norm_integral_mul_le_sqrt {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ] {f g : X → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) :
    ‖∫ x, f x * g x ∂μ‖
      ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  -- Cauchy–Schwarz / Hölder with conjugate exponents `p = q = 2`.
  have hpq : (2 : ℝ).HolderConjugate (2 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  -- both functions are in `L²` because they are bounded and `μ` is a finite measure
  have hfm : MeasureTheory.MemLp f (ENNReal.ofReal 2) μ := by
    obtain ⟨C, hC⟩ := hfb
    exact MeasureTheory.MemLp.of_bound hf C (Filter.Eventually.of_forall hC)
  have hgm : MeasureTheory.MemLp g (ENNReal.ofReal 2) μ := by
    obtain ⟨C, hC⟩ := hgb
    exact MeasureTheory.MemLp.of_bound hg C (Filter.Eventually.of_forall hC)
  calc ‖∫ x, f x * g x ∂μ‖
      ≤ ∫ x, ‖f x * g x‖ ∂μ := MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp
    _ ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hpq hfm hgm
    _ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        congr 2 <;> simp only [Real.rpow_ofNat]

end Work.BoseBoxFock
