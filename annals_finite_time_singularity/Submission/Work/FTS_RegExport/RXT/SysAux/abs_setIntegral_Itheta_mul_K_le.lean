import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

/-- On the angular interval `Iθ = [0, π/2]` the kernel `K(θ) = 3 sin θ cos²θ` is
nonnegative and bounded by `3`. -/
theorem abs_K_le_three_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ| ≤ 3 := by
  have h3 : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg h3]
  nlinarith [Real.abs_sin_le_one θ, Real.cos_sq_le_one θ, abs_nonneg (Real.sin θ)]

/-- The Lebesgue measure of `Iθ = [0, π/2]` is `π/2`. -/
theorem volume_real_Iθ : MeasureTheory.volume.real Work.Spaces.Iθ = Real.pi / 2 := by
  rw [MeasureTheory.Measure.real_def, Work.Spaces.Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
  ring

/-- The Lebesgue measure of `Iθ = [0, π/2]` is finite. -/
theorem volume_Iθ_lt_top : MeasureTheory.volume Work.Spaces.Iθ < ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

theorem abs_setIntegral_Itheta_mul_K_le {G : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hmeas : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), |G θ| ≤ c) :
    |∫ θ in Work.Spaces.Iθ, G θ * Work.Spaces.K θ| ≤ c * 3 * (Real.pi / 2) := by
  -- the pointwise bound `‖G θ * K θ‖ ≤ 3 * c` holds almost everywhere on `Iθ`
  have hC : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖G θ * Work.Spaces.K θ‖ ≤ 3 * c := by
    filter_upwards [hb, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hG hθ
    rw [Real.norm_eq_abs, abs_mul]
    calc |G θ| * |Work.Spaces.K θ| ≤ c * 3 :=
          mul_le_mul hG (abs_K_le_three_of_mem_Iθ hθ) (abs_nonneg _) hc
      _ = 3 * c := by ring
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
      (μ := MeasureTheory.volume) (s := Work.Spaces.Iθ)
      (f := fun θ => G θ * Work.Spaces.K θ) (C := 3 * c) volume_Iθ_lt_top hC
  rw [Real.norm_eq_abs, volume_real_Iθ] at h
  calc |∫ θ in Work.Spaces.Iθ, G θ * Work.Spaces.K θ| ≤ 3 * c * (Real.pi / 2) := h
    _ = c * 3 * (Real.pi / 2) := by ring

end Work.FTS_RegExport.RXT.SysAux
