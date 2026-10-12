import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.UBBInputs9.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `chiSup^2 ≥ 1 + 1/1000`

`chiSup = (∫ χ_base²)^{-1/2}` where `χ_base` is the `ContDiffBump 0` with
`rIn = 1/4`, `rOut = 1/2`.  Since `0 ≤ χ_base ≤ 1` with support inside
`ball 0 (1/2)`, we have `∫ χ_base² ≤ vol (ball 0 (1/2)) = π/6 ≈ 0.5236`, hence
`chiSup² = (∫ χ_base²)^{-1} ≥ 6/π ≥ 1 + 1/1000`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The `L²`-mass of the bump: `∫ χ_base² ≤ vol (ball 0 (1/2)) = π/6`. -/
lemma chiNormSq_le_pi_div_six : Submission.BoseGases.chiNormSq ≤ Real.pi / 6 := by
  have hzero : ∀ x ∉ Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2 = 0 := by
    intro x hx
    have hx' : (1 : ℝ) / 2 ≤ ‖x‖ := by
      simp only [Metric.mem_ball, dist_eq_norm, not_lt, sub_zero] at hx
      exact hx
    have h0 : chiBase x = 0 :=
      chiBump.zero_of_le_dist (by simpa [chiBump, dist_eq_norm] using hx')
    rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hEq : chiNormSq = ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2 := by
    rw [chiNormSq]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hmono : ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2 ≤
      ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (1 : ℝ) := by
    apply MeasureTheory.setIntegral_mono_ae
    · exact (chiBase_sq_continuous.integrable_of_hasCompactSupport
        chiBase_sq_hasCompactSupport).integrableOn
    · exact MeasureTheory.integrableOn_const (C := (1 : ℝ))
    · filter_upwards with x
      rw [pow_two]
      nlinarith [chiBase_nonneg x, chiBase_le_one x]
  have hval : ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (1 : ℝ) =
      (4 / 3) * Real.pi * (1 / 2) ^ 3 := by
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.Measure.real_def, volume_ball_open_r3 (1 / 2) (by norm_num)]
    rw [ENNReal.toReal_ofReal (by positivity)]
  calc chiNormSq = ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2 := hEq
    _ ≤ ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (1 : ℝ) := hmono
    _ = (4 / 3) * Real.pi * (1 / 2) ^ 3 := hval
    _ = Real.pi / 6 := by ring

theorem chiSup_sq_ge : (1 : ℝ) + 1 / 1000 ≤ Submission.BoseGases.chiSup ^ 2 := by
  have hsq : chiSup ^ 2 = chiNormSq⁻¹ := by
    unfold chiSup
    rw [inv_pow, Real.sq_sqrt (le_of_lt chiNormSq_pos)]
  rw [hsq]
  have hpi : Real.pi / 6 ≤ (1000 / 1001 : ℝ) := by
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hb : chiNormSq ≤ (1000 / 1001 : ℝ) := le_trans chiNormSq_le_pi_div_six hpi
  have h' : (1000 / 1001 : ℝ)⁻¹ ≤ chiNormSq⁻¹ :=
    (inv_le_inv₀ (by norm_num) chiNormSq_pos).mpr hb
  have he : (1 : ℝ) + 1 / 1000 = (1000 / 1001 : ℝ)⁻¹ := by norm_num
  exact le_trans he.le h'

end Work.UBBInputs9.B
