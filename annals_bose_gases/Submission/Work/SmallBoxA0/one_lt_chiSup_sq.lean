import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.SmallBoxA0.KinWitnessDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The `L²`-mass of the bump `chiBase` (a `ContDiffBump 0` with `rOut = 1/2`) is `< 1`:
the integrand `(chiBase x)²` vanishes outside `ball 0 (1/2)` and is `≤ 1` inside, so
`chiNormSq ≤ volume (ball 0 (1/2)) = (4/3) π (1/2)³ = π/6 < 1`. -/
lemma chiNormSq_lt_one : chiNormSq < 1 := by
  -- `chiBase` vanishes outside the ball of radius `1/2` (`= chiBump.rOut`)
  have hzero : ∀ x ∉ Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2 = 0 := by
    intro x hx
    have hx' : (1 : ℝ) / 2 ≤ ‖x‖ := by
      simp only [Metric.mem_ball, dist_eq_norm, not_lt, sub_zero] at hx
      exact hx
    have h0 : chiBase x = 0 :=
      chiBump.zero_of_le_dist (by simpa [chiBump, dist_eq_norm] using hx')
    rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  -- so the total integral is the integral over the ball
  have hEq : chiNormSq = ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2 := by
    rw [chiNormSq]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  -- on the ball the integrand is `≤ 1`, so the integral is at most the volume
  have hmono : ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2 ≤
      ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (1 : ℝ) := by
    apply MeasureTheory.setIntegral_mono_ae
    · exact (chiBase_sq_continuous.integrable_of_hasCompactSupport
        chiBase_sq_hasCompactSupport).integrableOn
    · exact MeasureTheory.integrableOn_const (C := (1 : ℝ))
    · filter_upwards with x
      rw [pow_two]
      nlinarith [chiBase_nonneg x, chiBase_le_one x]
  -- the volume of the ball of radius `1/2` in `ℝ³` is `(4/3) π (1/2)³ = π/6`
  have hval : ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (1 : ℝ) =
      (4 / 3) * Real.pi * (1 / 2) ^ 3 := by
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.Measure.real_def, volume_ball_open_r3 (1 / 2) (by norm_num)]
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hπ : (4 / 3) * Real.pi * (1 / 2) ^ 3 < 1 := by
    have := Real.pi_lt_four
    nlinarith [Real.pi_pos]
  calc chiNormSq = ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2 := hEq
    _ ≤ ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (1 : ℝ) := hmono
    _ = (4 / 3) * Real.pi * (1 / 2) ^ 3 := hval
    _ < 1 := hπ

/-- `1 < chiSup ^ 2`, where `chiSup := (Real.sqrt chiNormSq)⁻¹` and `chiNormSq := ∫ z, (chiBase z)²`.
Equivalently `chiNormSq < 1`.  HINT: `chiBase` is a `ContDiffBump 0` with `rOut = 1/2`, so
`0 ≤ chiBase ≤ 1` and `chiBase = 0` for `‖z‖ ≥ 1/2`; hence
`chiNormSq ≤ volume (ball 0 (1/2)) = π/6 < 1` (use `EuclideanSpace.volume_ball` for `ι = Fin 3`,
whose value is `(ofReal (1/2))^3 * ofReal (√π ^ 3 / Gamma (3/2 + 1))`, with
`Gamma (3/2 + 1) = 3√π/4` from `Real.Gamma_add_one` and `Real.Gamma_one_half_eq`, and
`π/6 < 1` from `Real.pi_lt_four`).  A cruder route also works: the support of `chiBase` lies in
`ball 0 (1/2) ⊂ acube 1` and `chiBase < 1` on a nonempty open subset of `acube 1`, so
`chiNormSq < volume (acube 1) = 1`. -/
lemma one_lt_chiSup_sq : 1 < chiSup ^ 2 := by
  have hsq : chiSup ^ 2 = chiNormSq⁻¹ := by
    unfold chiSup
    rw [inv_pow, Real.sq_sqrt (le_of_lt chiNormSq_pos)]
  rw [hsq, one_lt_inv_iff₀]
  exact ⟨chiNormSq_pos, chiNormSq_lt_one⟩

end Work.SmallBoxA0
