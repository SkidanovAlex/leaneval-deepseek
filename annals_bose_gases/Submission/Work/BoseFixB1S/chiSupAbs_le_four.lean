import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.BoseFixB1S.oneD_pow96_integral_le_conv48
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.chiSupAbs_le_four`

`chiSupAbs = (√chiNormSq)⁻¹` is the absolute sup of the corpus bump
`χ = chiBase/√chiNormSq` (`Submission.Work.ChiSmall`), where
`chiBase = chiBump : ContDiffBump (0 : ℝ³)` has `rIn = 1/4`, `rOut = 1/2`.  The
profile of `chiBase` between the radii is opaque (it comes from
`Classical.choice`), so the only usable quantitative information is

* `chiBase = 1` on the closed ball of radius `1/4`
  (`chiBase_sq_eq_one_of_norm_le`), and
* `0 ≤ chiBase ≤ 1` (`chiBase_le_one`).

Hence `chiNormSq = ∫ (chiBase)² ≥ vol (ball 0 (1/4)) = π/48` and the sharp
constant of this method is `chiSupAbs ≤ 1/√(π/48) = √(48/π) ≈ 3.909`.  The
requested bound `4` leaves the (tiny) margin `√(48/π) < 4 ⟺ π > 3`.

Counting: the volume of the `ℝ³`-ball of radius `r` is `r³·√π³/Γ(3/2+1)`
(`EuclideanSpace.volume_ball`) and `Γ(5/2) = 3√π/4`
(`Real.Gamma_nat_add_half`), giving `π/48` at `r = 1/4`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `Γ (2 + 1/2) = Γ (5/2) = 3√π/4`. -/
lemma Gamma_two_add_half_eq : Real.Gamma ((↑(2:ℕ) : ℝ) + 1/2) = 3 * Real.sqrt Real.pi / 4 := by
  rw [Real.Gamma_nat_add_half 2]
  norm_num [Nat.doubleFactorial]

/-- The volume of the ball of radius `1/4` in `ℝ³` equals `π/48`. -/
lemma volume_ball_quarter_eq_ofReal :
    MeasureTheory.volume (Metric.ball (0 : ℝ³) (1/4)) = ENNReal.ofReal (Real.pi/48) := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show (↑(3:ℕ):ℝ) / 2 + 1 = (↑(2:ℕ):ℝ) + 1/2 by norm_num, Gamma_two_add_half_eq]
  have hs : √Real.pi ≠ 0 := by positivity
  field_simp
  ring_nf
  rw [Real.sq_sqrt Real.pi_pos.le]

/-- `chiNormSq ≥ π/48`: the bump equals `1` on the ball of radius `1/4`. -/
lemma pi_div_48_le_chiNormSq : Real.pi/48 ≤ Submission.BoseGases.chiNormSq := by
  have hint : Integrable (fun x : ℝ³ => (Submission.BoseGases.chiBase x)^2) :=
    Submission.BoseGases.chiBase_sq_continuous.integrable_of_hasCompactSupport
      Submission.BoseGases.chiBase_sq_hasCompactSupport
  have hmono : ∫ x in Metric.ball (0:ℝ³) (1/4), (Submission.BoseGases.chiBase x)^2 ≤
      Submission.BoseGases.chiNormSq :=
    MeasureTheory.setIntegral_le_integral hint (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  have hcongr : ∫ x in Metric.ball (0:ℝ³) (1/4), (Submission.BoseGases.chiBase x)^2
      = ∫ x in Metric.ball (0:ℝ³) (1/4), (1:ℝ) := by
    refine MeasureTheory.setIntegral_congr_fun Metric.isOpen_ball.measurableSet ?_
    intro x hx
    have hx' : ‖x‖ < 1/4 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    exact Submission.BoseGases.chiBase_sq_eq_one_of_norm_le (le_of_lt hx')
  have hone : ∫ x in Metric.ball (0:ℝ³) (1/4), (1:ℝ) = Real.pi/48 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
      volume_ball_quarter_eq_ofReal, ENNReal.toReal_ofReal (by positivity)]
    simp
  linarith [hmono, hcongr.symm, hone]

theorem chiSupAbs_le_four : Submission.BoseGases.chiSupAbs ≤ 4 := by
  have h16 : (1:ℝ)/16 ≤ Submission.BoseGases.chiNormSq := by
    have := pi_div_48_le_chiNormSq
    nlinarith [Real.pi_gt_three]
  have hsqrt : (1:ℝ)/4 ≤ Real.sqrt Submission.BoseGases.chiNormSq := by
    have h := Real.sqrt_le_sqrt h16
    rwa [show Real.sqrt ((1:ℝ)/16) = 1/4 by
      rw [show (1:ℝ)/16 = (1/4)^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hpos : 0 < Real.sqrt Submission.BoseGases.chiNormSq :=
    Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos
  have h4 : (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ ≤ ((1:ℝ)/4)⁻¹ := by
    rw [inv_le_inv₀ hpos (by norm_num)]
    exact hsqrt
  simpa [Submission.BoseGases.chiSupAbs] using h4

end Work.BoseFixB1S
