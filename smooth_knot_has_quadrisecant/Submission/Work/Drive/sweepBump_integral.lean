import Mathlib
import Submission.Work.Drive.chordSweepSmooth

/-!
# Total mass of the smoothing bump

`Work.Drive.sweepBump u = Real.smoothTransition (1 + u) * Real.smoothTransition (1 - u)` is
the `C^∞` bump supported on `[-1,1]` used to smooth the chord sweep.  This file proves that it
has total mass one: `∫_{-1}^{1} sweepBump = 1`.
-/

namespace Work.Drive

open scoped Real Topology intervalIntegral

/-- The symmetry of `Real.smoothTransition`: `σ x + σ (1 - x) = 1`. -/
private lemma sweepTransition_symm (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  rw [Real.smoothTransition, Real.smoothTransition]
  have h3 : (1 : ℝ) - (1 - x) = x := by ring
  rw [h3]
  have hden : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    ne_of_gt (Real.smoothTransition.pos_denom x)
  rw [add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x)]
  rw [← add_div]
  exact div_self hden

/-- `∫_0^1 σ = 1/2`, by symmetry of the transition function. -/
private lemma integral_smoothTransition_zero_one :
    (∫ x in (0:ℝ)..1, Real.smoothTransition x) = 1/2 := by
  have hsub : (∫ x in (0:ℝ)..1, Real.smoothTransition (1 - x))
      = (∫ x in (0:ℝ)..1, Real.smoothTransition x) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => Real.smoothTransition x) (a := 0) (b := 1)]
    norm_num
  have hone : (∫ x in (0:ℝ)..1,
      (Real.smoothTransition x + Real.smoothTransition (1 - x))) = 1 := by
    rw [show (fun x : ℝ => Real.smoothTransition x + Real.smoothTransition (1 - x))
        = fun _ => (1:ℝ) from funext sweepTransition_symm]
    simp
  have hA : (∫ x in (0:ℝ)..1, Real.smoothTransition x)
      + (∫ x in (0:ℝ)..1, Real.smoothTransition (1 - x)) = 1 := by
    rw [← intervalIntegral.integral_add (μ := MeasureTheory.volume)
      (f := Real.smoothTransition) (g := fun x : ℝ => Real.smoothTransition (1 - x))
      (Real.smoothTransition.continuous.intervalIntegrable 0 1)
      ((Real.smoothTransition.continuous.comp
        (continuous_const.sub continuous_id)).intervalIntegrable 0 1)]
    exact hone
  rw [← hsub] at hA
  nlinarith [hA]

private lemma sweepBump_cont : Continuous sweepBump := by
  change Continuous (fun u : ℝ =>
    Real.smoothTransition (1 + u) * Real.smoothTransition (1 - u))
  exact (Real.smoothTransition.continuous.comp (continuous_const.add continuous_id)).mul
    (Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id))

theorem sweepBump_integral : (∫ u in (-1 : ℝ)..1, sweepBump u) = 1 := by
  have hadd : ((∫ x in (-1:ℝ)..0, sweepBump x)) + (∫ x in (0:ℝ)..1, sweepBump x)
      = (∫ x in (-1:ℝ)..1, sweepBump x) :=
    intervalIntegral.integral_add_adjacent_intervals
      (show IntervalIntegrable sweepBump MeasureTheory.volume (-1) 0 from
        sweepBump_cont.intervalIntegrable _ _)
      (show IntervalIntegrable sweepBump MeasureTheory.volume 0 1 from
        sweepBump_cont.intervalIntegrable _ _)
  have hleft : (∫ u in (-1:ℝ)..0, sweepBump u) = 1/2 := by
    have h1 : (∫ u in (-1:ℝ)..0, sweepBump u)
        = (∫ u in (-1:ℝ)..0, Real.smoothTransition (1 + u)) := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hu
      rw [sweepBump]
      rw [Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 1 - u by linarith [hu.2]),
        mul_one]
    rw [h1]
    have hshift : (∫ u in (-1:ℝ)..0, Real.smoothTransition (1 + u))
        = (∫ x in (0:ℝ)..1, Real.smoothTransition x) := by
      rw [intervalIntegral.integral_comp_add_left (fun x => Real.smoothTransition x) 1]
      norm_num
    rw [hshift, integral_smoothTransition_zero_one]
  have hright : (∫ u in (0:ℝ)..1, sweepBump u) = 1/2 := by
    have h1 : (∫ u in (0:ℝ)..1, sweepBump u)
        = (∫ u in (0:ℝ)..1, (1 - Real.smoothTransition u)) := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
      rw [sweepBump]
      rw [Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 1 + u by linarith [hu.1]),
        one_mul]
      have := sweepTransition_symm u
      linarith
    rw [h1, intervalIntegral.integral_sub intervalIntegrable_const
      (Real.smoothTransition.continuous.intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    rw [integral_smoothTransition_zero_one]; ring
  rw [← hadd, hleft, hright]; norm_num

end Work.Drive
