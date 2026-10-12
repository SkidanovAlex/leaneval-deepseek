import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseSym.Bridge.l2Sq_graphPoint_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Strict positivity of the `L²`-norm-squared of a nonzero test function's graph point

For a smooth test function `F` supported in the open box `openBox N L`, with `F`
not identically zero, the function part of the graph point `graphPoint N L F` is
the (nonzero) `L²` class of `F`, so `l2Sq (graphPoint N L F) > 0`.

Route: `l2Sq_graphPoint_box` identifies `l2Sq (graphPoint N L F)` with the box
integral `∫_{box N L} F²`; the integrand `F²` is continuous, nonnegative and
compactly supported, hence its integral over the whole space is strictly positive
by `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero` (a point where
`F ≠ 0` exists by hypothesis), and since `F` vanishes off `openBox N L ⊆ box N L`
the box integral is the whole-space integral.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory
open BoseGases
open Submission.BoseGases

/-- A nonzero smooth test function supported in the open box has strictly
positive squared `L²` norm at its graph point. -/
theorem pos_l2Sq_graphPoint {N : ℕ} {L : ℝ} (F : Work.BoseSym.testSub N L)
    (hF : (F : Work.BoseSym.Conf N → ℝ) ≠ 0) :
    0 < Work.BoseSym.l2Sq (Work.BoseSym.graphPoint N L F) := by
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hF
  have hcont : Continuous (fun x : Work.BoseSym.Conf N =>
      ((F : Work.BoseSym.Conf N → ℝ) x) ^ 2) :=
    F.2.1.continuous.pow 2
  have hcs : HasCompactSupport (fun x : Work.BoseSym.Conf N =>
      ((F : Work.BoseSym.Conf N → ℝ) x) ^ 2) :=
    (hasCompactSupport_of_testFun F.2).mono (fun x hx => by
      simp only [Function.mem_support] at hx ⊢
      intro h
      exact hx (by rw [h]; ring))
  have hvanish : ∀ x ∉ box N L, ((F : Work.BoseSym.Conf N → ℝ) x) ^ 2 = 0 := by
    intro x hx
    have : (F : Work.BoseSym.Conf N → ℝ) x = 0 := by
      by_contra h
      exact hx (openBox_subset_box (F.2.2 (subset_tsupport _ (Function.mem_support.mpr h))))
    simp [this]
  rw [l2Sq_graphPoint_box F]
  rw [show Work.BoseSym.intBox N L (fun x => ((F : Work.BoseSym.Conf N → ℝ) x) ^ 2)
      = ∫ x in box N L, ((F : Work.BoseSym.Conf N → ℝ) x) ^ 2 from rfl]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : Measure (Work.BoseSym.Conf N))) hvanish]
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀) hcs
    (fun x => sq_nonneg _) (by simpa using pow_ne_zero 2 hx₀)

end Work.BoseSym.Bridge
