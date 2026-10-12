import ChallengeDeps
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bridge: the `L²`-norm-squared of a test function's graph point

For a smooth test function `F` supported in the open box, the function part of
its graph point `graphPoint N L F = (F, ∇F)` is the `L²` class of `F`, so

`l2Sq (graphPoint N L F) = ∫_{box N L} F²`.

The `L²` norm is computed through the inner product of `L²(volC N)`:
`‖u‖² = ⟪u,u⟫ = ∫ (toLp F)² = ∫ F²`, using `MemLp.coeFn_toLp`; the last step
replaces the integral over all of `Conf N` by the integral over `box N L`,
which is legitimate because `F` vanishes identically off `openBox N L ⊆ box N L`.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory
open BoseGases
open Submission.BoseGases

theorem l2Sq_graphPoint_box {N : ℕ} {L : ℝ} (F : testSub N L) :
    l2Sq (graphPoint N L F) = intBox N L (fun x => ((F : Conf N → ℝ) x) ^ 2) := by
  have hmem : MemLp (F : Conf N → ℝ) 2 (volC N) :=
    memLp_of_contDiff_hasCompactSupport F.2.1 (hasCompactSupport_of_testFun F.2)
  have h1 : l2Sq (graphPoint N L F)
      = ‖(MemLp.toLp (F : Conf N → ℝ) hmem : L2 N)‖ ^ 2 := by
    simp only [l2Sq, graphPoint]
  have h2 : ‖(MemLp.toLp (F : Conf N → ℝ) hmem : L2 N)‖ ^ 2
      = ∫ x, ((F : Conf N → ℝ) x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hmem] with x hx
    rw [hx]
    simp [sq]
  rw [h1, h2]
  rw [show intBox N L (fun x => ((F : Conf N → ℝ) x) ^ 2)
        = ∫ x in box N L, ((F : Conf N → ℝ) x) ^ 2 from rfl]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := (volume : Measure (Conf N)))]
  intro x hx
  have hxs : x ∉ Function.support (F : Conf N → ℝ) := by
    intro hmem'
    exact hx (openBox_subset_box (F.2.2 (subset_tsupport _ hmem')))
  simp [Function.mem_support] at hxs
  simp [hxs]

end Work.BoseSym.Bridge
