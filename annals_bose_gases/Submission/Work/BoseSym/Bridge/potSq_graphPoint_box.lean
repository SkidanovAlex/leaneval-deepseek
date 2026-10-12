import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — the potential energy `∫ W u²` of the graph point of a box test function

For a smooth test function `F` supported in the open box, the function part of
its graph point `graphPoint N L F = (F, ∇F)` is (the `L²` class of) `F`, so the
potential energy of the graph point is the box integral of the pointwise
weighted square:

`potSq W (graphPoint N L F) = ∫_{box N L} W x · F x ^ 2`.

The two ingredients are:

* `MemLp.coeFn_toLp` — `MemLp.toLp F h` agrees a.e. with `F`, so the pointwise
  weighted squares `W · (toLp F h)²` and `W · F²` are a.e. equal
  (`integral_congr_ae`);
* `F` vanishes identically off `openBox N L ⊆ box N L`, so the integral over
  the whole configuration space equals the integral over the box
  (`setIntegral_eq_integral_of_forall_compl_eq_zero`).

## Main results

* `potSq_graphPoint_box`
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ContDiff ENNReal

theorem potSq_graphPoint_box {N : ℕ} {L : ℝ} {W : Conf N → ℝ} (F : testSub N L) :
    potSq W (graphPoint N L F) = intBox N L (fun x => W x * ((F : Conf N → ℝ) x) ^ 2) := by
  -- unfold the potential energy, the graph point and the box integral
  simp only [potSq, graphPoint, intBox]
  -- the `L²` class of `F` agrees a.e. with `F` itself
  set hmem : MemLp (F : Conf N → ℝ) 2 (volC N) :=
    memLp_of_contDiff_hasCompactSupport F.2.1 (hasCompactSupport_of_testFun F.2)
  have hae : (fun x => W x * ((MemLp.toLp (F : Conf N → ℝ) hmem : L2 N) x) ^ 2)
      =ᵐ[volC N] (fun x => W x * ((F : Conf N → ℝ) x) ^ 2) := by
    filter_upwards [MemLp.coeFn_toLp hmem] with x hx
    rw [hx]
  rw [integral_congr_ae hae]
  -- the integrand vanishes off the box, so the integral over all of
  -- configuration space is the integral over the box
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := (volume : Measure (Conf N)))]
  intro x hx
  have hx0 : (F : Conf N → ℝ) x = 0 := by
    by_contra hne
    exact hx (openBox_subset_box (F.2.2 (subset_tsupport _ hne)))
  rw [hx0]
  ring

end Work.BoseSym.Bridge
