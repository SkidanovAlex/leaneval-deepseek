import Mathlib
import Submission.Work.RadialSpace.RadialSeminorm
import Submission.Work.RadialSpace.Profile

/-!
# Radial derivatives

Corollaries of the radial-derivative API: the radial derivative of a radial
function vanishes at the origin (in every order), and the profile of a radial
function has vanishing odd derivatives at `0`.

## Main results

* `Work.RadialSpace.radialDeriv_zero`
* `Work.RadialSpace.iteratedDeriv_profile_odd_zero`
-/

open Filter Topology
open scoped SchwartzMap Topology ContDiff ENNReal

namespace Work.RadialSpace

open LeanEval.Analysis.CKMRVInterpolation

variable {n : ℕ} [NeZero n]

/-- The radial derivative of a radial function vanishes at the origin. -/
theorem radialDeriv_zero {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Radial f) :
    radialDeriv f 0 = 0 := by
  rw [radialDeriv_apply, norm_zero]
  exact deriv_profile_zero hf

/-- All odd iterated derivatives of the profile of a radial function vanish at
the origin. -/
theorem iteratedDeriv_profile_odd_zero {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Radial f)
    {m : ℕ} (hm : Odd m) : iteratedDeriv m (profile f) 0 = 0 := by
  have hfun : (fun x : ℝ => profile f (-x)) = profile f := funext (profile_neg hf)
  have h := iteratedDeriv_comp_neg m (profile f) 0
  rw [hfun, neg_zero] at h
  -- h : iteratedDeriv m (profile f) 0 = (-1) ^ m • iteratedDeriv m (profile f) 0
  have hneg : ((-1 : ℝ) ^ m) = -1 := by
    rw [hm.neg_one_pow]
  rw [hneg, neg_one_smul] at h
  have h5 : iteratedDeriv m (profile f) 0 + iteratedDeriv m (profile f) 0 = 0 := by
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  have h6 : (2 : ℂ) * iteratedDeriv m (profile f) 0 = 0 := by
    rw [two_mul]; exact h5
  exact (mul_eq_zero.mp h6).resolve_left two_ne_zero

end Work.RadialSpace
