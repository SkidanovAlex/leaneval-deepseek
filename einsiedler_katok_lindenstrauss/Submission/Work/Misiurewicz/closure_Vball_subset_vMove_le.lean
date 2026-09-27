import Mathlib
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.Misiurewicz.vMove_lt_iff
import Submission.Work.EKLNonExc.VFacts
import Submission.Work.Misiurewicz.Vball_eq_empty_of_nonpos

/-!
# `closure (V r • z) ⊆ {y | vMove z y ≤ r}`

The `V`-displacement `vMove z y` (see `Submission/Work/EKLComp/Misiurewicz/Defs.lean`) is the
infimum of the `δ > 0` with `y ∈ Vball δ z = V δ • z`, and `Submission/Work/Misiurewicz/
vMove_lt_iff.lean` shows `vMove z y < r ↔ y ∈ Vball r z` for `r > 0`.  The present file takes the
limit of that equivalence: the closure of a ball of radius `r` sits in the closed sublevel set
`{y | vMove z y ≤ r}`.  This is the "the balls do not jump" statement used for the frontier
estimate of the Misiurewicz construction.

The mathematical content is that for every `s > r` the translate `Vball s z` *contains* the
closure of `Vball r z`, i.e. the strict inequality of the displacement is preserved in the limit.
This is proved here by compactness rather than by `V`-arithmetic:

* the closed entrywise box `Vbar r` is compact (`Work.EKLNonExc.clBox_isCompact`), the orbit map
  `u ↦ u • z : SL₃(ℝ) → X₃` is continuous, and `X₃` is Hausdorff, so the image
  `(fun u ↦ u • z) '' Vbar r` is closed;
* it contains `Vball r z = (fun u ↦ u • z) '' V r` because `V r ⊆ Vbar r`, hence it contains
  `closure (Vball r z)`;
* finally `Vbar r ⊆ V s` for `r < s`, since the entrywise condition is `≤ r` and `< s`.

For `r > 0` this yields `vMove z y < s` for every `s > r`, whence `vMove z y ≤ r`.  For `r ≤ 0`
the ball itself is empty (`Work.Misiurewicz.Vball_eq_empty_of_nonpos`), so its closure is empty
and the claim is vacuous.
-/

namespace Work.Misiurewicz

open Work.EKLContract Work.EKLComp

/-- The orbit map `u ↦ u • z : SL₃(ℝ) → X₃` is continuous. -/
theorem continuous_smul_X3 (z : X3) : Continuous (fun u : SL3 => u • z) :=
  continuous_id.smul continuous_const

/-- The translate `Vbar r • z` is closed in `X₃`: it is the image of the compact box `Vbar r`
under the continuous orbit map, and `X₃` is Hausdorff. -/
theorem isClosed_vbarBall (z : X3) (r : ℝ) : IsClosed ((fun u : SL3 => u • z) '' Vbar r) :=
  ((Work.EKLNonExc.clBox_isCompact r).image (continuous_smul_X3 z)).isClosed

/-- **The balls do not jump**: for `r < s` the closure of `Vball r z` is contained in
`Vball s z`. -/
theorem closure_Vball_subset_Vball_of_lt (z : X3) {r s : ℝ} (hrs : r < s) :
    closure (Vball r z) ⊆ Vball s z := by
  have hclosed := isClosed_vbarBall z r
  have h1 : closure (Vball r z) ⊆ ((fun u : SL3 => u • z) '' Vbar r) := by
    rw [← hclosed.closure_eq]
    exact closure_mono (Vball_subset_Vbar_ball r z)
  intro y hy
  obtain ⟨u, hu, rfl⟩ := h1 hy
  exact ⟨u, fun i j => lt_of_le_of_lt (hu i j) hrs, rfl⟩

theorem closure_Vball_subset_vMove_le (r : ℝ) (z : Work.EKLContract.X3) : closure (Work.EKLComp.Vball r z) ⊆ {y : Work.EKLContract.X3 | Work.EKLComp.vMove z y ≤ r} := by
  intro y hy
  by_cases hr : 0 < r
  · -- `vMove z y < s` for every `s > r`, so `vMove z y ≤ r`
    refine le_of_forall_gt (a := r) (b := vMove z y) (fun s hs => ?_)
    rw [vMove_lt_iff (lt_trans hr hs)]
    exact closure_Vball_subset_Vball_of_lt z hs hy
  · -- for `r ≤ 0` the ball, and hence its closure, is empty
    obtain hrle : r ≤ 0 := not_lt.mp hr
    rw [Vball_eq_empty_of_nonpos hrle z, closure_empty] at hy
    exact absurd hy (by simp)

end Work.Misiurewicz
