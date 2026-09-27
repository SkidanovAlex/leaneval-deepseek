import Mathlib
import Submission.Work.EKLComp.USCBasic
import Submission.Work.Misiurewicz.exists_null_frontier_Vball_radius

/-!
# A bump function on a ball in `X₃`

For `0 < r < s` and `y : X₃` we build a continuous `ψ : X₃ → ℝ` with values in `[0,1]` which is
`1` on `ball r y` and `0` outside `ball s y`.

The construction is Urysohn's lemma in its locally compact form
(`exists_continuous_one_zero_of_isCompact`, which needs only `RegularSpace` and
`LocallyCompactSpace` and a *compact* rather than closed first set):

* the ball `ball r y = V r • y` is contained in the image of the closed box `Vbar r` under the
  continuous orbit map `u ↦ u • y`; that image is compact (`Vbar r` is the closed box
  `Work.EKLNonExc.clBox r`) and closed, so `closure (ball r y)` is compact;
* the balls *never jump*: `closure (ball r y) ⊆ ball s y` for `r < s`
  (`Work.Misiurewicz.closure_Vball_subset`), so `closure (ball r y)` is disjoint from the closed
  set `(ball s y)ᶜ`.

Urysohn applied to these two sets gives `ψ` with `ψ = 1` on `closure (ball r y)` (hence on
`ball r y`) and `ψ = 0` on `(ball s y)ᶜ`, as required.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.EKLComp

open MeasureTheory Filter Topology
open Work.EKLContract

theorem exists_bump_on_ball (y : Work.EKLContract.X3) {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    ∃ ψ : Work.EKLContract.X3 → ℝ, Continuous ψ ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
      (∀ x ∈ Work.EKLComp.ball r y, ψ x = 1) ∧
      (∀ x, x ∉ Work.EKLComp.ball s y → ψ x = 0) := by
  -- `X₃` is Hausdorff and locally compact (so that Urysohn's lemma applies)
  haveI : IsClosed (Γ3 : Set SL3) := Work.EKLContract.Lemmas.isClosed_Γ3
  haveI : T2Space X3 := inferInstance
  haveI : LocallyCompactSpace X3 := inferInstance
  -- `ball r y` is contained in the compact closed image of the closed box `Vbar r`
  have hK : IsCompact (Vbar r) := Work.EKLNonExc.clBox_isCompact r
  have himg : IsCompact ((fun u : SL3 => u • y) '' Vbar r) :=
    hK.image (Work.Misiurewicz.continuous_smul_X3 y)
  have hsub : closure (ball r y) ⊆ (fun u : SL3 => u • y) '' Vbar r :=
    closure_minimal (Vball_subset_Vbar_ball r y) himg.isClosed
  have hcomp : IsCompact (closure (ball r y)) :=
    himg.of_isClosed_subset isClosed_closure hsub
  -- the balls do not jump: the closure of the smaller ball still sits inside the larger ball
  have hcl : closure (ball r y) ⊆ ball s y :=
    Work.Misiurewicz.closure_Vball_subset y hrs
  -- Urysohn between `closure (ball r y)` (compact) and `(ball s y)ᶜ` (closed)
  obtain ⟨f, hf1, hf0, -, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hcomp (isOpen_ball s y).isClosed_compl
      (Set.disjoint_compl_right_iff_subset.mpr hcl)
  refine ⟨f, f.continuous, fun x => hf01 x, ?_, ?_⟩
  · intro x hx
    exact hf1 (subset_closure hx)
  · intro x hx
    exact hf0 (by simpa using hx)

end Work.EKLComp
