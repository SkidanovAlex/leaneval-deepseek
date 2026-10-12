import ChallengeDeps
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The indicator of the box of an a.e.-strongly measurable function

The box `box N L ⊆ Conf N` is a closed (hence measurable) set, and the identity
`aemeasurable_indicator_iff` states that for a measurable `s` the function
`s.indicator f` is a.e.-measurable w.r.t. `μ` exactly when `f` is a.e.-measurable
w.r.t. the restricted measure `μ.restrict s`.  Since `ℝ` is second countable,
a.e.-*strong* measurability on `μ.restrict s` is the same as a.e.-measurability,
which gives the claim.
-/

namespace Work.BoseSym.Bridge

/-- The box `[0,L]^{3N} ⊆ Conf N` is a measurable set. -/
lemma measurableSet_box (N : ℕ) (L : ℝ) : MeasurableSet (BoseGases.box N L) := by
  unfold BoseGases.box
  measurability

theorem aemeas_indicator_of_aesm_on_box {N : ℕ} {L : ℝ} {W : Work.BoseSym.Conf N → ℝ}
    (hW : MeasureTheory.AEStronglyMeasurable W
      (MeasureTheory.volume.restrict (BoseGases.box N L))) :
    AEMeasurable (fun x => (BoseGases.box N L).indicator W x) (Work.BoseSym.volC N) := by
  rw [aemeasurable_indicator_iff (measurableSet_box N L)]
  exact hW.aemeasurable

end Work.BoseSym.Bridge
