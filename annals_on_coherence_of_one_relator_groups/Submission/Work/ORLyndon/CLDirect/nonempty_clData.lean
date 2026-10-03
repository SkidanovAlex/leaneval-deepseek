import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs

namespace Work.ORLyndon.CLDirect

/-- N4's Cohen--Lyndon basis packaged as `CLData`. Sketch: `hu := Work.OROneRel.ne_one_of_not_isProperPower hpp`; `hpp' : ¬ Work.ORLocInd.IsProperPower u` via `Work.ORLocInd.CohenLyndon.isProperPower_bridge hu`; `obtain ⟨e, he⟩ := Work.ORLocInd.FKSKernel.cohenLyndonBasis u hu hpp'`; set `s q := (he q).choose`, fields from `.choose_spec`. -/
theorem nonempty_clData {X : Type*} (u : FreeGroup X)
    (hpp : ¬ Work.OROneRel.IsProperPower u) : Nonempty (Work.ORLyndon.CLDirect.CLData u) := by
  have hu : u ≠ 1 := Work.OROneRel.ne_one_of_not_isProperPower hpp
  have hpp' : ¬ Work.ORLocInd.IsProperPower u :=
    fun h => hpp ((Work.ORLocInd.CohenLyndon.isProperPower_bridge hu).mp h)
  obtain ⟨e, he⟩ := Work.ORLocInd.FKSKernel.cohenLyndonBasis u hu hpp'
  exact ⟨{ e := e,
           s := fun q => (he q).choose,
           mk_s := fun q => (he q).choose_spec.1,
           e_of := fun q => (he q).choose_spec.2 }⟩

end Work.ORLyndon.CLDirect
