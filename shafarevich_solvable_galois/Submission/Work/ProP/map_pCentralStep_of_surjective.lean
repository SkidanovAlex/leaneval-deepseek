import Mathlib
import Submission.Work.ProP.Defs
import Submission.Work.Shrinking.map_pCentralSeries_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- A surjective homomorphism transports one step of the descending `p`-central series of an
arbitrary subgroup: `(H^p [H, P]).map f = (H.map f)^p [H.map f, Q]`.  Surjectivity is needed
only to replace `⊤.map f` by `⊤` (the `p`-power part and the commutator part already commute
with images under an arbitrary homomorphism). -/
theorem map_pCentralStep_of_surjective (p : ℕ) {P Q : Type*} [Group P] [Group Q] (f : P →* Q)
    (hf : Function.Surjective f) (H : Subgroup P) :
    (Work.Shrinking.pCentralStep p H).map f = Work.Shrinking.pCentralStep p (H.map f) := by
  rw [Work.Shrinking.pCentralStep, Work.Shrinking.pCentralStep, Subgroup.map_sup,
    Work.Shrinking.map_powSubgroup, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective f hf]

end Work.ProP
