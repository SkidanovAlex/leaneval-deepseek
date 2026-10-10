import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Submission.NK.LocalAnabelian.GaloisCorrespondence.numIndexClosedSubgroups_eq_natCard_finrank_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

set_option maxHeartbeats 800000

namespace NK.LocalAnabelian

noncomputable section

variable {k K' : Type*} [Field k] [Field K'] [Algebra k K']

/-- **Index-`p` subgroups are degree-`p` subextensions**, given that all index-`p`
subgroups of the absolute Galois group are closed in the Krull topology. -/
theorem numIndexSubgroups_eq_natCard_finrank_eq [IsGalois k K'] (p : ℕ)
    (hclosed : ∀ H : Subgroup (Gal(K'/k)), H.index = p → IsClosed (H : Set (Gal(K'/k)))) :
    numIndexSubgroups p (Gal(K'/k)) =
      Nat.card {L : IntermediateField k K' // Module.finrank k L = p} := by
  rw [← GaloisCorrespondence.numIndexClosedSubgroups_eq_natCard_finrank_eq (k := k) (K' := K') p]
  unfold numIndexSubgroups
  exact Nat.card_congr
    { toFun := fun H => ⟨⟨H.1, hclosed H.1 H.2⟩, H.2⟩
      invFun := fun H => ⟨(H.1 : ClosedSubgroup (Gal(K'/k))).toSubgroup, H.2⟩
      left_inv := fun H => Subtype.ext rfl
      right_inv := fun H => Subtype.ext rfl }

end

end NK.LocalAnabelian
