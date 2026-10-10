import Mathlib.FieldTheory.IsSepClosed
import Submission.NK.TameStructureDeep.Tame.UnramifiedNoPow
import Submission.NK.TameStructureDeep.Tame.isGalois_tameClosure
import Submission.NK.TameStructureDeep.Tame.isTameFrobeniusLift_correctedWildInertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K'] [IsSepClosure κ K']

/-- **The corrected wild inertia is normal in `G_κ`**: it is the fixing subgroup of the Galois
extension `κ^{tr}/κ`. -/
theorem correctedWildInertia_normal (p : ℕ) (hp : p.Prime) {π : κ} (hπ : π ≠ 0) :
    (correctedWildInertia (K' := K') p π).Normal := by
  haveI := isGalois_tameClosure (K' := K') p hp hπ
  exact (show (tameClosure (K' := K') p π).fixingSubgroup.Normal from inferInstance)

end

end NK.TameStructureDeep.Tame
