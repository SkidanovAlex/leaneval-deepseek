import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs

namespace Work.ORLyndon.CLDirect

/-- `clPi` on a generator. Sketch: `MonoidAlgebra.of_apply`, `mapDomainRingHom_apply`, `mapDomain_single`; compare with `Work.ORLyndon.presentAlg_of`. -/
theorem clPi_of {X : Type*} [DecidableEq X] {K : Type*} [Field K] {u : FreeGroup X}
    (D : Work.ORLyndon.CLDirect.CLData u) (l : ℕ)
    (g : FreeGroup (FreeGroup X ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup X)))) :
    Work.ORLyndon.CLDirect.clPi (K := K) D l (MonoidAlgebra.of K _ g) =
      MonoidAlgebra.of K _ (Work.ORLyndon.presentRho (u ^ l) (D.e g : FreeGroup X)) := by
  rw [Work.ORLyndon.CLDirect.clPi, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.of_apply, MonoidAlgebra.mapDomain_single]
  rfl

end Work.ORLyndon.CLDirect
