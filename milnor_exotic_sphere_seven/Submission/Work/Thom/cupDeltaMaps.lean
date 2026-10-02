import Mathlib
import Submission.Work.Thom.cupDeltaInfra
import Submission.Work.Thom.cupRightLM_dcomm
import Submission.Work.Thom.tau1LM_dcomm
import Submission.Work.Thom.relRestrCochain_dcocycle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Thom

noncomputable section

/-- **The top component of the transgression morphism**: the cup product with a relative cocycle,
descended to the relative small cochains of the cover. -/
noncomputable def tau1 (X : TopCat) (A U V : Set X) (n : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (ht : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0) :
    Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X ∅ U V) ⟶
      Tsq.shK (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)) n :=
  HomologicalComplex.Hom.mk (fun p => tau1LM X A U V n p t) (by
    intro i j hij
    rw [ComplexShape.up_Rel] at hij
    subst hij
    exact Work.Thom.tau1LM_dcomm X A U V n i t ht)

/-- The commutation condition for the `U`-piece is satisfied. -/
theorem cupComm_U (X : TopCat) (A U V : Set X) (n : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (ht : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0) :
    CupComm (relRestrCochain A U n t) (Work.Cohomology.interAU ∅ U) :=
  fun i => Work.Thom.cupRightLM_dcomm (relRestrCochain A U n t)
    (Work.Thom.relRestrCochain_dcocycle A U n t ht) (Work.Cohomology.interAU ∅ U) i

/-- The commutation condition for the `V`-piece is satisfied. -/
theorem cupComm_V (X : TopCat) (A U V : Set X) (n : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (ht : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0) :
    CupComm (relRestrCochain A V n t) (Work.Cohomology.interAU ∅ V) :=
  fun i => Work.Thom.cupRightLM_dcomm (relRestrCochain A V n t)
    (Work.Thom.relRestrCochain_dcocycle A V n t ht) (Work.Cohomology.interAU ∅ V) i

/-- The commutation condition for the overlap is satisfied. -/
theorem cupComm_W (X : TopCat) (A U V : Set X) (n : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (ht : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0) :
    CupComm (relRestrCochain A (U ∩ V) n t) (Work.Cohomology.interAU ∅ (U ∩ V)) :=
  fun i => Work.Thom.cupRightLM_dcomm (relRestrCochain A (U ∩ V) n t)
    (Work.Thom.relRestrCochain_dcocycle A (U ∩ V) n t ht)
    (Work.Cohomology.interAU ∅ (U ∩ V)) i

end

end Work.Thom
