import Mathlib
import Submission.Work.Thom.complexification
import Submission.Work.Thom.realification
import Submission.Work.Thom.whitney
import Submission.Work.Thom.sumEps

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Stability of the Pontryagin classes: the real splitting

This module contains the one *explicit* object on which the real (Pontryagin) incarnation of
stability rests: the **real splitting**

`Work.Thom.rhoR k : ℝ^k × ℝ¹ ≃L[ℝ] ℝ^{k+1}`,

namely `EuclideanSpace.finAddEquivProd.symm`.  The rest of the development
(`Submission/Work/Thom/realSumStable.lean`) uses

* the **complexification** `Work.Thom.rhoC k : ℂ^k × ℂ¹ ≃L[ℂ] ℂ^{k+1}` of `rhoR k`, characterised
  by `rhoC (cxOfReal u, cxOfReal v) = cxOfReal (rhoR k (u, v))` and by the *intertwining* identity
  `cxTrans (rhoR (T × id) rhoR⁻¹) = rhoC ((cxTrans T) × id) rhoC⁻¹` (proved by delegation, as
  `Work.Thom.exists_rhoC_compat`), and
* the two standard-fibre presentations `sumEpsR ι₀ Z` (real) and `sumEpsC ι₀ W` (complex) of the
  sum with a trivial line,

to obtain the stability of the (complexified) real sum, and hence `p₁(E ⊕ ε¹) = p₁(E)`.
-/

namespace Work.Thom

open Work.TangentClasses

open scoped RealInnerProductSpace

noncomputable section

/-- **The explicit real splitting `ℝ^k × ℝ¹ ≃L[ℝ] ℝ^{k+1}`** (the coordinate concatenation of
Mathlib).  It is the real counterpart of `Work.Thom.prodFinEquiv` — which is *opaque*
(`Classical.choose`), so it cannot be used for any comparison with the complexification; this one is
explicit, which is what makes the complexification comparison below possible. -/
noncomputable def rhoR (k : ℕ) :
    (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := 1)).symm

/-- The inverse of the real splitting, as a continuous linear map. -/
noncomputable def rhoRsymm (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 1)) :=
  (rhoR k).symm

@[simp] theorem rhoRsymm_apply (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    rhoRsymm k v = (rhoR k).symm v := rfl

end

end Work.Thom
