import Mathlib
import Submission.Work.Thom.exists_coreMapFibre
import Submission.Work.Thom.exists_continuousLinearEquiv_euclideanSpace_prod
import Submission.Work.Thom.whitney

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
# The Whitney sum with a trivial summand, in the standard fibre

The Chern recursion `Work.Thom.chernClass` is stated for complex bundles whose model fibre is
*exactly* `EuclideanSpace ℂ (Fin m)`, while the Whitney sum `Work.Thom.bundleSum Z ε¹` of a bundle
of rank `m` with the trivial bundle of rank `1` has the *product* fibre
`EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)`.  This module supplies the missing
presentation: `Work.Thom.sumEps ι₀ Z` is the sum, transported along the continuous linear
equivalence `EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1) ≃L[ℂ] EuclideanSpace ℂ (Fin (m+1))`
(`Work.Thom.exists_continuousLinearEquiv_euclideanSpace_prod`) with the transport operation of
`Work.Thom.exists_coreMapFibre`.  Its index type is `ι × ι₀` and its fibre is the standard
`EuclideanSpace ℂ (Fin (m+1))`, so the Chern recursion applies to it, and it is isomorphic to the
sum by construction (`Work.Thom.nonempty_bundleIso_sumEps`).

This is the bookkeeping of `README.md` ADDENDUM 23.3 item 2; with it, *stability*
`c_j(Z ⊕ ε¹) = c_j(Z)` is a statement about `Work.Thom.sumEps ι₀ Z`, whose proof needs only
isomorphism-invariance of the Chern classes (`Work.Thom.chernClass_homeo`) plus the explicit
isomorphism `Q|_A ≅ π_A^*Z` over the locus `A = {u ≠ 0}` on which the tautological quotient is
canonically the pullback of `Z` (see ADDENDUM 23.3 and 23.4).
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **The standard identification of the product fibre `ℂ^m × ℂ` with `ℂ^{m+1}`**, used to present
the Whitney sum `Z ⊕ ε¹` in the standard fibre `EuclideanSpace ℂ (Fin (m+1))`
(`Work.Thom.exists_continuousLinearEquiv_euclideanSpace_prod`). -/
noncomputable def prodFinEquiv (m : ℕ) :
    (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) ≃L[ℂ]
      EuclideanSpace ℂ (Fin (m + 1)) :=
  Classical.choice (exists_continuousLinearEquiv_euclideanSpace_prod m)

/-- **The Whitney sum `Z ⊕ ε¹` of a complex bundle `Z` of rank `m` with the trivial complex line
bundle, presented in the *standard* fibre `EuclideanSpace ℂ (Fin (m+1))`** (index type `ι × ι₀`),
so that the Chern recursion of `Submission/Work/Thom/chernClass.lean` applies to it. -/
noncomputable def sumEps (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) (ι × ι₀) :=
  Classical.choose (exists_coreMapFibre
    (e := prodFinEquiv m)
    (bundleSum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)))

/-- The base sets of `Work.Thom.sumEps` are those of the Whitney sum
`Work.Thom.bundleSum Z ε¹`. -/
theorem sumEps_baseSet (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (sumEps ι₀ Z).baseSet
      = (bundleSum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)).baseSet :=
  (Classical.choose_spec (exists_coreMapFibre
    (e := prodFinEquiv m)
    (bundleSum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)))).1

/-- The index map of `Work.Thom.sumEps` is that of the Whitney sum `Work.Thom.bundleSum Z ε¹`. -/
theorem sumEps_indexAt (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    (sumEps ι₀ Z).indexAt
      = (bundleSum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)).indexAt :=
  (Classical.choose_spec (exists_coreMapFibre
    (e := prodFinEquiv m)
    (bundleSum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)))).2.1

/-- The transition functions of `Work.Thom.sumEps`: those of the Whitney sum, conjugated by the
standard identification `Work.Thom.prodFinEquiv` of the product fibre with
`EuclideanSpace ℂ (Fin (m+1))`. -/
theorem sumEps_coordChange (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i j : ι × ι₀) (x : B) :
    (sumEps ι₀ Z).coordChange i j x
      = (prodFinEquiv m : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
            EuclideanSpace ℂ (Fin (m + 1))).comp
          (((bundleSum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)).coordChange
            i j x).comp
            ((prodFinEquiv m).symm : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
              (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)))) :=
  (Classical.choose_spec (exists_coreMapFibre (e := prodFinEquiv m)
    (bundleSum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)))).2.2.1 i j x

/-- **`Work.Thom.sumEps ι₀ Z` is isomorphic to the Whitney sum `Z ⊕ ε¹`** (so its isomorphism class
is that of `Z ⊕ ε¹`). -/
theorem nonempty_bundleIso_sumEps (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Nonempty (BundleIso
      (bundleSum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀))
      (sumEps ι₀ Z)) :=
  (Classical.choose_spec (exists_coreMapFibre
    (e := prodFinEquiv m)
    (bundleSum Z (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₀)))).2.2.2

end

end Work.Thom
