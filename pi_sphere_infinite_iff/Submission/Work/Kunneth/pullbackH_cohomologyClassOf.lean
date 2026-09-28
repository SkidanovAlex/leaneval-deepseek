import Mathlib
import Submission.Work.Kunneth.CrossH
import Submission.Work.Cohomology.pxTools

/-!
# Naturality of the cohomology class of a cocycle under a pullback

`Work.Kunneth.pullbackH X Y f n` is the map `H^n(Y;ℤ) → H^n(X;ℤ)` induced by a simplicial map
`f : X ⟶ Y`: it is the `n`-th homology map of the dual of the chain map `C_*(X) ⟶ C_*(Y)`
(`Work.Cohomology.dualComplexMap`).  This file computes it on the cohomology class of a cocycle:
the pullback of the class of `β` is the class of the pulled back cochain
`Work.Cohomology.Kunneth.ssetPullback X Y f n β`.

The proof is the usual zig-zag: naturality of `homologyπ` under a map of complexes reduces the
claim to the equality of the cycles representing the two classes, which is checked after applying
the (injective) inclusion of the cycles.  The computation is carried out for an arbitrary map of
singular cochain complexes
(`homologyMap_cohomologyClassOf`) and then specialised to the dual of the singular chain map.

## Main results

* `Work.Kunneth.homologyMap_cohomologyClassOf` — the general computation;
* `Work.Kunneth.pullbackH_cohomologyClassOf` — the pullback of a cohomology class is the class of
  the pulled back cocycle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial

namespace Work.Kunneth

noncomputable section

/-- **Naturality of the cohomology class of a cocycle.**  For a map
`φ : C^*(Y) ⟶ C^*(X)` of singular cochain complexes over `ℤ` and cochains `β`, `β'` with
`(φ.f n).hom β = β'`, the cohomology class of the cocycle `β` is mapped to the class of the
cocycle `β'`. -/
lemma homologyMap_cohomologyClassOf (X Y : SSet) (n : ℕ)
    (φ : Work.Cohomology.SSetCochainComplex ℤ Y ⟶ Work.Cohomology.SSetCochainComplex ℤ X)
    (β : Work.Cohomology.Cochain ℤ Y n) (β' : Work.Cohomology.Cochain ℤ X n)
    (hβ : Work.Cohomology.cochainDiff ℤ Y β = 0)
    (hβ' : Work.Cohomology.cochainDiff ℤ X β' = 0)
    (hφ : (φ.f n).hom β = β') :
    (HomologicalComplex.homologyMap φ n).hom
        ((Work.Cohomology.SSetCochainComplex ℤ Y).homologyπ n
          (Work.Cohomology.cocycleOf ℤ Y β hβ))
      = (Work.Cohomology.SSetCochainComplex ℤ X).homologyπ n
          (Work.Cohomology.cocycleOf ℤ X β' hβ') := by
  have h1 : (Work.Cohomology.SSetCochainComplex ℤ Y).homologyπ n
        ≫ HomologicalComplex.homologyMap φ n
      = HomologicalComplex.cyclesMap φ n
        ≫ (Work.Cohomology.SSetCochainComplex ℤ X).homologyπ n :=
    HomologicalComplex.homologyπ_naturality φ n
  have h2 := congrArg (fun (g : (Work.Cohomology.SSetCochainComplex ℤ Y).cycles n ⟶
      (Work.Cohomology.SSetCochainComplex ℤ X).homology n) =>
      ModuleCat.Hom.hom g (Work.Cohomology.cocycleOf ℤ Y β hβ)) h1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have hkey : ModuleCat.Hom.hom (HomologicalComplex.cyclesMap φ n)
        (Work.Cohomology.cocycleOf ℤ Y β hβ)
      = Work.Cohomology.cocycleOf ℤ X β' hβ' := by
    refine Work.Cohomology.iCycles_injective ℤ X n ?_
    have hii := congrArg (fun (g : (Work.Cohomology.SSetCochainComplex ℤ Y).cycles n ⟶
        (Work.Cohomology.SSetCochainComplex ℤ X).X n) =>
        ModuleCat.Hom.hom g (Work.Cohomology.cocycleOf ℤ Y β hβ))
      (HomologicalComplex.cyclesMap_i φ n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hii
    rw [hii, Work.Cohomology.iCycles_cocycleOf, Work.Cohomology.iCycles_cocycleOf]
    exact hφ
  exact h2.trans (congrArg (fun w => ModuleCat.Hom.hom
    ((Work.Cohomology.SSetCochainComplex ℤ X).homologyπ n) w) hkey)

/-- **The pullback of a cohomology class is the class of the pulled back cocycle.** -/
theorem pullbackH_cohomologyClassOf (X Y : SSet) (f : X ⟶ Y) (n : ℕ)
    (β : Work.Cohomology.Cochain ℤ Y n) (hβ : Work.Cohomology.cochainDiff ℤ Y β = 0) :
    Work.Kunneth.pullbackH X Y f n (Work.Cohomology.cohomologyClassOf ℤ Y β hβ)
      = Work.Cohomology.cohomologyClassOf ℤ X
          (Work.Cohomology.Kunneth.ssetPullback X Y f n β)
          (Work.Cohomology.pxSsetPullback_cocycle X Y f n β hβ) := by
  let φ : Work.Cohomology.SSetCochainComplex ℤ Y ⟶ Work.Cohomology.SSetCochainComplex ℤ X :=
    Work.Cohomology.dualComplexMap ℤ (sChain X) (sChain Y) (SSet.chainComplexMap f zz)
  change (HomologicalComplex.homologyMap φ n).hom
      ((Work.Cohomology.SSetCochainComplex ℤ Y).homologyπ n
        (Work.Cohomology.cocycleOf ℤ Y β hβ))
    = (Work.Cohomology.SSetCochainComplex ℤ X).homologyπ n
        (Work.Cohomology.cocycleOf ℤ X
          (Work.Cohomology.Kunneth.ssetPullback X Y f n β)
          (Work.Cohomology.pxSsetPullback_cocycle X Y f n β hβ))
  exact homologyMap_cohomologyClassOf X Y n φ β
    (Work.Cohomology.Kunneth.ssetPullback X Y f n β) hβ
    (Work.Cohomology.pxSsetPullback_cocycle X Y f n β hβ) rfl

end

end Work.Kunneth
