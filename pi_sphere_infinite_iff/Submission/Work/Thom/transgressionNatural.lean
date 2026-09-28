import Mathlib
import Submission.Work.Thom.transgressionPiAux
import Submission.Work.Thom.transgressionNaturalDefs

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Thom

/-- Naturality of the honest Mayer--Vietoris connecting map (`Work.Cohomology.honestDelta`) under
a continuous map `f : X → Y` and the preimage cover: the square

`H^k(U∩V) --δ_Y--> H^{k+1}(Y)`  and  `H^k(U∩V) --R--> H^k(f⁻¹U∩f⁻¹V) --δ_X--> H^{k+1}(X)`

commutes, where `R` is the pullback along the restriction of `f` to the overlap. -/
theorem transgressionNatural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (k : ℕ) :
    (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.honestDelta (TopCat.of Y) (∅ : Set Y) U V hU hV hcov k)
        (Work.Thom.relPb f (k + 1)))
      = (CategoryTheory.CategoryStruct.comp
          (Work.Thom.relCohMap (Work.Thom.fPieceProj f U V) (∅ : Set ↥(f ⁻¹' U ∩ f ⁻¹' V))
            (∅ : Set ↥(U ∩ V)) (fun _ h => h) ℤ k)
          (Work.Cohomology.honestDelta (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
            (hU.preimage f.continuous) (hV.preimage f.continuous)
            (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) k)) := by
  have hcovX : f ⁻¹' U ∪ f ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, hcov, Set.preimage_univ]
  rw [Work.Cohomology.honestDelta, Work.Cohomology.honestDelta]
  simp only [Category.assoc]
  rw [cmpXIso_inv_relPb f hU hV hcov k]
  have hd : (Work.Cohomology.hmv_shortExact (TopCat.of Y) (∅ : Set Y) U V).δ k (k + 1)
        (Work.Cohomology.relCohMVUpRel k)
        ≫ HomologicalComplex.homologyMap (dTop f U V) (k + 1)
        ≫ (Work.Cohomology.cmpXIso (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
            (hU.preimage f.continuous) (hV.preimage f.continuous) hcovX (k + 1)).inv
      = HomologicalComplex.homologyMap (dUV f U V) k
        ≫ (Work.Cohomology.hmv_shortExact (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)).δ k (k + 1)
            (Work.Cohomology.relCohMVUpRel k)
        ≫ (Work.Cohomology.cmpXIso (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
            (hU.preimage f.continuous) (hV.preimage f.continuous) hcovX (k + 1)).inv := by
    rw [← Category.assoc, delta_natural f U V k, Category.assoc]
  rw [hd]
  have hw : (Work.Cohomology.cmpWIso (TopCat.of Y) (∅ : Set Y) U V k).hom
        ≫ HomologicalComplex.homologyMap (dUV f U V) k
        ≫ ((Work.Cohomology.hmv_shortExact (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)).δ k (k + 1)
              (Work.Cohomology.relCohMVUpRel k)
            ≫ (Work.Cohomology.cmpXIso (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
                (hU.preimage f.continuous) (hV.preimage f.continuous) hcovX (k + 1)).inv)
      = Work.Thom.relCohMap (Work.Thom.fPieceProj f U V) (∅ : Set ↥(f ⁻¹' U ∩ f ⁻¹' V))
          (∅ : Set ↥(U ∩ V)) (fun _ h => h) ℤ k
        ≫ (Work.Cohomology.cmpWIso (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V) k).hom
        ≫ ((Work.Cohomology.hmv_shortExact (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)).δ k (k + 1)
              (Work.Cohomology.relCohMVUpRel k)
            ≫ (Work.Cohomology.cmpXIso (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
                (hU.preimage f.continuous) (hV.preimage f.continuous) hcovX (k + 1)).inv) := by
    rw [← Category.assoc, ← cmpWIso_natural f k, Category.assoc]
  rw [hw]

end Work.Thom
