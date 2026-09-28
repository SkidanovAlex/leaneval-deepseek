import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGlue

/-!
# `relChainsRPairMap` depends only on the continuous map

The relative chain map of a map of pairs is determined by the underlying continuous map; this is the
ingredient that lets the assembly of the cell step identify the composite of the pair map with a
section and the pair map with the identity *at the level of the chain complexes*, rather than having
to rewrite inside the dependent `MapsTo` argument.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.Csr

noncomputable section

/-- `cokernel.map` depends only on the maps. -/
theorem csrCokernelMap_congr {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y X' Y' : C} (f : X ⟶ Y) [HasCokernel f] (f' : X' ⟶ Y') [HasCokernel f']
    {p₁ p₂ : X ⟶ X'} {q₁ q₂ : Y ⟶ Y'} (hp : p₁ = p₂) (hq : q₁ = q₂)
    (w₁ : f ≫ q₁ = p₁ ≫ f') (w₂ : f ≫ q₂ = p₂ ≫ f') :
    cokernel.map f f' p₁ q₁ w₁ = cokernel.map f f' p₂ q₂ w₂ := by
  cases hp; cases hq; rfl

/-- `relChainsRPairMap` depends only on the continuous map. -/
theorem relChainsRPairMap_congr' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} {g g' : C(X, Y)} (h : g = g')
    (hg : Set.MapsTo g A B) (hg' : Set.MapsTo g' A B) :
    Work.Serre.relChainsRPairMap A B g hg = Work.Serre.relChainsRPairMap A B g' hg' := by
  unfold Work.Serre.relChainsRPairMap Work.Serre.csrRelMapOf
  apply csrCokernelMap_congr (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A)
    (Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B)
  · refine congrArg (fun φ => Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B) φ) ?_
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (congrFun (congrArg DFunLike.coe h) x.1)
  · refine congrArg (fun φ => Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) φ) ?_
    exact congrArg TopCat.ofHom h

end

end Work.Serre.Csr
