import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGeom
import Submission.Work.Serre.csrCompress
import Submission.Work.Serre.csrRelIso
import Submission.Work.Serre.csrExcisionRat
import Submission.Work.Stems.Engine.CoeffTransfer
import Submission.Work.Cohomology.relChainsMapOf_comp

/-!
# Assembly of the rational cell step

This file reduces the rational cell step `Work.Serre.cellStepRelHomologyIso` to the "cell-wise"
comparison over the union of the open half-balls around the cell centres (the hypothesis `hmid`).

The reduction is the chain of maps of pairs

`(E, q⁻¹Y') → (E, q⁻¹V) → (Z, V)`,

* the first is an isomorphism on rational homology because the pair `(q⁻¹V, q⁻¹Y')` has vanishing
  relative rational homology (`Work.Serre.csrCompress` and `Work.Serre.csrRelIso`);
* the second is `hmid`;
* the square with the map `(E, q⁻¹Y') → (Z, Y') → (Z, V)` commutes by functoriality.

The functoriality lemmas for the relative pair maps are reproduced here (with the prefix `csrAsm_`)
so that this file only depends on the stable modules `csrDefs`, `csrGeom`, `csrCompress`,
`csrRelIso`, `csrExcisionRat`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

noncomputable section

/-! ## Functoriality of the relative pair maps -/

/-- `cokernel.map` depends only on the two horizontal maps. -/
theorem csrAsm_cokernelMap_congr {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y X' Y' : C} (f : X ⟶ Y) [HasCokernel f] (f' : X' ⟶ Y') [HasCokernel f']
    {p₁ p₂ : X ⟶ X'} {q₁ q₂ : Y ⟶ Y'} (hp : p₁ = p₂) (hq : q₁ = q₂)
    (w₁ : f ≫ q₁ = p₁ ≫ f') (w₂ : f ≫ q₂ = p₂ ≫ f') :
    cokernel.map f f' p₁ q₁ w₁ = cokernel.map f f' p₂ q₂ w₂ := by
  cases hp; cases hq; rfl

/-- **Composition of the relative chain maps of a composite of maps of pairs.** -/
theorem csrAsm_pair_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z}
    (g : C(X, Y)) (g' : C(Y, Z)) (hg : Set.MapsTo g A B) (hg' : Set.MapsTo g' B C)
    {hg'' : Set.MapsTo (g'.comp g) A C} :
    relChainsRPairMap A B g hg ≫ relChainsRPairMap B C g' hg'
      = relChainsRPairMap A C (g'.comp g) hg'' := by
  apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A))).1
  rw [← Category.assoc, cokernel_π_relChainsRPairMap, Category.assoc,
    cokernel_π_relChainsRPairMap, cokernel_π_relChainsRPairMap]
  rw [← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains, ← TopCat.ofHom_comp]

/-- `relChainsRPairMap` depends only on the continuous map. -/
theorem csrAsm_pair_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} {g g' : C(X, Y)} (h : g = g')
    (hg : Set.MapsTo g A B) (hg' : Set.MapsTo g' A B) :
    relChainsRPairMap A B g hg = relChainsRPairMap A B g' hg' := by
  apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A))).1
  rw [cokernel_π_relChainsRPairMap, cokernel_π_relChainsRPairMap]
  exact congrArg (fun φ => Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) φ
    ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Y) B)) (congrArg TopCat.ofHom h)

/-- The relative chain map of the identity map of pairs, with an arbitrary `MapsTo` proof. -/
theorem csrAsm_pair_id {X : Type} [TopologicalSpace X] (A : Set X)
    (hg : Set.MapsTo (ContinuousMap.id X) A A) :
    relChainsRPairMap A A (ContinuousMap.id X) hg
      = 𝟙 (Work.StemsB.relChainsR ℚ (TopCat.of X) A) := by
  apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A))).1
  rw [cokernel_π_relChainsRPairMap, Category.comp_id]
  have h1 : Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of X)
      (TopCat.ofHom (ContinuousMap.id X)) =
      𝟙 (Work.Cohomology.singularChains ℚ (TopCat.of X)) :=
    CategoryTheory.Functor.map_id _ _
  rw [h1, Category.id_comp]

/-! ## The assembly -/

/-- **Assembly of the rational cell step.**  Assuming the comparison of the preimage pair over
`V = csrV` (the complement of the cell centres) is an isomorphism on rational homology in degrees
`≤ N`, so is the map of pairs `(E, q⁻¹Y') → (Z, Y')`. -/
theorem csrAssembly (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (N : ℕ)
    (hmid : ∀ m : ℕ, m ≤ N →
      CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (X := E)
          (Y := Work.RatHurewicz.attachCells n Y ι f)
          (q ⁻¹' csrV n Y ι f) (csrV n Y ι f) q (by intro x hx; exact hx)) m))
    (i : ℕ) (hi : i ≤ N) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) i) := by
  classical
  have hcomp := csrCompress n Y ι f q hq
  -- transfer the two compression vanishings to `ℚ`
  have hV : ∀ m : ℕ, CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(csrV n Y ι f))
        {x : ↥(csrV n Y ι f) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈
          Set.range (Work.RatHurewicz.attachIncl n Y ι f)}).homology m) :=
    fun m => Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ m (hcomp m).1
  have hB : ∀ m : ℕ, CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' csrV n Y ι f))
        {x : ↥(q ⁻¹' csrV n Y ι f) | (x : E) ∈ q ⁻¹' (Set.range
          (Work.RatHurewicz.attachIncl n Y ι f))}).homology m) :=
    fun m => Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains _ _ m (hcomp m).2
  -- the inclusion `Y' ⊆ V` and its preimage
  have hYV : Set.range (Work.RatHurewicz.attachIncl n Y ι f) ⊆ csrV n Y ι f := by
    rintro z ⟨y, rfl⟩ ⟨k, hk⟩
    refine Work.RatHurewicz.cellOrigin_notMem_range_attachIncl (f := f) k ?_
    change csrCentre n Y ι f k ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)
    exact hk ▸ ⟨y, rfl⟩
  have hAB : (q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f))) ⊆ q ⁻¹' csrV n Y ι f :=
    Set.preimage_mono hYV
  -- the two comparison isomorphisms and the middle map
  have h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsRPairMap (q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
        (q ⁻¹' csrV n Y ι f) (ContinuousMap.id E) hAB) i) :=
    csrRelIso _ _ hAB hB i
  have h2 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsRPairMap (q ⁻¹' csrV n Y ι f) (csrV n Y ι f) q
        (by intro x hx; exact hx)) i) :=
    hmid i hi
  have h3 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relChainsRPairMap (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) (csrV n Y ι f)
        (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) hYV) i) :=
    csrRelIso _ _ hYV hV i
  -- `cellStepMap` is the relative pair map of `q`
  have hcs : Work.Serre.cellStepMap n ι f q
      = relChainsRPairMap (q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
          (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) q (by intro x hx; exact hx) := by
    unfold Work.Serre.cellStepMap Work.Serre.cellStepRestrict relChainsRPairMap csrRelMapOf
    apply csrAsm_cokernelMap_congr
    · refine congrArg (fun φ => Work.Cohomology.chainMap ℚ
        (TopCat.of {e : E | q e ∈ Set.range (Work.RatHurewicz.attachIncl n Y ι f)})
        (TopCat.of (Set.range (Work.RatHurewicz.attachIncl n Y ι f))) φ) ?_
      exact congrArg TopCat.ofHom (ContinuousMap.ext (fun x => Subtype.ext rfl))
    · rfl
  -- the comparison square
  have hsq : Work.Serre.cellStepMap n ι f q
        ≫ relChainsRPairMap (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) (csrV n Y ι f)
            (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) hYV
      = relChainsRPairMap (q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
            (q ⁻¹' csrV n Y ι f) (ContinuousMap.id E) hAB
        ≫ relChainsRPairMap (q ⁻¹' csrV n Y ι f) (csrV n Y ι f) q (by intro x hx; exact hx) := by
    calc Work.Serre.cellStepMap n ι f q
          ≫ relChainsRPairMap (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) (csrV n Y ι f)
              (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) hYV
        = relChainsRPairMap (q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
              (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) q (by intro x hx; exact hx)
          ≫ relChainsRPairMap (Set.range (Work.RatHurewicz.attachIncl n Y ι f))
              (csrV n Y ι f) (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) hYV := by
            rw [hcs]
      _ = relChainsRPairMap (q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
              (csrV n Y ι f)
              ((ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)).comp q)
              (fun x hx => hYV hx) :=
            csrAsm_pair_comp q (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f))
              (by intro x hx; exact hx) hYV
      _ = relChainsRPairMap (q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
              (csrV n Y ι f) (q.comp (ContinuousMap.id E)) (fun x hx => hYV hx) :=
            csrAsm_pair_congr (ContinuousMap.ext (fun x => rfl)) _ _
      _ = relChainsRPairMap (q ⁻¹' (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
              (q ⁻¹' csrV n Y ι f) (ContinuousMap.id E) hAB
          ≫ relChainsRPairMap (q ⁻¹' csrV n Y ι f) (csrV n Y ι f) q (by intro x hx; exact hx) :=
            (csrAsm_pair_comp (ContinuousMap.id E) q hAB (by intro x hx; exact hx)
              (hg'' := fun x hx => hYV hx)).symm
  -- conclude at the level of homology
  have hsq' := congrArg (fun φ => HomologicalComplex.homologyMap φ i) hsq
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq'
  haveI := h1
  haveI := h2
  haveI := h3
  have hfinal : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) i
        ≫ HomologicalComplex.homologyMap
            (relChainsRPairMap (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) (csrV n Y ι f)
              (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) hYV) i) := by
    rw [hsq']; infer_instance
  exact CategoryTheory.IsIso.of_isIso_comp_right
    (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) i)
    (HomologicalComplex.homologyMap
      (relChainsRPairMap (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) (csrV n Y ι f)
        (ContinuousMap.id (Work.RatHurewicz.attachCells n Y ι f)) hYV) i)

end

end Work.Serre
