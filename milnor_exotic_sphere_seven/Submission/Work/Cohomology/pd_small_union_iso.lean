import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.relMV_quasiIso
import Submission.Work.Cohomology.pd_good

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The small chains of a cover inside the union

Let `M` be a topological space, `U, V ⊆ M` open subsets and `C^{U,V}_*(M)` the small chain complex
of the pair `(U, V)` (`Submission/Work/Cohomology/SmallChains.lean`), whose simplices are those
whose image lies in `U` or in `V`.  Every such simplex has image in `U ∪ V`, so it can be
*corestricted* to a simplex of the subspace `U ∪ V`; on chains this gives a map

`Φ : C^{U,V}_*(M) ⟶ C_*(U ∪ V)`.

This file proves `Work.Cohomology.pd_small_union_iso`: `Φ` exists, is compatible with the inclusion
`smallToSing U V` of the small chains into the singular chains of `M` (via the inclusion
`U ∪ V ⊆ M`), induces an isomorphism on homology, and is compatible with the maps
`smallOfU`, `smallOfV` of the Mayer–Vietoris sequence (with the inclusions `U ↪ U ∪ V`,
`V ↪ U ∪ V`).

The isomorphism on homology is the small-simplices theorem applied to the cover of the subspace
`U ∪ V` by the two (open) traces `U' = {x ∈ U ∪ V | x ∈ U}` and `V'`; the identification of the
small simplices of `M` with the small simplices of `(U', V')` inside `U ∪ V` is the isomorphism of
simplicial sets `smallUnionToSmall`.

## Contents

* `smallUnionToSing` — the corestriction simplicial map `small(U,V) ⟶ Simp(U ∪ V)`;
* `smallUnionTraceU`, `smallUnionTraceV` — the traces of `U`, `V` on the subspace `U ∪ V`;
* `smallUnionToSmall`, `smallUnionOfSmall` — inverse isomorphisms `small(U,V) ≅ small(U', V')`;
* `smallUnionToSing_comp_incl`, `smallLiftU_comp_smallUnion`, `smallLiftV_comp_smallUnion` —
  compatibility of the corestriction with the natural inclusions;
* `pd_small_union_iso` — the main statement.
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {M : TopCat} (U V : Set M)

/-! ## The corestriction of a small simplex to the union -/

/-- The `n`-simplices of the corestriction `small(U,V) ⟶ Simp(U ∪ V)`: a small simplex of `M` is
sent to the same simplex with codomain restricted to the union `U ∪ V`. -/
def smallUnionToApp (n : SimplexCategoryᵒᵖ) :
    (smallSSet U V).obj n ⟶ (TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M))).obj n :=
  ↾ fun (x : (smallSSet U V).obj n) =>
    (TopCat.toSSetObjEquiv (TopCat.of (U ∪ V : Set M)) n).symm
      ⟨fun z => ⟨(TopCat.toSSetObjEquiv M n x.1) z, by
          rcases x.2 with h | h
          · exact Or.inl (h ⟨z, rfl⟩)
          · exact Or.inr (h ⟨z, rfl⟩)⟩,
       Continuous.subtype_mk (TopCat.toSSetObjEquiv M n x.1).continuous (fun z => by
          rcases x.2 with h | h
          · exact Or.inl (h ⟨z, rfl⟩)
          · exact Or.inr (h ⟨z, rfl⟩))⟩

/-- **The corestriction map** `small(U,V) ⟶ Simp(U ∪ V)`: a small simplex of `M` has image in
`U ∪ V`, so it may be regarded as a simplex of the subspace `U ∪ V`. -/
def smallUnionToSing (U V : Set M) :
    smallSSet U V ⟶ TopCat.toSSet.obj (TopCat.of (U ∪ V : Set M)) where
  app := smallUnionToApp U V
  naturality n m f := by
    ext x
    apply (TopCat.toSSetObjEquiv (TopCat.of (U ∪ V : Set M)) m).injective
    ext z
    rfl

/-! ## The traces of `U` and `V` on the union -/

/-- The trace of `U` on the subspace `U ∪ V`. -/
def smallUnionTraceU : Set (TopCat.of (U ∪ V : Set M)) := {x | (x : M) ∈ U}

/-- The trace of `V` on the subspace `U ∪ V`. -/
def smallUnionTraceV : Set (TopCat.of (U ∪ V : Set M)) := {x | (x : M) ∈ V}

/-! ## Compatibility of the corestriction with the natural inclusions -/

/-- Corestriction followed by the inclusion `U ∪ V ↪ M` is the inclusion of the small simplices
into the singular simplices of `M`. -/
theorem smallUnionToSing_comp_incl :
    smallUnionToSing U V ≫ TopCat.toSSet.map (subtypeIncl M (U ∪ V : Set M))
    = (smallSubcomplex U V).ι := by
  ext n x
  apply (TopCat.toSSetObjEquiv M n).injective
  ext z
  rfl

/-- The map `C_*(U) ⟶ C^{U,V}_*(M)` of the Mayer–Vietoris sequence, followed by the corestriction,
is the chain map induced by the inclusion `U ↪ U ∪ V`. -/
theorem smallLiftU_comp_smallUnion : smallLiftU U V ≫ smallUnionToSing U V
    = TopCat.toSSet.map (pdIncl (U ∪ V) U Set.subset_union_left) := by
  ext n x
  apply (TopCat.toSSetObjEquiv (TopCat.of (U ∪ V : Set M)) n).injective
  ext z
  rfl

/-- The map `C_*(V) ⟶ C^{U,V}_*(M)` of the Mayer–Vietoris sequence, followed by the corestriction,
is the chain map induced by the inclusion `V ↪ U ∪ V`. -/
theorem smallLiftV_comp_smallUnion : smallLiftV U V ≫ smallUnionToSing U V
    = TopCat.toSSet.map (pdIncl (U ∪ V) V Set.subset_union_right) := by
  ext n x
  apply (TopCat.toSSetObjEquiv (TopCat.of (U ∪ V : Set M)) n).injective
  ext z
  rfl

/-! ## The small simplices of `M` and those of the cover of `U ∪ V` -/

/-- The range of the corestriction consists of small simplices of the cover `(U', V')` of the
union. -/
theorem smallUnionToSing_range_le :
    SSet.Subcomplex.range (smallUnionToSing U V)
      ≤ smallSubcomplex (smallUnionTraceU U V) (smallUnionTraceV U V) := by
  intro n y hy
  rw [Subfunctor.range_obj] at hy
  obtain ⟨x, rfl⟩ := hy
  rcases x.2 with h | h
  · left; rintro w ⟨z, rfl⟩; exact h ⟨z, rfl⟩
  · right; rintro w ⟨z, rfl⟩; exact h ⟨z, rfl⟩

/-- A small simplex of the cover `(U', V')` of the union, viewed in `M`, is a small simplex of the
pair `(U, V)`. -/
theorem smallUnionOfFun_range_le :
    SSet.Subcomplex.range ((smallSubcomplex (smallUnionTraceU U V) (smallUnionTraceV U V)).ι
        ≫ TopCat.toSSet.map (subtypeIncl M (U ∪ V : Set M))) ≤ smallSubcomplex U V := by
  intro n y hy
  rw [Subfunctor.range_obj] at hy
  obtain ⟨x, rfl⟩ := hy
  rcases x.2 with h | h
  · left; rintro w ⟨z, rfl⟩; exact h ⟨z, rfl⟩
  · right; rintro w ⟨z, rfl⟩; exact h ⟨z, rfl⟩

/-- **Corestriction to the small simplices of the union**, i.e. the range of `smallUnionToSing`. -/
def smallUnionToSmall :
    smallSSet U V ⟶ smallSSet (smallUnionTraceU U V) (smallUnionTraceV U V) :=
  (smallSubcomplex (smallUnionTraceU U V) (smallUnionTraceV U V)).lift (smallUnionToSing U V)
    (smallUnionToSing_range_le U V)

/-- **The inverse of the corestriction**: a small simplex of the cover `(U', V')` of the union,
viewed in `M`, is a small simplex of `(U, V)`. -/
def smallUnionOfSmall :
    smallSSet (smallUnionTraceU U V) (smallUnionTraceV U V) ⟶ smallSSet U V :=
  (smallSubcomplex U V).lift ((smallSubcomplex (smallUnionTraceU U V) (smallUnionTraceV U V)).ι
    ≫ TopCat.toSSet.map (subtypeIncl M (U ∪ V : Set M))) (smallUnionOfFun_range_le U V)

/-- Viewing a small simplex of the union in `M` and then corestricting it back to the union returns
the original simplex. -/
theorem smallUnionOfSmall_comp : smallUnionOfSmall U V ≫ smallUnionToSing U V
      = (smallSubcomplex (smallUnionTraceU U V) (smallUnionTraceV U V)).ι := by
  ext n x
  apply (TopCat.toSSetObjEquiv (TopCat.of (U ∪ V : Set M)) n).injective
  ext z
  rfl

/-- `smallUnionOfSmall` is a left inverse of `smallUnionToSmall`. -/
theorem smallUnionToSmall_hom_inv : smallUnionToSmall U V ≫ smallUnionOfSmall U V
    = 𝟙 (smallSSet U V) := by
  unfold smallUnionToSmall smallUnionOfSmall
  rw [← cancel_mono (smallSubcomplex U V).ι]
  rw [Category.assoc]
  rw [SSet.Subcomplex.lift_ι]
  rw [← Category.assoc]
  rw [SSet.Subcomplex.lift_ι]
  rw [smallUnionToSing_comp_incl]
  rw [Category.id_comp]

/-- `smallUnionOfSmall` is a right inverse of `smallUnionToSmall`. -/
theorem smallUnionOfSmall_inv_hom : smallUnionOfSmall U V ≫ smallUnionToSmall U V
    = 𝟙 (smallSSet (smallUnionTraceU U V) (smallUnionTraceV U V)) := by
  unfold smallUnionToSmall smallUnionOfSmall
  rw [← cancel_mono (smallSubcomplex (smallUnionTraceU U V) (smallUnionTraceV U V)).ι]
  rw [Category.assoc]
  rw [SSet.Subcomplex.lift_ι]
  rw [show SSet.Subcomplex.lift ((smallSubcomplex (smallUnionTraceU U V) (smallUnionTraceV U V)).ι
        ≫ TopCat.toSSet.map (subtypeIncl M (U ∪ V : Set M))) (smallUnionOfFun_range_le U V)
      ≫ smallUnionToSing U V = (smallSubcomplex (smallUnionTraceU U V) (smallUnionTraceV U V)).ι from
    smallUnionOfSmall_comp U V]
  rw [Category.id_comp]

/-! ## The main statement -/

/-- **The small chains of a cover of `U ∪ V` inside `M`.**

Let `U, V ⊆ M` be open.  There is a chain map `Φ` from the small chains `C^{U,V}_*(M)` to the
singular chains of the subspace `U ∪ V` which

* is the corestriction of a small simplex to its image,
* induces an isomorphism on homology (the small-simplices theorem for the cover `(U', V')` of
  `U ∪ V`),
* is compatible with the maps `C_*(U) ⟶ C^{U,V}_*(M)`, `C_*(V) ⟶ C^{U,V}_*(M)` of the
  Mayer–Vietoris sequence. -/
theorem pd_small_union_iso {M : TopCat} (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) :
    ∃ (Φ : smallChains U V ⟶ singularChains ℤ (TopCat.of (U ∪ V : Set M))),
      (CategoryTheory.CategoryStruct.comp Φ (inclChains M (U ∪ V)) = smallToSing U V) ∧
      (∀ n : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap Φ n)) ∧
      (CategoryTheory.CategoryStruct.comp (smallOfU U V) Φ
        = chainMap ℤ (TopCat.of U) (TopCat.of (U ∪ V : Set M))
            (pdIncl (U ∪ V) U Set.subset_union_left)) ∧
      (CategoryTheory.CategoryStruct.comp (smallOfV U V) Φ
        = chainMap ℤ (TopCat.of V) (TopCat.of (U ∪ V : Set M))
            (pdIncl (U ∪ V) V Set.subset_union_right)) := by
  -- The two traces form an open cover of the subspace `U ∪ V`.
  have hU' : IsOpen (smallUnionTraceU U V) := hU.preimage continuous_subtype_val
  have hV' : IsOpen (smallUnionTraceV U V) := hV.preimage continuous_subtype_val
  have hcov : smallUnionTraceU U V ∪ smallUnionTraceV U V = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rcases x.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨SSet.chainComplexMap (smallUnionToSing U V) (ModuleCat.of ℤ ℤ), ?_, ?_, ?_, ?_⟩
  · -- compatibility with `smallToSing U V`
    show ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map (smallUnionToSing U V)
        ≫ ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
            (TopCat.toSSet.map (subtypeIncl M (U ∪ V : Set M)))
      = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map (smallSubcomplex U V).ι
    rw [← Functor.map_comp, smallUnionToSing_comp_incl]
  · -- the isomorphism on homology
    intro n
    have hfac : SSet.chainComplexMap (smallUnionToSing U V) (ModuleCat.of ℤ ℤ)
        = SSet.chainComplexMap (smallUnionToSmall U V) (ModuleCat.of ℤ ℤ)
          ≫ smallToSing (smallUnionTraceU U V) (smallUnionTraceV U V) := by
      rw [← SSet.Subcomplex.lift_ι (smallUnionToSing U V) (smallUnionToSing_range_le U V)]
      simp only [SSet.chainComplexMap, Functor.map_comp]
      rfl
    rw [hfac, HomologicalComplex.homologyMap_comp]
    have hsm : IsIso (smallUnionToSmall U V) :=
      Iso.isIso_hom ⟨smallUnionToSmall U V, smallUnionOfSmall U V,
        smallUnionToSmall_hom_inv U V, smallUnionOfSmall_inv_hom U V⟩
    haveI hsm' : IsIso (smallUnionToSmall U V) := hsm
    haveI hc : IsIso (SSet.chainComplexMap (smallUnionToSmall U V) (ModuleCat.of ℤ ℤ)) :=
      Functor.map_isIso ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
        (smallUnionToSmall U V)
    haveI : IsIso (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (smallUnionToSmall U V) (ModuleCat.of ℤ ℤ)) n) :=
      (quasiIsoAt_iff_isIso_homologyMap _ n).mp (quasiIsoAt_of_isIso _ n)
    haveI : IsIso (HomologicalComplex.homologyMap
        (smallToSing (smallUnionTraceU U V) (smallUnionTraceV U V)) n) :=
      smallChains_homology_iso _ _ hU' hV' hcov n
    exact inferInstance
  · -- compatibility with `smallOfU`
    show ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map (smallLiftU U V)
        ≫ ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map (smallUnionToSing U V)
      = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.toSSet.map (pdIncl (U ∪ V) U Set.subset_union_left))
    rw [← Functor.map_comp, smallLiftU_comp_smallUnion]
  · -- compatibility with `smallOfV`
    show ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map (smallLiftV U V)
        ≫ ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map (smallUnionToSing U V)
      = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.toSSet.map (pdIncl (U ∪ V) V Set.subset_union_right))
    rw [← Functor.map_comp, smallLiftV_comp_smallUnion]

end

end Work.Cohomology
