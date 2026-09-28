import Mathlib
import Submission.Work.Thom.transgressionPiAux
import Submission.Work.Cohomology.relCohMV_honest_les

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# Naturality of the honest Mayer--Vietoris connecting map in the ambient space

This module builds the chain-level pullback maps along a continuous map `f : X → Y` of the
relative small-chain complexes of the Mayer--Vietoris cover `(f⁻¹U, f⁻¹V)` of `X` to those of the
cover `(U,V)` of `Y`, together with their compatibility with the maps of the Mayer--Vietoris
sequence.  These are the inputs of `Work.Thom.transgressionNatural`.
-/

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Thom

noncomputable section

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-! ## 1. Smallness is preserved by a continuous map -/

/-- Smallness for a cover is preserved by a continuous map, for the preimage cover. -/
theorem isSmall_pullback (f : C(X, Y)) {U V : Set Y} {n : SimplexCategoryᵒᵖ}
    {σ : (TopCat.toSSet.obj (TopCat.of X)).obj n}
    (h : Work.Cohomology.IsSmall (f ⁻¹' U) (f ⁻¹' V) σ) :
    Work.Cohomology.IsSmall U V ((TopCat.toSSet.map (TopCat.ofHom f)).app n σ) := by
  unfold Work.Cohomology.IsSmall
  rcases h with h | h
  · left
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    beta_reduce
    rw [Work.Cohomology.toSSetObjEquiv_map_apply]
    exact h ⟨z, rfl⟩
  · right
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    beta_reduce
    rw [Work.Cohomology.toSSetObjEquiv_map_apply]
    exact h ⟨z, rfl⟩

/-- The same for simplices lying in a set `B`. -/
theorem isSmallIn_pullback (f : C(X, Y)) {U V B : Set Y} {n : SimplexCategoryᵒᵖ}
    {σ : (TopCat.toSSet.obj (TopCat.of X)).obj n}
    (h : Work.Cohomology.IsSmallIn (f ⁻¹' U) (f ⁻¹' V) (f ⁻¹' B) σ) :
    Work.Cohomology.IsSmallIn U V B ((TopCat.toSSet.map (TopCat.ofHom f)).app n σ) := by
  refine ⟨isSmall_pullback f h.1, ?_⟩
  intro y hy
  obtain ⟨z, rfl⟩ := hy
  beta_reduce
  rw [Work.Cohomology.toSSetObjEquiv_map_apply]
  exact h.2 ⟨z, rfl⟩

/-! ## 2. The pullback simplicial and chain maps -/

/-- **The pullback of the small simplices lying in `B`** along `f`, for the preimage cover. -/
def pbSSetIn (f : C(X, Y)) (U V B : Set Y) :
    Work.Cohomology.smallInSSet (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (f ⁻¹' B) ⟶
      Work.Cohomology.smallInSSet (X := TopCat.of Y) U V B :=
  Subfunctor.lift (G := Work.Cohomology.smallInSubcomplex (X := TopCat.of Y) U V B)
    ((Work.Cohomology.smallInSubcomplex (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (f ⁻¹' B)).ι
      ≫ TopCat.toSSet.map (TopCat.ofHom f))
    (by
      intro n σ hσ
      obtain ⟨a, ha⟩ := hσ
      rw [← ha]
      exact isSmallIn_pullback f a.2)

/-- The defining rule of `pbSSetIn`. -/
@[reassoc (attr := simp)]
theorem pbSSetIn_ι (f : C(X, Y)) (U V B : Set Y) :
    pbSSetIn f U V B
        ≫ (Work.Cohomology.smallInSubcomplex (X := TopCat.of Y) U V B).ι
      = (Work.Cohomology.smallInSubcomplex (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (f ⁻¹' B)).ι
        ≫ TopCat.toSSet.map (TopCat.ofHom f) :=
  Subfunctor.lift_ι _ _

/-- **The pullback of the small simplices** (the small subcomplex) along `f`. -/
def pbSSet (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.smallSSet (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) ⟶
      Work.Cohomology.smallSSet (X := TopCat.of Y) U V :=
  Subfunctor.lift (G := Work.Cohomology.smallSubcomplex (X := TopCat.of Y) U V)
    ((Work.Cohomology.smallSubcomplex (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V)).ι
      ≫ TopCat.toSSet.map (TopCat.ofHom f))
    (by
      intro n σ hσ
      obtain ⟨a, ha⟩ := hσ
      rw [← ha]
      exact isSmall_pullback f a.2)

/-- The defining rule of `pbSSet`. -/
@[reassoc (attr := simp)]
theorem pbSSet_ι (f : C(X, Y)) (U V : Set Y) :
    pbSSet f U V ≫ (Work.Cohomology.smallSubcomplex (X := TopCat.of Y) U V).ι
      = (Work.Cohomology.smallSubcomplex (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V)).ι
        ≫ TopCat.toSSet.map (TopCat.ofHom f) :=
  Subfunctor.lift_ι _ _

/-- **The pullback of the small chains lying in `B`.** -/
def pbSmallIn (f : C(X, Y)) (U V B : Set Y) :
    Work.Cohomology.smallInChains (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (f ⁻¹' B) ⟶
      Work.Cohomology.smallInChains (X := TopCat.of Y) U V B :=
  SSet.chainComplexMap (pbSSetIn f U V B) (ModuleCat.of ℤ ℤ)

/-- **The pullback of the small chains.** -/
def pbSmall (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.smallChains (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) ⟶
      Work.Cohomology.smallChains (X := TopCat.of Y) U V :=
  SSet.chainComplexMap (pbSSet f U V) (ModuleCat.of ℤ ℤ)

/-! ## 3. Naturality of the comparison and inclusion maps -/

/-- The restriction of `f` to the preimage of `B`. -/
def preimageProj (f : C(X, Y)) (B : Set Y) : C(↥(f ⁻¹' B), ↥B) :=
  ⟨fun x => ⟨f x.1, x.2⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem preimageProj_apply (f : C(X, Y)) (B : Set Y) (x : ↥(f ⁻¹' B)) :
    (preimageProj f B x : Y) = f x.1 := rfl

theorem subtypeIncl_comp_preimageProj (f : C(X, Y)) (B : Set Y) :
    TopCat.ofHom (preimageProj f B) ≫ Work.Cohomology.subtypeIncl (TopCat.of Y) B
      = Work.Cohomology.subtypeIncl (TopCat.of X) (f ⁻¹' B) ≫ TopCat.ofHom f := by
  apply TopCat.hom_ext
  ext x
  rfl

/-- Naturality of `smallInLift` under the pullback. -/
theorem smallInLift_pullback (f : C(X, Y)) (U V B : Set Y) :
    Work.Cohomology.smallInLift (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (f ⁻¹' B)
        ≫ TopCat.toSSet.map (TopCat.ofHom (preimageProj f B))
      = pbSSetIn f U V B
        ≫ Work.Cohomology.smallInLift (X := TopCat.of Y) U V B := by
  refine (cancel_mono (TopCat.toSSet.map
    (Work.Cohomology.subtypeIncl (TopCat.of Y) B))).1 ?_
  rw [Category.assoc, ← Functor.map_comp, subtypeIncl_comp_preimageProj, Functor.map_comp,
    ← Category.assoc, Work.Cohomology.smallInLift_comp]
  rw [Category.assoc, Work.Cohomology.smallInLift_comp, pbSSetIn_ι]

/-- Naturality of `smallInToSmall` under the pullback. -/
theorem smallInToSmall_pullback (f : C(X, Y)) (U V B : Set Y) :
    Work.Cohomology.smallInToSmall (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (f ⁻¹' B)
        ≫ pbSmall f U V
      = pbSmallIn f U V B
        ≫ Work.Cohomology.smallInToSmall (X := TopCat.of Y) U V B := by
  have hsim : Subfunctor.homOfLe (Work.Cohomology.smallInSubcomplex_le (X := TopCat.of X)
        (f ⁻¹' U) (f ⁻¹' V) (f ⁻¹' B)) ≫ pbSSet f U V
      = pbSSetIn f U V B
        ≫ Subfunctor.homOfLe (Work.Cohomology.smallInSubcomplex_le (X := TopCat.of Y) U V B) := by
    refine (cancel_mono (Work.Cohomology.smallSubcomplex (X := TopCat.of Y) U V).ι).1 ?_
    simp only [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.homOfLe_ι_assoc,
      pbSSet_ι, pbSSetIn_ι, pbSSetIn_ι_assoc]
  rw [Work.Cohomology.smallInToSmall, Work.Cohomology.smallInToSmall, pbSmall, pbSmallIn]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun m => SSet.chainComplexMap m (ModuleCat.of ℤ ℤ)) hsim

/-- `chainMap` is the simplicial chain map. -/
theorem chainMap_eq (f : C(X, Y)) :
    Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)
      = SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ) := rfl

/-- Naturality of `smallToSing` under the pullback. -/
theorem smallToSing_pullback (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.smallToSing (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V)
        ≫ SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)
      = pbSmall f U V ≫ Work.Cohomology.smallToSing (X := TopCat.of Y) U V := by
  rw [Work.Cohomology.smallToSing, Work.Cohomology.smallToSing, pbSmall]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun m => SSet.chainComplexMap m (ModuleCat.of ℤ ℤ)) (pbSSet_ι f U V)

/-- Naturality of `subInclChain` under the pullback. -/
theorem subInclChain_pullback (f : C(X, Y)) (U V : Set Y) {C B : Set Y} (h : C ⊆ B) :
    Work.Cohomology.subInclChain (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (Set.preimage_mono h)
        ≫ pbSmallIn f U V B
      = pbSmallIn f U V C
        ≫ Work.Cohomology.subInclChain (X := TopCat.of Y) U V h := by
  have hsim : Subfunctor.homOfLe (Work.Cohomology.smallInSubcomplex_mono (X := TopCat.of X)
        (Set.preimage_mono h)) ≫ pbSSetIn f U V B
      = pbSSetIn f U V C ≫ Subfunctor.homOfLe
          (Work.Cohomology.smallInSubcomplex_mono (X := TopCat.of Y) h) := by
    refine (cancel_mono (Work.Cohomology.smallInSubcomplex (X := TopCat.of Y) U V B).ι).1 ?_
    simp only [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.homOfLe_ι_assoc,
      pbSSetIn_ι, pbSSetIn_ι_assoc]
  rw [Work.Cohomology.subInclChain, Work.Cohomology.subInclChain, pbSmallIn, pbSmallIn]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun m => SSet.chainComplexMap m (ModuleCat.of ℤ ℤ)) hsim

/-- Naturality of `smallInToSingA` under the pullback. -/
theorem smallInToSingA_pullback (f : C(X, Y)) (U V B : Set Y) :
    Work.Cohomology.smallInToSingA (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (f ⁻¹' B)
        ≫ SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (preimageProj f B)))
            (ModuleCat.of ℤ ℤ)
      = pbSmallIn f U V B
        ≫ Work.Cohomology.smallInToSingA (X := TopCat.of Y) U V B := by
  rw [Work.Cohomology.smallInToSingA, Work.Cohomology.smallInToSingA, pbSmallIn]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun m => SSet.chainComplexMap m (ModuleCat.of ℤ ℤ)) (smallInLift_pullback f U V B)

theorem pbUU_w (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.relMVτ₂U (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X)
        ≫ pbSmallIn f U V U
      = pbSmallIn f U V (U ∩ (∅ : Set Y))
        ≫ Work.Cohomology.relMVτ₂U (X := TopCat.of Y) U V (∅ : Set Y) :=
  subInclChain_pullback f U V (Set.inter_subset_left : U ∩ (∅ : Set Y) ⊆ U)

theorem pbVV_w (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.relMVτ₂V (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X)
        ≫ pbSmallIn f U V V
      = pbSmallIn f U V (V ∩ (∅ : Set Y))
        ≫ Work.Cohomology.relMVτ₂V (X := TopCat.of Y) U V (∅ : Set Y) :=
  subInclChain_pullback f U V (Set.inter_subset_left : V ∩ (∅ : Set Y) ⊆ V)

theorem pbUV_w (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.relMVτ₁ (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X)
        ≫ pbSmallIn f U V (U ∩ V)
      = pbSmallIn f U V (U ∩ V ∩ (∅ : Set Y))
        ≫ Work.Cohomology.relMVτ₁ (X := TopCat.of Y) U V (∅ : Set Y) :=
  subInclChain_pullback f U V (Set.inter_subset_left : U ∩ V ∩ (∅ : Set Y) ⊆ U ∩ V)

theorem pbTop_w (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.smallInToSmall (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X)
        ≫ pbSmall f U V
      = pbSmallIn f U V (∅ : Set Y)
        ≫ Work.Cohomology.smallInToSmall (X := TopCat.of Y) U V (∅ : Set Y) :=
  smallInToSmall_pullback f U V (∅ : Set Y)

/-- The pullback on the `U`-piece. -/
def pbUU (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.relMVUU (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V) ⟶
      Work.Cohomology.relMVUU (X := TopCat.of Y) (∅ : Set Y) U V :=
  cokernel.map
    (Work.Cohomology.relMVτ₂U (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X))
    (Work.Cohomology.relMVτ₂U (X := TopCat.of Y) U V (∅ : Set Y))
    (pbSmallIn f U V (U ∩ (∅ : Set Y)))
    (pbSmallIn f U V U)
    (pbUU_w f U V)

/-- The pullback on the `V`-piece. -/
def pbVV (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.relMVVV (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V) ⟶
      Work.Cohomology.relMVVV (X := TopCat.of Y) (∅ : Set Y) U V :=
  cokernel.map
    (Work.Cohomology.relMVτ₂V (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X))
    (Work.Cohomology.relMVτ₂V (X := TopCat.of Y) U V (∅ : Set Y))
    (pbSmallIn f U V (V ∩ (∅ : Set Y)))
    (pbSmallIn f U V V)
    (pbVV_w f U V)

/-- The pullback on the overlap. -/
def pbUV (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.relMVUV (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V) ⟶
      Work.Cohomology.relMVUV (X := TopCat.of Y) (∅ : Set Y) U V :=
  cokernel.map
    (Work.Cohomology.relMVτ₁ (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X))
    (Work.Cohomology.relMVτ₁ (X := TopCat.of Y) U V (∅ : Set Y))
    (pbSmallIn f U V (U ∩ V ∩ (∅ : Set Y)))
    (pbSmallIn f U V (U ∩ V))
    (pbUV_w f U V)

/-- The pullback on the pair term. -/
def pbTop (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.relMVTopC (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V) ⟶
      Work.Cohomology.relMVTopC (X := TopCat.of Y) (∅ : Set Y) U V :=
  cokernel.map
    (Work.Cohomology.smallInToSmall (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X))
    (Work.Cohomology.smallInToSmall (X := TopCat.of Y) U V (∅ : Set Y))
    (pbSmallIn f U V (∅ : Set Y))
    (pbSmall f U V)
    (pbTop_w f U V)

/-- The compatibility of the pullback with `α_U`. -/
theorem alphaU_pullback (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.HMV.alphaU (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
        ≫ pbTop f U V
      = pbUU f U V ≫ Work.Cohomology.HMV.alphaU (X := TopCat.of Y) (∅ : Set Y) U V := by
  rw [pbUU, pbTop]
  refine (cancel_epi (cokernel.π (Work.Cohomology.relMVτ₂U (X := TopCat.of X)
    (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X)))).1 ?_
  conv_lhs => rw [← Category.assoc, Work.Cohomology.HMV.alphaU_comp, Category.assoc,
    Work.Cohomology.cokernel_π_map, ← Category.assoc, smallInToSmall_pullback]
  conv_rhs => rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
    Work.Cohomology.HMV.alphaU_comp]
  rw [Category.assoc]

/-- The compatibility of the pullback with `α_V`. -/
theorem alphaV_pullback (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.HMV.alphaV (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
        ≫ pbTop f U V
      = pbVV f U V ≫ Work.Cohomology.HMV.alphaV (X := TopCat.of Y) (∅ : Set Y) U V := by
  rw [pbVV, pbTop]
  refine (cancel_epi (cokernel.π (Work.Cohomology.relMVτ₂V (X := TopCat.of X)
    (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X)))).1 ?_
  conv_lhs => rw [← Category.assoc, Work.Cohomology.HMV.alphaV_comp, Category.assoc,
    Work.Cohomology.cokernel_π_map, ← Category.assoc, smallInToSmall_pullback]
  conv_rhs => rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
    Work.Cohomology.HMV.alphaV_comp]
  rw [Category.assoc]

/-- The compatibility of the pullback with `γ`. -/
theorem gamma_pullback (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.HMV.gamma (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
        ≫ pbUU f U V
      = pbUV f U V ≫ Work.Cohomology.HMV.gamma (X := TopCat.of Y) (∅ : Set Y) U V := by
  rw [pbUV, pbUU]
  refine (cancel_epi (cokernel.π (Work.Cohomology.relMVτ₁ (X := TopCat.of X)
    (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X)))).1 ?_
  conv_lhs => rw [← Category.assoc, Work.Cohomology.HMV.gamma_comp, Category.assoc,
    Work.Cohomology.cokernel_π_map, ← Category.assoc,
    subInclChain_pullback f U V (Set.inter_subset_left : U ∩ V ⊆ U)]
  conv_rhs => rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
    Work.Cohomology.HMV.gamma_comp]
  rw [Category.assoc]

/-- The compatibility of the pullback with `δ`. -/
theorem delta_pullback (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.HMV.delta (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
        ≫ pbVV f U V
      = pbUV f U V ≫ Work.Cohomology.HMV.delta (X := TopCat.of Y) (∅ : Set Y) U V := by
  rw [pbUV, pbVV]
  refine (cancel_epi (cokernel.π (Work.Cohomology.relMVτ₁ (X := TopCat.of X)
    (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X)))).1 ?_
  conv_lhs => rw [← Category.assoc, Work.Cohomology.HMV.delta_comp, Category.assoc,
    Work.Cohomology.cokernel_π_map, ← Category.assoc,
    subInclChain_pullback f U V (Set.inter_subset_right : U ∩ V ⊆ V)]
  conv_rhs => rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
    Work.Cohomology.HMV.delta_comp]
  rw [Category.assoc]

/-- The dual of the pullback on the top term. -/
def dTop (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC (X := TopCat.of Y) (∅ : Set Y) U V) ⟶
      Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVTopC (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)) :=
  Work.Cohomology.dualComplexMap ℤ
    (Work.Cohomology.relMVTopC (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V))
    (Work.Cohomology.relMVTopC (X := TopCat.of Y) (∅ : Set Y) U V) (pbTop f U V)

/-- The dual of the pullback on the `U`-piece. -/
def dUU (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU (X := TopCat.of Y) (∅ : Set Y) U V) ⟶
      Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)) :=
  Work.Cohomology.dualComplexMap ℤ
    (Work.Cohomology.relMVUU (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V))
    (Work.Cohomology.relMVUU (X := TopCat.of Y) (∅ : Set Y) U V) (pbUU f U V)

/-- The dual of the pullback on the `V`-piece. -/
def dVV (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV (X := TopCat.of Y) (∅ : Set Y) U V) ⟶
      Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)) :=
  Work.Cohomology.dualComplexMap ℤ
    (Work.Cohomology.relMVVV (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V))
    (Work.Cohomology.relMVVV (X := TopCat.of Y) (∅ : Set Y) U V) (pbVV f U V)

/-- The dual of the pullback on the overlap. -/
def dUV (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUV (X := TopCat.of Y) (∅ : Set Y) U V) ⟶
      Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUV (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)) :=
  Work.Cohomology.dualComplexMap ℤ
    (Work.Cohomology.relMVUV (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V))
    (Work.Cohomology.relMVUV (X := TopCat.of Y) (∅ : Set Y) U V) (pbUV f U V)

/-- The dual of the pullback on the middle term. -/
def dMid (f : C(X, Y)) (U V : Set Y) :
    (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU (X := TopCat.of Y) (∅ : Set Y) U V) ⊞
      Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV (X := TopCat.of Y) (∅ : Set Y) U V)) ⟶
      (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVUU (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)) ⊞
      Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relMVVV (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V))) :=
  biprod.map (dUU f U V) (dVV f U V)



/-! ## 4. Naturality of the comparison with the genuine relative chains -/

/-- `smallToSing` naturality, in the `chainMap` form. -/
theorem smallToSing_pullback_chainMap (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.smallToSing (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V)
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)
      = pbSmall f U V ≫ Work.Cohomology.smallToSing (X := TopCat.of Y) U V := by
  rw [chainMap_eq]
  exact smallToSing_pullback f U V

/-- `smallInToSingA` naturality, in the `chainMap` form. -/
theorem smallInToSingA_pullback_chainMap (f : C(X, Y)) (U V B : Set Y) :
    Work.Cohomology.smallInToSingA (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (f ⁻¹' B)
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(f ⁻¹' B)) (TopCat.of ↥B)
            (TopCat.ofHom (preimageProj f B))
      = pbSmallIn f U V B
        ≫ Work.Cohomology.smallInToSingA (X := TopCat.of Y) U V B := by
  rw [chainMap_eq]
  exact smallInToSingA_pullback f U V B

/-- Naturality of `mvPhi` under the pullback. -/
theorem mvPhi_pullback (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.HMV.mvPhi (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
        ≫ Work.Cohomology.hmvPairsChains (X₁ := TopCat.of X) (X₂ := TopCat.of Y)
            (∅ : Set X) (∅ : Set Y) (TopCat.ofHom f) (fun _ h => h)
      = pbTop f U V ≫ Work.Cohomology.HMV.mvPhi (X := TopCat.of Y) (∅ : Set Y) U V := by
  refine (cancel_epi (cokernel.π (Work.Cohomology.smallInToSmall (X := TopCat.of X)
    (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X)))).1 ?_
  conv_lhs => rw [← Category.assoc, Work.Cohomology.HMV.mvPhi_comp, Category.assoc,
    Work.Cohomology.hmvRelDualProj_relChains]
  conv_rhs => rw [← Category.assoc, pbTop, Work.Cohomology.cokernel_π_map, Category.assoc,
    Work.Cohomology.HMV.mvPhi_comp]
  rw [← Category.assoc, smallToSing_pullback_chainMap, Category.assoc]

/-- The computation rule for `relMVUVPhi`, in the `relChainsProj` form. -/
theorem relMVUVPhi_comp_rp (X : TopCat) (A U V : Set X) :
    cokernel.π (Work.Cohomology.relMVτ₁ U V A) ≫ Work.Cohomology.relMVUVPhi X A U V
      = Work.Cohomology.smallInToSingA U V (U ∩ V)
        ≫ Work.Cohomology.relChainsProj (Work.Cohomology.topW X U V)
            (Work.Cohomology.interAU A (U ∩ V)) :=
  Work.Cohomology.relMVUVPhi_comp X A U V


/-! ## 5. The morphisms of the small Mayer--Vietoris short complexes -/

theorem hmvF_pullback (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.hmvF (X := TopCat.of Y) (∅ : Set Y) U V ≫ dMid f U V
      = dTop f U V ≫ Work.Cohomology.hmvF (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V) := by
  unfold dMid dUU dVV dTop
  rw [Work.Cohomology.hmvF, Work.Cohomology.hmvF]
  refine biprod.ext_to_iff.mpr ⟨?_, ?_⟩
  · simp only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc, biprod.lift_fst,
      biprod.lift_fst_assoc]
    rw [← Work.Cohomology.dualComplexMap_comp, ← Work.Cohomology.dualComplexMap_comp,
      ← alphaU_pullback]
  · simp only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc, biprod.lift_snd,
      biprod.lift_snd_assoc]
    rw [← Work.Cohomology.dualComplexMap_comp, ← Work.Cohomology.dualComplexMap_comp,
      ← alphaV_pullback]

theorem hmvG_pullback (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.hmvG (X := TopCat.of Y) (∅ : Set Y) U V ≫ dUV f U V
      = dMid f U V ≫ Work.Cohomology.hmvG (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V) := by
  unfold dMid dUU dVV dUV
  rw [Work.Cohomology.hmvG, Work.Cohomology.hmvG]
  refine biprod.ext_from_iff.mpr ⟨?_, ?_⟩
  · simp only [Category.assoc, biprod.inl_map, biprod.inl_map_assoc, biprod.inl_desc,
      biprod.inl_desc_assoc]
    rw [← Work.Cohomology.dualComplexMap_comp, ← Work.Cohomology.dualComplexMap_comp,
      ← gamma_pullback]
  · simp only [Category.assoc, biprod.inr_map, biprod.inr_map_assoc, biprod.inr_desc,
      biprod.inr_desc_assoc, Preadditive.neg_comp, Preadditive.comp_neg]
    rw [← Work.Cohomology.dualComplexMap_comp, ← Work.Cohomology.dualComplexMap_comp,
      ← delta_pullback]


/-! ## 6. Naturality of the comparison isomorphisms with the honest complexes -/

theorem smallInToSingA_pullback_ovl (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.smallInToSingA (X := TopCat.of X) (f ⁻¹' U) (f ⁻¹' V) (f ⁻¹' U ∩ f ⁻¹' V)
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of ↥(f ⁻¹' U ∩ f ⁻¹' V)) (TopCat.of ↥(U ∩ V))
            (TopCat.ofHom (fPieceProj f U V))
      = pbSmallIn f U V (U ∩ V)
        ≫ Work.Cohomology.smallInToSingA (X := TopCat.of Y) U V (U ∩ V) :=
  smallInToSingA_pullback_chainMap f U V (U ∩ V)

theorem relMVUVPhi_pullback (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.relMVUVPhi (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
        ≫ Work.Cohomology.hmvPairsChains
            (X₁ := Work.Cohomology.topW (TopCat.of X) (f ⁻¹' U) (f ⁻¹' V))
            (X₂ := Work.Cohomology.topW (TopCat.of Y) U V)
            (Work.Cohomology.interAU (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U ∩ f ⁻¹' V))
            (Work.Cohomology.interAU (X := TopCat.of Y) (∅ : Set Y) (U ∩ V))
            (TopCat.ofHom (fPieceProj f U V)) (fun _ h => h)
      = pbUV f U V ≫ Work.Cohomology.relMVUVPhi (X := TopCat.of Y) (∅ : Set Y) U V := by
  refine (cancel_epi (cokernel.π (Work.Cohomology.relMVτ₁ (X := TopCat.of X)
    (f ⁻¹' U) (f ⁻¹' V) (∅ : Set X)))).1 ?_
  conv_lhs => rw [← Category.assoc, relMVUVPhi_comp_rp, Category.assoc,
    Work.Cohomology.hmvRelDualProj_relChains]
  conv_rhs => rw [← Category.assoc, pbUV, Work.Cohomology.cokernel_π_map, Category.assoc,
    relMVUVPhi_comp_rp]
  conv_lhs => rw [← Category.assoc]
  rw [smallInToSingA_pullback_ovl]
  rw [Category.assoc]

theorem cmpX_pullback (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.relComplexMap ℤ (X₁ := TopCat.of X) (X₂ := TopCat.of Y)
        (∅ : Set X) (∅ : Set Y) (TopCat.ofHom f) (fun _ h => h)
        ≫ Work.Cohomology.cmpX (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
      = Work.Cohomology.cmpX (X := TopCat.of Y) (∅ : Set Y) U V ≫ dTop f U V := by
  unfold dTop
  rw [Work.Cohomology.cmpX, Work.Cohomology.cmpX]
  conv_lhs => rw [← Category.assoc]
  conv_lhs => rw [Work.Cohomology.hmvRelComplexMap_comp_inv (∅ : Set X) (∅ : Set Y)
    (TopCat.ofHom f) (fun _ h => h)]
  conv_lhs => rw [Category.assoc]
  conv_lhs => rw [← Work.Cohomology.dualComplexMap_comp]
  conv_rhs => rw [Category.assoc, ← Work.Cohomology.dualComplexMap_comp]
  rw [mvPhi_pullback]

theorem cmpW_pullback (f : C(X, Y)) (U V : Set Y) :
    Work.Cohomology.relComplexMap ℤ (X₁ := TopCat.of ↥(f ⁻¹' U ∩ f ⁻¹' V))
        (X₂ := TopCat.of ↥(U ∩ V))
        (Work.Cohomology.interAU (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U ∩ f ⁻¹' V))
        (Work.Cohomology.interAU (X := TopCat.of Y) (∅ : Set Y) (U ∩ V))
        (TopCat.ofHom (fPieceProj f U V)) (fun _ h => h)
        ≫ Work.Cohomology.cmpW (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
      = Work.Cohomology.cmpW (X := TopCat.of Y) (∅ : Set Y) U V ≫ dUV f U V := by
  unfold dUV
  rw [Work.Cohomology.cmpW, Work.Cohomology.cmpW]
  conv_lhs => rw [← Category.assoc]
  conv_lhs => rw [Work.Cohomology.hmvRelComplexMap_comp_inv
    (Work.Cohomology.interAU (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U ∩ f ⁻¹' V))
    (Work.Cohomology.interAU (X := TopCat.of Y) (∅ : Set Y) (U ∩ V))
    (TopCat.ofHom (fPieceProj f U V)) (fun _ h => h)]
  conv_lhs => rw [Category.assoc]
  conv_lhs => rw [← Work.Cohomology.dualComplexMap_comp]
  conv_rhs => rw [Category.assoc, ← Work.Cohomology.dualComplexMap_comp]
  rw [relMVUVPhi_pullback]


/-! ## 7. Naturality of the connecting map of the small Mayer--Vietoris sequence -/

/-- The morphism of the small Mayer--Vietoris short complexes induced by the pullback. -/
def dPhi (f : C(X, Y)) (U V : Set Y) :
    (ShortComplex.mk (Work.Cohomology.hmvF (X := TopCat.of Y) (∅ : Set Y) U V)
        (Work.Cohomology.hmvG (X := TopCat.of Y) (∅ : Set Y) U V)
        (Work.Cohomology.hmv_comp (X := TopCat.of Y) (∅ : Set Y) U V)) ⟶
      (ShortComplex.mk (Work.Cohomology.hmvF (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V))
        (Work.Cohomology.hmvG (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V))
        (Work.Cohomology.hmv_comp (X := TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V))) :=
  ShortComplex.homMk (dTop f U V) (dMid f U V) (dUV f U V)
    (hmvF_pullback f U V).symm (hmvG_pullback f U V).symm

/-- Naturality of the connecting map of the small Mayer--Vietoris sequence under the pullback. -/
theorem delta_natural (f : C(X, Y)) (U V : Set Y) (k : ℕ) :
    (Work.Cohomology.hmv_shortExact (TopCat.of Y) (∅ : Set Y) U V).δ k (k + 1)
        (Work.Cohomology.relCohMVUpRel k)
      ≫ HomologicalComplex.homologyMap (dTop f U V) (k + 1)
    = HomologicalComplex.homologyMap (dUV f U V) k
      ≫ (Work.Cohomology.hmv_shortExact (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)).δ k (k + 1)
          (Work.Cohomology.relCohMVUpRel k) :=
  HomologicalComplex.HomologySequence.δ_naturality (dPhi f U V) _ _ k (k + 1)
    (Work.Cohomology.relCohMVUpRel k)


/-! ## 8. Naturality of the comparison isomorphisms at the level of cohomology -/

theorem cmpXIso_inv_relPb (f : C(X, Y)) {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (k : ℕ) :
    (Work.Cohomology.cmpXIso (TopCat.of Y) (∅ : Set Y) U V hU hV hcov (k + 1)).inv
        ≫ relPb f (k + 1)
      = HomologicalComplex.homologyMap (dTop f U V) (k + 1)
        ≫ (Work.Cohomology.cmpXIso (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
            (hU.preimage f.continuous) (hV.preimage f.continuous)
            (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) (k + 1)).inv := by
  have h := congrArg (fun m => HomologicalComplex.homologyMap m (k + 1)) (cmpX_pullback f U V)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  rw [← Work.Cohomology.cmpXIso_hom (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
        (hU.preimage f.continuous) (hV.preimage f.continuous)
        (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) (k + 1),
      ← Work.Cohomology.cmpXIso_hom (TopCat.of Y) (∅ : Set Y) U V hU hV hcov (k + 1)] at h
  have hR : relPb f (k + 1)
      = (Work.Cohomology.cmpXIso (TopCat.of Y) (∅ : Set Y) U V hU hV hcov (k + 1)).hom
        ≫ HomologicalComplex.homologyMap (dTop f U V) (k + 1)
        ≫ (Work.Cohomology.cmpXIso (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V)
            (hU.preimage f.continuous) (hV.preimage f.continuous)
            (by rw [← Set.preimage_union, hcov, Set.preimage_univ]) (k + 1)).inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hR, Iso.inv_hom_id_assoc]

theorem cmpWIso_natural (f : C(X, Y)) {U V : Set Y} (k : ℕ) :
    Work.Thom.relCohMap (fPieceProj f U V) (∅ : Set ↥(f ⁻¹' U ∩ f ⁻¹' V))
        (∅ : Set ↥(U ∩ V)) (fun _ h => h) ℤ k
        ≫ (Work.Cohomology.cmpWIso (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V) k).hom
      = (Work.Cohomology.cmpWIso (TopCat.of Y) (∅ : Set Y) U V k).hom
        ≫ HomologicalComplex.homologyMap (dUV f U V) k := by
  have h := congrArg (fun m => HomologicalComplex.homologyMap m k) (cmpW_pullback f U V)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  rw [← Work.Cohomology.cmpWIso_hom (TopCat.of X) (∅ : Set X) (f ⁻¹' U) (f ⁻¹' V) k,
      ← Work.Cohomology.cmpWIso_hom (TopCat.of Y) (∅ : Set Y) U V k] at h
  exact h

end
end Work.Thom

namespace Work.Thom
noncomputable section
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

end

end Work.Thom
