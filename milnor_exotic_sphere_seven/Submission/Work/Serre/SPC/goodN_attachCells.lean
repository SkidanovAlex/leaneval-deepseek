import Mathlib
import Submission.Work.Serre.SPC.B1Setup
import Submission.Work.Serre.cellStepDefs
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.SPC.tauTwoRange
import Submission.Work.Serre.SPC.discDefs
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.StemsB.SphLoopRelPair
import Submission.Work.StemsB.tripleShort_shortExact
import Submission.Work.RatHurewicz.CompressRelToRelPi

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-!
# The propagation of `GoodN` across a cell attachment

`Work.Serre.SPC.GoodN b₀ p r γ₀ g` says that the comparison map
`relPairMap (pullbackFst g p) γ₀` of the pullback of `p : E → B` along `g : Γ → B` is an
isomorphism on integral homology in degrees `< r` and surjective in degree `r`.  This file proves
that the property is preserved when `Γ` is replaced by `Γ' = attachCells (D-2) Γ ι fr` and `g` by
its extension `attachG (D-2) Γ ι fr g G hG` over the attached cells, provided the *cell step* map
`cellStepAttachMap D Γ ι fr (Pullback g' p) (pullbackFst g' p)` is an isomorphism in degrees `< r + 1`.

The proof is the five lemma applied to the morphism of short exact sequences of the triples
`F ⊆ X₀ ⊆ X₁` and `{γ₀'} ⊆ attachOld ⊆ Γ'`, where `X₁ = Pullback g' p`,
`X₀ = (pullbackFst g' p) ⁻¹' attachOld ≅ Pullback g p` and `F` is the fibre over the base point.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows HomologicalComplex
open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

variable {B : Type} [TopologicalSpace B] {E : Type} [TopologicalSpace E]

/-- The restriction of the projection `Pullback g' p → Γ'` of a pullback to the preimage of the
old part `Γ ⊆ Γ'`. -/
def attachStepRestr {Γ : Type} [TopologicalSpace Γ] (p : C(E, B)) {D : ℕ} (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    (g' : C(Work.RatHurewicz.attachCells (D - 2) Γ ι fr, B)) :
    C(↥((Work.StemsB.pullbackFst g' p) ⁻¹' Work.Serre.attachOld D Γ ι fr),
      ↥(Work.Serre.attachOld D Γ ι fr)) :=
  ⟨fun x => ⟨(Work.StemsB.pullbackFst g' p) x.1, x.2⟩,
    Continuous.subtype_mk ((Work.StemsB.pullbackFst g' p).continuous.comp continuous_subtype_val)
      (fun x => x.2)⟩

/-- The inverse homeomorphism `range attachIncl → Γ` as a continuous map `Γ → range attachIncl`. -/
def attachRangeIncl {Γ : Type} [TopologicalSpace Γ] {D : ℕ} (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) :
    C(Γ, ↥(Work.Serre.attachOld D Γ ι fr)) :=
  ⟨⇑(Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr),
    (Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr).continuous⟩

@[simp] theorem attachRangeIncl_apply {Γ : Type} [TopologicalSpace Γ] {D : ℕ} (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) (x : Γ) :
    (attachRangeIncl ι fr x : Work.RatHurewicz.attachCells (D - 2) Γ ι fr)
      = Work.RatHurewicz.attachIncl (D - 2) Γ ι fr x := rfl

/-- The pullback condition of the canonical map `Pullback g p → Pullback g' p`. -/
theorem pbAttach_cond {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B)) {D : ℕ}
    (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    (G : ι → C(Work.RatHurewicz.cellDisk (D - 2), B))
    (hG : ∀ (i : ι) (z : Work.RatHurewicz.cellSphere (D - 2)),
      G i (Work.RatHurewicz.cellSphereToDisk (D - 2) z) = g (fr i z))
    (p : C(E, B)) (x : Work.StemsB.Pullback g p) :
    Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG
        (Work.RatHurewicz.attachIncl (D - 2) Γ ι fr x.1.1) = p x.1.2 := by
  rw [Work.Serre.CWModel.attachG_incl]; exact x.2

/-- The membership proof for the canonical map `Pullback g p → (pullbackFst g' p) ⁻¹' Γ`. -/
theorem pbAttach_mem {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B)) {D : ℕ}
    (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    (G : ι → C(Work.RatHurewicz.cellDisk (D - 2), B))
    (hG : ∀ (i : ι) (z : Work.RatHurewicz.cellSphere (D - 2)),
      G i (Work.RatHurewicz.cellSphereToDisk (D - 2) z) = g (fr i z))
    (p : C(E, B)) (x : Work.StemsB.Pullback g p) :
    (Work.StemsB.pullbackFst (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) p)
        ⟨(Work.RatHurewicz.attachIncl (D - 2) Γ ι fr x.1.1, x.1.2),
          pbAttach_cond γ₀ g ι fr G hG p x⟩ ∈ Work.Serre.attachOld D Γ ι fr :=
  ⟨x.1.1, rfl⟩

/-- **The pullback of `p` along `g` is the part of the pullback along its extension `g'` lying over
the old part.** -/
def pbAttachHomeo {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B)) {D : ℕ}
    (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    (G : ι → C(Work.RatHurewicz.cellDisk (D - 2), B))
    (hG : ∀ (i : ι) (z : Work.RatHurewicz.cellSphere (D - 2)),
      G i (Work.RatHurewicz.cellSphereToDisk (D - 2) z) = g (fr i z))
    (p : C(E, B)) : Work.StemsB.Pullback g p ≃ₜ
      ↥((Work.StemsB.pullbackFst (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) p) ⁻¹'
        Work.Serre.attachOld D Γ ι fr) where
  toFun x := ⟨⟨(Work.RatHurewicz.attachIncl (D - 2) Γ ι fr x.1.1, x.1.2),
      pbAttach_cond γ₀ g ι fr G hG p x⟩, pbAttach_mem γ₀ g ι fr G hG p x⟩
  invFun y := ⟨((Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr).symm ⟨y.1.1.1, y.2⟩, y.1.1.2), by
      show g ((Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr).symm ⟨y.1.1.1, y.2⟩) = p y.1.1.2
      have h1 : Work.RatHurewicz.attachIncl (D - 2) Γ ι fr
          ((Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr).symm ⟨y.1.1.1, y.2⟩) = y.1.1.1 :=
        congrArg (fun z : ↥(Work.Serre.attachOld D Γ ι fr) =>
            (z : Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
          (Homeomorph.apply_symm_apply (Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr)
            (⟨y.1.1.1, y.2⟩ : ↥(Work.Serre.attachOld D Γ ι fr)))
      rw [← Work.Serre.CWModel.attachG_incl (D - 2) Γ ι fr g G hG, h1]
      exact y.1.2⟩
  left_inv x := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    show ((Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr).symm
        ⟨Work.RatHurewicz.attachIncl (D - 2) Γ ι fr x.1.1, ⟨x.1.1, rfl⟩⟩ : Γ) = x.1.1
    rw [show (⟨Work.RatHurewicz.attachIncl (D - 2) Γ ι fr x.1.1, ⟨x.1.1, rfl⟩⟩ :
        ↥(Work.Serre.attachOld D Γ ι fr))
        = Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr x.1.1 from rfl,
      Homeomorph.symm_apply_apply]
  right_inv y := by
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
    show Work.RatHurewicz.attachIncl (D - 2) Γ ι fr
        ((Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr).symm ⟨y.1.1.1, y.2⟩) = y.1.1.1
    exact congrArg (fun z : ↥(Work.Serre.attachOld D Γ ι fr) =>
      (z : Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
      (Homeomorph.apply_symm_apply (Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr)
        (⟨y.1.1.1, y.2⟩ : ↥(Work.Serre.attachOld D Γ ι fr)))
  continuous_toFun := by
    have h0 : Continuous (fun x : Work.StemsB.Pullback g p =>
        (⟨(Work.RatHurewicz.attachIncl (D - 2) Γ ι fr x.1.1, x.1.2),
          pbAttach_cond γ₀ g ι fr G hG p x⟩ :
          Work.StemsB.Pullback (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) p)) :=
      (Continuous.prodMk
        ((Work.RatHurewicz.attachIncl (D - 2) Γ ι fr).continuous.comp
          (continuous_fst.comp continuous_subtype_val))
        (continuous_snd.comp continuous_subtype_val)).subtype_mk
        (fun x => pbAttach_cond γ₀ g ι fr G hG p x)
    exact h0.subtype_mk (fun x => pbAttach_mem γ₀ g ι fr G hG p x)
  continuous_invFun := by
    have h0 : Continuous (fun y : ↥((Work.StemsB.pullbackFst
        (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) p) ⁻¹'
          Work.Serre.attachOld D Γ ι fr) =>
        (((Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr).symm ⟨y.1.1.1, y.2⟩, y.1.1.2) :
          Γ × E)) :=
      Continuous.prodMk
        ((Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr).symm.continuous.comp
          (((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
            (fun y => y.2))))
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))
    exact h0.subtype_mk (fun y => by
      show g ((Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr).symm ⟨y.1.1.1, y.2⟩) = p y.1.1.2
      have h1 : Work.RatHurewicz.attachIncl (D - 2) Γ ι fr
          ((Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr).symm ⟨y.1.1.1, y.2⟩) = y.1.1.1 :=
        congrArg (fun z : ↥(Work.Serre.attachOld D Γ ι fr) =>
            (z : Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
          (Homeomorph.apply_symm_apply (Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr)
            (⟨y.1.1.1, y.2⟩ : ↥(Work.Serre.attachOld D Γ ι fr)))
      rw [← Work.Serre.CWModel.attachG_incl (D - 2) Γ ι fr g G hG, h1]
      exact y.1.2)

theorem pbAttachHomeo_apply_fst {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B))
    {D : ℕ} (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    (G : ι → C(Work.RatHurewicz.cellDisk (D - 2), B))
    (hG : ∀ (i : ι) (z : Work.RatHurewicz.cellSphere (D - 2)),
      G i (Work.RatHurewicz.cellSphereToDisk (D - 2) z) = g (fr i z))
    (p : C(E, B)) (x : Work.StemsB.Pullback g p) :
    (pbAttachHomeo γ₀ g ι fr G hG p x).1.1.1
      = Work.RatHurewicz.attachIncl (D - 2) Γ ι fr x.1.1 := rfl

theorem pbAttachHomeo_apply_snd {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B))
    {D : ℕ} (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    (G : ι → C(Work.RatHurewicz.cellDisk (D - 2), B))
    (hG : ∀ (i : ι) (z : Work.RatHurewicz.cellSphere (D - 2)),
      G i (Work.RatHurewicz.cellSphereToDisk (D - 2) z) = g (fr i z))
    (p : C(E, B)) (x : Work.StemsB.Pullback g p) :
    (pbAttachHomeo γ₀ g ι fr G hG p x).1.1.2 = x.1.2 := rfl

/-- **The compatibility of `pbAttachHomeo` with the two projections.** -/
theorem pbAttachHomeo_comp {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B))
    {D : ℕ} (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    (G : ι → C(Work.RatHurewicz.cellDisk (D - 2), B))
    (hG : ∀ (i : ι) (z : Work.RatHurewicz.cellSphere (D - 2)),
      G i (Work.RatHurewicz.cellSphereToDisk (D - 2) z) = g (fr i z))
    (p : C(E, B)) (x : Work.StemsB.Pullback g p) :
    attachStepRestr p ι fr (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG)
        (pbAttachHomeo γ₀ g ι fr G hG p x)
      = attachRangeIncl ι fr (Work.StemsB.pullbackFst g p x) := by
  refine Subtype.ext ?_
  rw [show (attachStepRestr p ι fr (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG)
        (pbAttachHomeo γ₀ g ι fr G hG p x)).1
      = (Work.StemsB.pullbackFst (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) p)
          (pbAttachHomeo γ₀ g ι fr G hG p x).1 from rfl]
  rw [show (Work.StemsB.pullbackFst (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) p)
          (pbAttachHomeo γ₀ g ι fr G hG p x).1
      = (pbAttachHomeo γ₀ g ι fr G hG p x).1.1.1 from rfl]
  rw [pbAttachHomeo_apply_fst]
  rw [show (attachRangeIncl ι fr (Work.StemsB.pullbackFst g p x)).1
      = Work.RatHurewicz.attachIncl (D - 2) Γ ι fr (Work.StemsB.pullbackFst g p x) from rfl]
  rfl

/-- **`pbAttachHomeo` carries the fibre over `γ₀` to the fibre over `γ₀'`.** -/
theorem pbAttachHomeo_mem {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B))
    {D : ℕ} (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    (G : ι → C(Work.RatHurewicz.cellDisk (D - 2), B))
    (hG : ∀ (i : ι) (z : Work.RatHurewicz.cellSphere (D - 2)),
      G i (Work.RatHurewicz.cellSphereToDisk (D - 2) z) = g (fr i z))
    (p : C(E, B)) (x : Work.StemsB.Pullback g p) :
    x ∈ (Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ) ↔
      (pbAttachHomeo γ₀ g ι fr G hG p x).1
        ∈ (Work.StemsB.pullbackFst (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) p) ⁻¹'
            ({Work.RatHurewicz.attachIncl (D - 2) Γ ι fr γ₀} : Set
              (Work.RatHurewicz.attachCells (D - 2) Γ ι fr)) := by
  have key := pbAttachHomeo_apply_fst γ₀ g ι fr G hG p x
  constructor
  · intro hx
    show Work.RatHurewicz.attachIncl (D - 2) Γ ι fr x.1.1
      = Work.RatHurewicz.attachIncl (D - 2) Γ ι fr γ₀
    rw [show x.1.1 = γ₀ from hx]
  · intro hx
    show x.1.1 = γ₀
    exact Work.RatHurewicz.AttachRange.attachIncl_injective (D - 2) Γ ι fr (key.symm.trans hx)

/-! ## Helper identifications -/

/-- The `g`-component of `relChainsSubMap` as a `relChainsMapOf` of the identity. -/
theorem relChainsSubMap_eq_relChainsMapOf {X : TopCat} {A B : Set X} (h : A ⊆ B) :
    Work.Cohomology.relChainsSubMap X A B h
      = Work.Cohomology.relChainsMapOf X X A B (𝟙 X)
          (Work.StemsB.pairRestrict (𝟙 X) A B (fun x hx => h hx))
          (Work.StemsB.pairRestrict_comp_subtypeIncl (𝟙 X) A B (fun x hx => h hx)).symm := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).1
  rw [Work.Cohomology.relChainsSubMap_comp]
  unfold Work.Cohomology.relChainsMapOf
  rw [Work.Cohomology.cokernel_π_map, Work.StemsB.chainMap_id, Category.id_comp]

/-- The `f`-component of `Work.StemsB.tripleShort`. -/
@[simp] theorem stemsB_tripleShort_f {X : TopCat} (C A : Set X) (h : C ⊆ A) :
    (Work.StemsB.tripleShort X C A h).f = Work.Cohomology.relChainsMap X A C := rfl

/-- The `g`-component of `Work.StemsB.tripleShort`. -/
@[simp] theorem stemsB_tripleShort_g {X : TopCat} (C A : Set X) (h : C ⊆ A) :
    (Work.StemsB.tripleShort X C A h).g = Work.Cohomology.relChainsSubMap X C A h := rfl

/-- `Work.Cohomology.relChainsSubMap` via `Work.StemsB.pairRestrict`. -/
theorem relChainsMapOf_pairRestrict {X Y : TopCat} (f : X ⟶ Y) (A : Set X) (B : Set Y)
    (hf : ∀ x ∈ A, f x ∈ B) :
    Work.StemsB.relChainsMapOf f A B hf
      = Work.Cohomology.relChainsMapOf X Y A B f (Work.StemsB.pairRestrict f A B hf)
          (Work.StemsB.pairRestrict_comp_subtypeIncl f A B hf) := rfl

/-- Functoriality of `relChainsMapOf` in the form in which both the maps and the compatibility
proof are explicit (so that it can be used as a rewrite rule). -/
theorem relChainsMapOf_comp' {X Y Z : TopCat} (A : Set X) (B : Set Y) (C : Set Z)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (f' : Y ⟶ Z) (g' : TopCat.of B ⟶ TopCat.of C)
    (w' : Work.Cohomology.subtypeIncl Y B ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Z C) :
    Work.Cohomology.relChainsMapOf X Y A B f g w ≫
        Work.Cohomology.relChainsMapOf Y Z B C f' g' w'
      = Work.Cohomology.relChainsMapOf X Z A C (f ≫ f') (g ≫ g')
          (by rw [← Category.assoc, w, Category.assoc, w', Category.assoc]) := by
  exact Work.Cohomology.relChainsMapOf_comp A B C f g w f' g' w' _

/-- The five lemma at degree `0`: the middle column is an epimorphism in degree `0` as soon as the
two outer columns are. -/
lemma epi_homologyMap_τ₂_zero {S₁ S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : Epi (homologyMap φ.τ₁ 0)) (h₃ : Epi (homologyMap φ.τ₃ 0)) :
    Epi (homologyMap φ.τ₂ 0) := by
  have hR₂ := HomologySequence.composableArrows₂_exact hS₂ 0
  have hβ : Epi ((HomologySequence.composableArrows₂ S₁ 0).map' 1 2) := by
    haveI : Epi S₁.g := hS₁.epi_g
    have hh := epi_homologyMap_of_epi_of_not_rel S₁.g 0 (fun j hj => by
      rw [ComplexShape.down_Rel] at hj; omega)
    show Epi (homologyMap S₁.g 0)
    exact hh
  have key := Abelian.epi_of_epi_of_epi_of_epi
    (HomologySequence.mapComposableArrows₂ φ 0) hR₂ hβ
    (show Epi (app' (HomologySequence.mapComposableArrows₂ φ 0) 0) from h₁)
    (show Epi (app' (HomologySequence.mapComposableArrows₂ φ 0) 2) from h₃)
  have hψ : app' (HomologySequence.mapComposableArrows₂ φ 0) 1 = homologyMap φ.τ₂ 0 := rfl
  rwa [hψ] at key

/-- The five lemma at degree `0`: the middle column is a monomorphism in degree `0` as soon as the
outer columns are. -/
lemma mono_homologyMap_τ₂_zero {S₁ S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (hγ₁ : Epi (homologyMap φ.τ₃ 1)) (hα₀ : Mono (homologyMap φ.τ₁ 0))
    (hγ₀ : Mono (homologyMap φ.τ₃ 0)) :
    Mono (homologyMap φ.τ₂ 0) := by
  have hij : (ComplexShape.down ℕ).Rel (0 + 1) 0 := by rw [ComplexShape.down_Rel]
  have hδ₁ : (mk₂ (hS₁.δ (0 + 1) 0 hij) (homologyMap S₁.f 0)).Exact :=
    (hS₁.homology_exact₁ (0 + 1) 0 hij).exact_toComposableArrows
  have hαβ₁ : (mk₂ (homologyMap S₁.f 0) (homologyMap S₁.g 0)).Exact :=
    (hS₁.homology_exact₂ 0).exact_toComposableArrows
  have hδ₂ : (mk₂ (hS₂.δ (0 + 1) 0 hij) (homologyMap S₂.f 0)).Exact :=
    (hS₂.homology_exact₁ (0 + 1) 0 hij).exact_toComposableArrows
  have hαβ₂ : (mk₂ (homologyMap S₂.f 0) (homologyMap S₂.g 0)).Exact :=
    (hS₂.homology_exact₂ 0).exact_toComposableArrows
  have hR₁ : (mk₃ (hS₁.δ (0 + 1) 0 hij) (homologyMap S₁.f 0) (homologyMap S₁.g 0)).Exact :=
    exact_of_δ₀ hδ₁ (by
      show (mk₂ (homologyMap S₁.f 0) (homologyMap S₁.g 0)).Exact
      exact hαβ₁)
  have hR₂ : (mk₃ (hS₂.δ (0 + 1) 0 hij) (homologyMap S₂.f 0) (homologyMap S₂.g 0)).Exact :=
    exact_of_δ₀ hδ₂ (by
      show (mk₂ (homologyMap S₂.f 0) (homologyMap S₂.g 0)).Exact
      exact hαβ₂)
  let ψ : mk₃ (hS₁.δ (0 + 1) 0 hij) (homologyMap S₁.f 0) (homologyMap S₁.g 0) ⟶
      mk₃ (hS₂.δ (0 + 1) 0 hij) (homologyMap S₂.f 0) (homologyMap S₂.g 0) :=
    homMk₃ (homologyMap φ.τ₃ (0 + 1)) (homologyMap φ.τ₁ 0) (homologyMap φ.τ₂ 0)
      (homologyMap φ.τ₃ 0)
      (HomologySequence.δ_naturality φ hS₁ hS₂ (0 + 1) 0 hij)
      (naturality' (HomologySequence.mapComposableArrows₂ φ 0) 0 1)
      (naturality' (HomologySequence.mapComposableArrows₂ φ 0) 1 2)
  have key := Abelian.mono_of_epi_of_mono_of_mono ψ hR₁ hR₂
    (show Epi (app' ψ 0) from hγ₁)
    (show Mono (app' ψ 1) from hα₀)
    (show Mono (app' ψ 3) from hγ₀)
  have hψ : app' ψ 2 = homologyMap φ.τ₂ 0 := rfl
  rwa [hψ] at key

/-- The five lemma at degree `1`: the middle column is an epimorphism in degree `1` as soon as the
outer columns are. -/
lemma epi_homologyMap_τ₂_one {S₁ S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (hα₁ : Epi (homologyMap φ.τ₁ 1)) (hγ₁ : Epi (homologyMap φ.τ₃ 1))
    (hα₀ : Mono (homologyMap φ.τ₁ 0)) :
    Epi (homologyMap φ.τ₂ 1) := by
  have hij : (ComplexShape.down ℕ).Rel (0 + 1) 0 := by rw [ComplexShape.down_Rel]
  have hαβ₁ : (mk₂ (homologyMap S₁.f 1) (homologyMap S₁.g 1)).Exact :=
    (hS₁.homology_exact₂ 1).exact_toComposableArrows
  have hβδ₁ : (mk₂ (homologyMap S₁.g 1) (hS₁.δ (0 + 1) 0 hij)).Exact :=
    (hS₁.homology_exact₃ (0 + 1) 0 hij).exact_toComposableArrows
  have hαβ₂ : (mk₂ (homologyMap S₂.f 1) (homologyMap S₂.g 1)).Exact :=
    (hS₂.homology_exact₂ 1).exact_toComposableArrows
  have hβδ₂ : (mk₂ (homologyMap S₂.g 1) (hS₂.δ (0 + 1) 0 hij)).Exact :=
    (hS₂.homology_exact₃ (0 + 1) 0 hij).exact_toComposableArrows
  have hR₁ : (mk₃ (homologyMap S₁.f 1) (homologyMap S₁.g 1)
      (hS₁.δ (0 + 1) 0 hij)).Exact :=
    exact_of_δ₀ hαβ₁ (by
      show (mk₂ (homologyMap S₁.g 1) (hS₁.δ (0 + 1) 0 hij)).Exact
      exact hβδ₁)
  have hR₂ : (mk₃ (homologyMap S₂.f 1) (homologyMap S₂.g 1)
      (hS₂.δ (0 + 1) 0 hij)).Exact :=
    exact_of_δ₀ hαβ₂ (by
      show (mk₂ (homologyMap S₂.g 1) (hS₂.δ (0 + 1) 0 hij)).Exact
      exact hβδ₂)
  let ψ : mk₃ (homologyMap S₁.f 1) (homologyMap S₁.g 1) (hS₁.δ (0 + 1) 0 hij) ⟶
      mk₃ (homologyMap S₂.f 1) (homologyMap S₂.g 1) (hS₂.δ (0 + 1) 0 hij) :=
    homMk₃ (homologyMap φ.τ₁ 1) (homologyMap φ.τ₂ 1) (homologyMap φ.τ₃ 1)
      (homologyMap φ.τ₁ 0)
      (naturality' (HomologySequence.mapComposableArrows₂ φ 1) 0 1)
      (naturality' (HomologySequence.mapComposableArrows₂ φ 1) 1 2)
      (HomologySequence.δ_naturality φ hS₁ hS₂ (0 + 1) 0 hij)
  have key := Abelian.epi_of_epi_of_epi_of_mono ψ hR₁ hR₂
    (show Epi (app' ψ 0) from hα₁)
    (show Epi (app' ψ 2) from hγ₁)
    (show Mono (app' ψ 3) from hα₀)
  have hψ : app' ψ 1 = homologyMap φ.τ₂ 1 := rfl
  rwa [hψ] at key

theorem goodN_attachCells {B : Type} [TopologicalSpace B] (b₀ : B) {E : Type} [TopologicalSpace E] (p : C(E, B)) {r : ℕ} {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B)) (hGood : Work.Serre.SPC.GoodN b₀ p r γ₀ g) {D : ℕ} (hD : 2 ≤ D) (ι : Type) (fr : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) (G : ι → C(Work.RatHurewicz.cellDisk (D - 2), B)) (hG : ∀ (i : ι) (z : Work.RatHurewicz.cellSphere (D - 2)), G i (Work.RatHurewicz.cellSphereToDisk (D - 2) z) = g (fr i z)) (hstep : ∀ i : ℕ, i < r + 1 → CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Serre.cellStepAttachMap D Γ ι fr (Work.StemsB.Pullback (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) p) (Work.StemsB.pullbackFst (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) p)) i)) : Work.Serre.SPC.GoodN b₀ p r (Work.RatHurewicz.attachIncl (D - 2) Γ ι fr γ₀) (Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG) := by
  classical
  rw [Work.Serre.SPC.GoodN] at hGood ⊢
  obtain ⟨hGood₁, hGood₂⟩ := hGood
  let g' := Work.Serre.CWModel.attachG (D - 2) Γ ι fr g G hG
  let γ₀' := Work.RatHurewicz.attachIncl (D - 2) Γ ι fr γ₀
  let Q := Work.StemsB.Pullback g' p
  let q' := Work.StemsB.pullbackFst g' p
  let Q₀ : Set Q := q' ⁻¹' Work.Serre.attachOld D Γ ι fr
  let F' : Set Q := q' ⁻¹' ({γ₀'} : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
  let B_F : Set ↥Q₀ := {y | (y : Q) ∈ F'}
  let B_γ : Set ↥(Work.Serre.attachOld D Γ ι fr) :=
    {y | (y : Work.RatHurewicz.attachCells (D - 2) Γ ι fr) ∈ ({γ₀'} : Set _)}
  let P := Work.StemsB.Pullback g p
  let F : Set P := (Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)
  let eP : TopCat.of P ⟶ TopCat.of ↥Q₀ :=
    Work.StemsB.sphHomeoHom (X := TopCat.of P) (Y := TopCat.of ↥Q₀)
      (pbAttachHomeo γ₀ g ι fr G hG p)
  let eΓ : TopCat.of Γ ⟶ TopCat.of ↥(Work.Serre.attachOld D Γ ι fr) :=
    Work.StemsB.sphHomeoHom (X := TopCat.of Γ) (Y := TopCat.of ↥(Work.Serre.attachOld D Γ ι fr))
      (Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr)
  have hF'Q₀ : F' ⊆ Q₀ := fun z hz => ⟨γ₀, by rw [show q' z = γ₀' from hz]⟩
  have hγOld : ({γ₀'} : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι fr)) ⊆
      Work.Serre.attachOld D Γ ι fr :=
    fun z hz => by rw [show z = γ₀' from hz]; exact ⟨γ₀, rfl⟩
  let S₁ := Work.StemsB.tripleShort (TopCat.of Q) F' Q₀ hF'Q₀
  let S₂ := Work.StemsB.tripleShort (TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
    ({γ₀'} : Set _) (Work.Serre.attachOld D Γ ι fr) hγOld
  have hSE₁ : (Work.StemsB.tripleShort (TopCat.of Q) F' Q₀ hF'Q₀).ShortExact :=
    Work.StemsB.tripleShort_shortExact (X := TopCat.of Q) F' Q₀ hF'Q₀
  have hSE₂ : (Work.StemsB.tripleShort (TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
      ({γ₀'} : Set _) (Work.Serre.attachOld D Γ ι fr) hγOld).ShortExact :=
    Work.StemsB.tripleShort_shortExact (X := TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
      ({γ₀'} : Set _) (Work.Serre.attachOld D Γ ι fr) hγOld
  let τ₂ : S₁.X₂ ⟶ S₂.X₂ := Work.StemsB.relPairMap q' γ₀'
  let τ₃ : S₁.X₃ ⟶ S₂.X₃ := Work.Serre.cellStepAttachMap D Γ ι fr Q q'
  have hmemτ₁ : ∀ y ∈ B_F, (TopCat.ofHom (attachStepRestr p ι fr g')) y ∈ B_γ := by
    intro y hy
    show (Work.StemsB.pullbackFst g' p) (y : Q) = γ₀'
    exact hy
  let τ₁ : S₁.X₁ ⟶ S₂.X₁ :=
    Work.Cohomology.relChainsMapOf (TopCat.of ↥Q₀) (TopCat.of ↥(Work.Serre.attachOld D Γ ι fr))
      B_F B_γ (TopCat.ofHom (attachStepRestr p ι fr g'))
      (Work.StemsB.pairRestrict (TopCat.ofHom (attachStepRestr p ι fr g')) B_F B_γ hmemτ₁)
      (Work.StemsB.pairRestrict_comp_subtypeIncl (TopCat.ofHom (attachStepRestr p ι fr g')) B_F B_γ hmemτ₁).symm
  have comm12 : τ₁ ≫ S₂.f = S₁.f ≫ τ₂ := by
    rw [show τ₁ = Work.Cohomology.relChainsMapOf (TopCat.of ↥Q₀)
        (TopCat.of ↥(Work.Serre.attachOld D Γ ι fr)) B_F B_γ
        (TopCat.ofHom (attachStepRestr p ι fr g'))
        (Work.StemsB.pairRestrict (TopCat.ofHom (attachStepRestr p ι fr g')) B_F B_γ hmemτ₁) _ from rfl]
    rw [show S₂.f = Work.Cohomology.relChainsMap (TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
        (Work.Serre.attachOld D Γ ι fr) ({γ₀'} : Set _) from rfl]
    rw [show S₁.f = Work.Cohomology.relChainsMap (TopCat.of Q) Q₀ F' from rfl]
    rw [show τ₂ = Work.Cohomology.relChainsMapOf (TopCat.of Q)
        (TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr)) F'
        ({γ₀'} : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
        (TopCat.ofHom q') (Work.StemsB.fibreMap q' γ₀') _ from rfl]
    unfold Work.Cohomology.relChainsMap
    conv_lhs => rw [Work.Serre.SPC.relChainsMapOf_comp']
    conv_rhs => rw [Work.Serre.SPC.relChainsMapOf_comp']
    exact Work.Serre.SPC.relChainsMapOf_congr' _ _
      (show (TopCat.ofHom (attachStepRestr p ι fr g') ≫
          Work.Cohomology.subtypeIncl (TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
            (Work.Serre.attachOld D Γ ι fr))
        = (Work.Cohomology.subtypeIncl (TopCat.of Q) Q₀ ≫ TopCat.ofHom q') from
        TopCat.ext (fun x => rfl))
      (show (Work.StemsB.pairRestrict (TopCat.ofHom (attachStepRestr p ι fr g')) B_F B_γ hmemτ₁ ≫
          Work.Cohomology.inclInterA (TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
            (Work.Serre.attachOld D Γ ι fr) ({γ₀'} : Set _))
        = (Work.Cohomology.inclInterA (TopCat.of Q) Q₀ F' ≫ Work.StemsB.fibreMap q' γ₀') from
        TopCat.ext (fun x => Subtype.ext (by
          show (Work.StemsB.pullbackFst g' p) (x.1 : Q) = γ₀'
          exact x.2))) _ _
  have comm23 : τ₂ ≫ S₂.g = S₁.g ≫ τ₃ := by
    rw [show τ₂ = Work.Cohomology.relChainsMapOf (TopCat.of Q)
        (TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr)) F'
        ({γ₀'} : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
        (TopCat.ofHom q') (Work.StemsB.fibreMap q' γ₀') _ from rfl]
    rw [show S₂.g = Work.Cohomology.relChainsSubMap
        (TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr))
        ({γ₀'} : Set _) (Work.Serre.attachOld D Γ ι fr) hγOld from rfl]
    rw [show S₁.g = Work.Cohomology.relChainsSubMap (TopCat.of Q) F' Q₀ hF'Q₀ from rfl]
    rw [show τ₃ = Work.Cohomology.relChainsMapOf (TopCat.of Q)
        (TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr)) Q₀
        (Work.Serre.attachOld D Γ ι fr) (TopCat.ofHom q')
        (TopCat.ofHom (Work.Serre.cellStepMapRel D Γ ι fr Q q')) _ from rfl]
    rw [relChainsSubMap_eq_relChainsMapOf (X := TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr)) hγOld,
      relChainsSubMap_eq_relChainsMapOf (X := TopCat.of Q) hF'Q₀]
    conv_lhs => rw [Work.Serre.SPC.relChainsMapOf_comp']
    conv_rhs => rw [Work.Serre.SPC.relChainsMapOf_comp']
    exact Work.Serre.SPC.relChainsMapOf_congr' _ _
      (show (TopCat.ofHom q' ≫ 𝟙 (TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr)))
          = (𝟙 (TopCat.of Q) ≫ TopCat.ofHom q') from by
        rw [Category.comp_id, Category.id_comp])
      (show (Work.StemsB.fibreMap q' γ₀' ≫ Work.StemsB.pairRestrict
            (𝟙 (TopCat.of (Work.RatHurewicz.attachCells (D - 2) Γ ι fr))) ({γ₀'} : Set _)
            (Work.Serre.attachOld D Γ ι fr) (fun x hx => hγOld hx))
          = (Work.StemsB.pairRestrict (𝟙 (TopCat.of Q)) F' Q₀ (fun x hx => hF'Q₀ hx) ≫
              TopCat.ofHom (Work.Serre.cellStepMapRel D Γ ι fr Q q')) from
        TopCat.ext (fun x => Subtype.ext (by
          show γ₀' = (Work.StemsB.pullbackFst g' p) x.1
          exact x.2.symm))) _ _
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk τ₁ τ₂ τ₃ comm12 comm23
  -- ## the hypotheses on the columns
  have hτ₃ : ∀ i : ℕ, i ≤ r → CategoryTheory.IsIso (HomologicalComplex.homologyMap τ₃ i) :=
    fun i hi => hstep i (by omega)
  -- ## the transport of the first column
  have hmemv₁ : ∀ x ∈ F, eP x ∈ B_F := by
    intro x hx
    exact (pbAttachHomeo_mem γ₀ g ι fr G hG p x).mp hx
  have hmemv₂ : ∀ a ∈ ({γ₀} : Set Γ), eΓ a ∈ B_γ := by
    intro a ha
    show (Work.RatHurewicz.attachIncl (D - 2) Γ ι fr a) = γ₀'
    rw [show a = γ₀ from ha]
  let v₁ := Work.Cohomology.relChainsMapOf (TopCat.of P) (TopCat.of ↥Q₀) F B_F eP
      (Work.StemsB.pairRestrict eP F B_F hmemv₁)
      (Work.StemsB.pairRestrict_comp_subtypeIncl eP F B_F hmemv₁).symm
  let v₂ := Work.Cohomology.relChainsMapOf (TopCat.of Γ)
      (TopCat.of ↥(Work.Serre.attachOld D Γ ι fr)) ({γ₀} : Set Γ) B_γ eΓ
      (Work.StemsB.pairRestrict eΓ ({γ₀} : Set Γ) B_γ hmemv₂)
      (Work.StemsB.pairRestrict_comp_subtypeIncl eΓ ({γ₀} : Set Γ) B_γ hmemv₂).symm
  have hv₁ : CategoryTheory.IsIso v₁ := by
    rw [show v₁ = Work.StemsB.relChainsMapOf
        (Work.StemsB.sphHomeoHom (X := TopCat.of P) (Y := TopCat.of ↥Q₀)
          (pbAttachHomeo γ₀ g ι fr G hG p)) F B_F hmemv₁ from rfl]
    exact Work.StemsB.isIso_relChainsMapOf_homeomorph (X := TopCat.of P) (Y := TopCat.of ↥Q₀)
      (pbAttachHomeo γ₀ g ι fr G hG p) F B_F
      (fun x => pbAttachHomeo_mem γ₀ g ι fr G hG p x)
  have hv₂ : CategoryTheory.IsIso v₂ := by
    rw [show v₂ = Work.StemsB.relChainsMapOf
        (Work.StemsB.sphHomeoHom (X := TopCat.of Γ)
          (Y := TopCat.of ↥(Work.Serre.attachOld D Γ ι fr))
          (Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr)) ({γ₀} : Set Γ) B_γ hmemv₂ from rfl]
    exact Work.StemsB.isIso_relChainsMapOf_homeomorph (X := TopCat.of Γ)
      (Y := TopCat.of ↥(Work.Serre.attachOld D Γ ι fr))
      (Work.RatHurewicz.rangeHomeo (D - 2) Γ ι fr) ({γ₀} : Set Γ) B_γ
      (fun a => by
        constructor
        · intro h; rw [show a = γ₀ from h]; rfl
        · intro h
          exact Work.RatHurewicz.AttachRange.attachIncl_injective (D - 2) Γ ι fr h)
  have hsquare : v₁ ≫ τ₁ = Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀ ≫ v₂ := by
    rw [show v₁ = Work.Cohomology.relChainsMapOf (TopCat.of P) (TopCat.of ↥Q₀) F B_F eP
        (Work.StemsB.pairRestrict eP F B_F hmemv₁) _ from rfl]
    rw [show τ₁ = Work.Cohomology.relChainsMapOf (TopCat.of ↥Q₀)
        (TopCat.of ↥(Work.Serre.attachOld D Γ ι fr)) B_F B_γ
        (TopCat.ofHom (attachStepRestr p ι fr g'))
        (Work.StemsB.pairRestrict (TopCat.ofHom (attachStepRestr p ι fr g')) B_F B_γ hmemτ₁) _ from rfl]
    rw [show Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀ =
        Work.Cohomology.relChainsMapOf (TopCat.of P) (TopCat.of Γ) F ({γ₀} : Set Γ)
        (TopCat.ofHom (Work.StemsB.pullbackFst g p)) (Work.StemsB.fibreMap (Work.StemsB.pullbackFst g p) γ₀) _ from rfl]
    rw [show v₂ = Work.Cohomology.relChainsMapOf (TopCat.of Γ)
        (TopCat.of ↥(Work.Serre.attachOld D Γ ι fr)) ({γ₀} : Set Γ) B_γ eΓ
        (Work.StemsB.pairRestrict eΓ ({γ₀} : Set Γ) B_γ hmemv₂) _ from rfl]
    conv_lhs => rw [Work.Serre.SPC.relChainsMapOf_comp']
    conv_rhs => rw [Work.Serre.SPC.relChainsMapOf_comp']
    exact Work.Serre.SPC.relChainsMapOf_congr' _ _
      (show (eP ≫ TopCat.ofHom (attachStepRestr p ι fr g'))
          = (TopCat.ofHom (Work.StemsB.pullbackFst g p) ≫ eΓ) from
        TopCat.ext (fun x => pbAttachHomeo_comp γ₀ g ι fr G hG p x))
      (show (Work.StemsB.pairRestrict eP F B_F hmemv₁ ≫
            Work.StemsB.pairRestrict (TopCat.ofHom (attachStepRestr p ι fr g')) B_F B_γ hmemτ₁)
          = (Work.StemsB.fibreMap (Work.StemsB.pullbackFst g p) γ₀ ≫
              Work.StemsB.pairRestrict eΓ ({γ₀} : Set Γ) B_γ hmemv₂) from
        TopCat.ext (fun x => Subtype.ext (Subtype.ext (by
          show (Work.RatHurewicz.attachIncl (D - 2) Γ ι fr (Work.StemsB.pullbackFst g p x.1)) = γ₀'
          rw [show Work.StemsB.pullbackFst g p x.1 = γ₀ from x.2])))) _ _
  have hτ₁hom : ∀ i : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap τ₁ i) ↔
      CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) i) := by
    intro i
    haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap v₁ i) :=
      Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i) v₁
    haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap v₂ i) :=
      Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i) v₂
    exact Work.Serre.SPC.isIso_iff_of_comm_square _ _ _ _
      (by rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        hsquare])
  have hτ₁surj : Function.Surjective (HomologicalComplex.homologyMap τ₁ r).hom ↔
      Function.Surjective (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) r).hom := by
    haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap v₁ r) :=
      Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) r) v₁
    haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap v₂ r) :=
      Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) r) v₂
    exact Work.Serre.SPC.surjective_iff_of_comm_square _ _ _ _
      (by rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        hsquare])
  have hτ₁iso : ∀ i : ℕ, i < r → CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₁ i) :=
    fun i hi => (hτ₁hom i).mpr (hGood₁ i hi)
  have hτ₁epi : CategoryTheory.Epi (HomologicalComplex.homologyMap φ.τ₁ r) :=
    (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyMap φ.τ₁ r)).mpr (hτ₁surj.mpr hGood₂)
  -- ## the five lemma
  by_cases hr : 2 ≤ r
  · have hφ₃ : CategoryTheory.IsIso (HomologicalComplex.homologyMap φ.τ₃ r) := hτ₃ r le_rfl
    obtain ⟨hiso, hepi⟩ := Work.Serre.SPC.tauTwoRange φ hSE₁ hSE₂ r hr hτ₁iso
      (fun i hi => hτ₃ i (le_of_lt hi)) hτ₁epi (by haveI := hφ₃; exact IsIso.epi_of_iso _)
    exact ⟨hiso, (ModuleCat.epi_iff_surjective _).mp hepi⟩
  · -- the remaining degrees `r ≤ 1`
    have hrle : r = 0 ∨ r = 1 := by omega
    rcases hrle with h0 | h1
    · subst h0
      refine ⟨fun i hi => absurd hi (by omega), ?_⟩
      exact (ModuleCat.epi_iff_surjective _).mp
        (epi_homologyMap_τ₂_zero φ hSE₁ hSE₂ hτ₁epi
          (by haveI h3 : CategoryTheory.IsIso (homologyMap φ.τ₃ 0) := hτ₃ 0 (by omega)
              exact IsIso.epi_of_iso _))
    · subst h1
      refine ⟨fun i hi => ?_, ?_⟩
      · interval_cases i
        haveI hmono : Mono (homologyMap φ.τ₂ 0) :=
          mono_homologyMap_τ₂_zero φ hSE₁ hSE₂
            (by haveI h3 : CategoryTheory.IsIso (homologyMap φ.τ₃ 1) := hτ₃ 1 (by omega)
                exact IsIso.epi_of_iso _)
            (by haveI h1 : CategoryTheory.IsIso (homologyMap φ.τ₁ 0) := hτ₁iso 0 (by omega)
                exact IsIso.mono_of_iso _)
            (by haveI h3 : CategoryTheory.IsIso (homologyMap φ.τ₃ 0) := hτ₃ 0 (by omega)
                exact IsIso.mono_of_iso _)
        haveI hepi : Epi (homologyMap φ.τ₂ 0) :=
          epi_homologyMap_τ₂_zero φ hSE₁ hSE₂
            (by haveI h1 : CategoryTheory.IsIso (homologyMap φ.τ₁ 0) := hτ₁iso 0 (by omega)
                exact IsIso.epi_of_iso _)
            (by haveI h3 : CategoryTheory.IsIso (homologyMap φ.τ₃ 0) := hτ₃ 0 (by omega)
                exact IsIso.epi_of_iso _)
        exact isIso_of_mono_of_epi (homologyMap φ.τ₂ 0)
      · exact (ModuleCat.epi_iff_surjective _).mp
          (epi_homologyMap_τ₂_one φ hSE₁ hSE₂ hτ₁epi
            (by haveI h3 : CategoryTheory.IsIso (homologyMap φ.τ₃ 1) := hτ₃ 1 (by omega)
                exact IsIso.epi_of_iso _)
            (by haveI h1 : CategoryTheory.IsIso (homologyMap φ.τ₁ 0) := hτ₁iso 0 (by omega)
                exact IsIso.mono_of_iso _))

end

end Work.Serre.SPC
