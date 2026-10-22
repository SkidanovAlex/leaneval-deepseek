import Mathlib
import Submission.Work.RESOL.Basic

/-!
# The functorial atom cover

This file constructs the functorial epimorphism `Λ(M) ⟶ M` onto a light condensed abelian group
`M` from a small sum of free light condensed abelian groups `ℤ[S]`, given a *small skeleton*
`(ι, S)` of the light profinite sets which is cofinal for retractions: every light profinite set
`X` is a retract of some `S i`.

The construction is the one from the blueprint (B6): with `Λ(M) = ∐_{(i,x)} ℤ[S i]`, where `x`
runs through the sections of `M` over `S i`, the canonical map to `M` is an epimorphism: given a
section `y` of `M` over `X`, choose a retraction `X → S i → X` and use the summand indexed by the
pullback of `y` to `S i` restricted along the inclusion `X → S i`.

The construction is functorial in `M` because the index set `Σ i, M(S i)` is functorial in `M`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

/-! Since `LightCondAb` is a category of sheaves, coproducts exist but instance search has
difficulty finding them (there are several competing candidate instances for sheaf categories,
and the search blows the heartbeat budget). We register the canonical sheaf colimit instance with
a high priority so that the constructions below elaborate quickly.

Anyone writing further lemmas about the constructions of this file which invokes coproduct
instance search should repeat this `local instance` command (or supply
`@Sheaf.instHasColimitsOfShape` explicitly) in their own file. -/
attribute [local instance 2000] Sheaf.instHasColimitsOfShape

variable {ι : Type} (S : ι → LightProfinite.{0})

/-- The index type of the atom cover of `M`: pairs of a skeleton element `S i` and a section
of `M` over it. -/
abbrev AtomIdx (M : LightCondAb) : Type := Σ i : ι, M.obj.obj (Opposite.op (S i))

/-- The small sum of atoms covering `M`: a coproduct of `ℤ[S i]`, indexed by the sections of `M`
over the skeleton elements `S i`. -/
abbrev atomCover (M : LightCondAb) : LightCondAb :=
  ∐ (fun a : AtomIdx S M => (free ℤ).obj (S a.1).toCondensed)

/-- The action of the atom cover on a morphism `f : M ⟶ N`: the summand of `Λ(M)` indexed by
`(i, x)` is mapped into the summand of `Λ(N)` indexed by `(i, f x)`. -/
abbrev atomCoverShift {M N : LightCondAb} (f : M ⟶ N) : atomCover S M ⟶ atomCover S N :=
  Sigma.desc (fun a : AtomIdx S M =>
      Sigma.ι (fun b : AtomIdx S N => (free ℤ).obj (S b.1).toCondensed)
        ⟨a.1, f.hom.app (Opposite.op (S a.1)) a.2⟩)

/-- The functor sending `M` to the small sum of atoms `Λ(M)` covering it. -/
abbrev atomCoverFunctor : LightCondAb ⥤ LightCondAb where
  obj := atomCover S
  map f := atomCoverShift S f
  map_id M := by
    apply Sigma.hom_ext
    intro a
    rw [Sigma.ι_comp_desc]
    simp
  map_comp {M N P} f g := by
    apply Sigma.hom_ext
    intro a
    rw [Sigma.ι_comp_desc, ← Category.assoc, Sigma.ι_comp_desc]
    simp

/-! ## The section ↔ morphism bijection -/

/-- The bijection between morphisms `ℤ[T] ⟶ M` and sections of `M` over `T`: the free-forgetful
adjunction followed by the Yoneda lemma. This is the naturality input for the construction. -/
abbrev homEquivSection (T : LightProfinite.{0}) (M : LightCondAb) :
    ((free ℤ).obj T.toCondensed ⟶ M) ≃ M.obj.obj (Opposite.op T) :=
  ((LightCondensed.freeForgetAdjunction ℤ).homEquiv T.toCondensed M).trans
    (GrothendieckTopology.yonedaEquiv (coherentTopology LightProfinite))

lemma homEquivSection_apply (T : LightProfinite.{0}) (M : LightCondAb)
    (θ : (free ℤ).obj T.toCondensed ⟶ M) :
    homEquivSection T M θ = (GrothendieckTopology.yonedaEquiv (coherentTopology LightProfinite))
      (((LightCondensed.freeForgetAdjunction ℤ).homEquiv T.toCondensed M) θ) := by
  rw [homEquivSection, Equiv.trans_apply]
  rfl

/-- Naturality of `homEquivSection` in the target `M`. -/
lemma homEquivSection_natural {M N : LightCondAb} (f : M ⟶ N) (T : LightProfinite.{0})
    (θ : (free ℤ).obj T.toCondensed ⟶ M) :
    homEquivSection T N (θ ≫ f) = f.hom.app (Opposite.op T) (homEquivSection T M θ) := by
  rw [homEquivSection_apply, homEquivSection_apply, Adjunction.homEquiv_naturality_right]
  rw [GrothendieckTopology.yonedaEquiv_comp]
  rfl

/-- Naturality of `homEquivSection` in the test object. -/
lemma homEquivSection_map {X Y : LightProfinite.{0}} (g : X ⟶ Y) (M : LightCondAb)
    (θ : (free ℤ).obj Y.toCondensed ⟶ M) :
    homEquivSection X M ((lightProfiniteToLightCondSet ⋙ free ℤ).map g ≫ θ)
      = M.obj.map g.op (homEquivSection Y M θ) := by
  rw [homEquivSection_apply, homEquivSection_apply, Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left (LightCondensed.freeForgetAdjunction ℤ)
      (lightProfiniteToLightCondSet.map g) θ]
  change (coherentTopology LightProfinite).yonedaEquiv
      ((coherentTopology LightProfinite).yoneda.map g ≫
        ((LightCondensed.freeForgetAdjunction ℤ).homEquiv Y.toCondensed M) θ)
    = M.obj.map g.op ((coherentTopology LightProfinite).yonedaEquiv
        (((LightCondensed.freeForgetAdjunction ℤ).homEquiv Y.toCondensed M) θ))
  rw [← GrothendieckTopology.yonedaEquiv_naturality]
  rfl

/-! ## The cover map -/

/-- The canonical map `Λ(M) ⟶ M` out of the atom cover, sending the summand indexed by a section
`x` of `M` over `S i` to the corresponding morphism `ℤ[S i] ⟶ M`. -/
abbrev atomCoverMap (M : LightCondAb) : atomCover S M ⟶ M :=
  Sigma.desc (fun a : AtomIdx S M => (homEquivSection (S a.1) M).symm a.2)

lemma atomCoverMap_natural {M N : LightCondAb} (f : M ⟶ N) :
    atomCoverShift S f ≫ atomCoverMap S N = atomCoverMap S M ≫ f := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, Sigma.ι_comp_desc, ← Category.assoc, Sigma.ι_comp_desc]
  rw [Equiv.symm_apply_eq]
  rw [Sigma.ι_comp_desc]
  rw [homEquivSection_natural (M := M) (N := N) f (S a.1)
    ((homEquivSection (S a.1) M).symm a.2), Equiv.apply_symm_apply]

/-- The natural transformation `Λ ⟶ 𝟭` given by the atom cover maps. -/
abbrev atomCoverNat : atomCoverFunctor S ⟶ 𝟭 LightCondAb where
  app M := atomCoverMap S M
  naturality {M N} (f : M ⟶ N) := atomCoverMap_natural S f

/-! ## The atom cover is an epimorphism -/

/-- The atom cover map is an epimorphism, provided every light profinite set is a retract of
some `S i`. -/
theorem epi_atomCoverMap (h : ∀ X : LightProfinite.{0}, ∃ (i : ι) (e : X ⟶ S i) (r : S i ⟶ X),
      e ≫ r = 𝟙 X) (M : LightCondAb) : Epi (atomCoverMap S M) := by
  rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
  intro T y
  obtain ⟨i, e, r, hr⟩ := h T
  set y' : M.obj.obj (Opposite.op (S i)) := M.obj.map r.op y with hy'
  set θ : (free ℤ).obj (S i).toCondensed ⟶ atomCover S M :=
    Sigma.ι (fun b : AtomIdx S M => (free ℤ).obj (S b.1).toCondensed) ⟨i, y'⟩ with hθdef
  refine ⟨T, 𝟙 T, Function.surjective_id,
    homEquivSection T (atomCover S M)
      ((lightProfiniteToLightCondSet ⋙ free ℤ).map e ≫ θ), ?_⟩
  have hθ : θ ≫ atomCoverMap S M = (homEquivSection (S i) M).symm y' := by
    rw [hθdef, atomCoverMap, Sigma.ι_comp_desc]
  rw [← homEquivSection_natural (M := atomCover S M) (N := M) (atomCoverMap S M) T]
  rw [Category.assoc, hθ]
  rw [homEquivSection_map e M ((homEquivSection (S i) M).symm y'), Equiv.apply_symm_apply]
  rw [hy']
  have hmap : M.obj.map r.op ≫ M.obj.map e.op = M.obj.map (Opposite.op (𝟙 T)) := by
    rw [← Functor.map_comp, ← CategoryTheory.op_comp, hr]
    rfl
  rw [← hmap]
  simp only [ModuleCat.comp_apply]

/-! ## The atom cover is a small atomic sum -/

/-- The atom cover of `M` is a small sum of atoms `ℤ[S i]`, i.e. an atomic sum in the sense of
`IsAtomicSum`. -/
theorem isAtomicSum_atomCover (M : LightCondAb) : IsAtomicSum (atomCover S M) := by
  refine ⟨AtomIdx S M, fun a => S a.1, ?_, ?_, ?_⟩
  · exact colimit.cocone (Discrete.functor fun a : AtomIdx S M => (free ℤ).obj (S a.1).toCondensed)
  · exact ⟨colimit.isColimit _⟩
  · exact ⟨Iso.refl _⟩

/-- **The atom cover exists**: assuming a small skeleton `(ι, S)` of the light profinite sets
which is cofinal for retractions, there is a functorial epimorphism onto every light condensed
abelian group from a small atomic sum. -/
theorem hasAtomicCover_of_skeleton (ι : Type) (S : ι → LightProfinite.{0})
    (h : ∀ X : LightProfinite.{0}, ∃ (i : ι) (e : X ⟶ S i) (r : S i ⟶ X),
      CategoryTheory.CategoryStruct.comp e r = CategoryTheory.CategoryStruct.id X) :
    Work.RESOL.HasAtomicCover := by
  exact ⟨atomCoverFunctor S, atomCoverNat S, fun M => epi_atomCoverMap S h M,
    fun M => isAtomicSum_atomCover S M⟩

end Work.RESOL
