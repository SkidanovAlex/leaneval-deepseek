/-
AREA RESOL — a *zero-preserving* functorial atom cover.

The construction of functorial solid-cofibrant resolutions (B6 of REFS/02) starts from a
functorial epimorphism `Λ(M) ⟶ M` from a small sum of atoms.  For the total complex of the
resulting "resolution bicomplex" to be bounded above (and for the truncation sequences to
behave well) one needs the resolution functor to send the zero object to the zero complex,
which in turn follows from `Λ(0) = 0`.

The cover of `Submission/Work/RESOL/hasAtomicCover_of_skeleton.lean` does *not* have this
property: it is indexed by *all* sections of `M` over the skeleton elements.  Here we remove
the zero section: the cover is the coproduct of `ℤ[S i]` over the *nonzero* sections `x ≠ 0`
of `M` over `S i`.  This is still functorial (a nonzero section is sent to a possibly zero
section, in which case the corresponding component of the map is `0`), it is still an
epimorphism onto `M` (only the zero section was removed), and its values are atomic sums by
construction.

Main results:

* `redCoverFunctor`, `redCoverNat` : the cover functor and the natural epimorphism;
* `isAtomicSum_redCover` : its values are atomic sums;
* `isZero_redCover_zero` : the cover of `0` is a zero object;
* `redCoverFunctor_preservesZeroMorphisms` : it preserves zero morphisms.
-/
import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.exists_atomSkeleton
import Submission.Work.RESOL.hasAtomicCover_of_skeleton

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

attribute [local instance] Classical.propDecidable

/-- A chosen zero object of light condensed abelian groups. -/
def zeroLC : LightCondAb := Classical.choose (HasZeroObject.zero (C := LightCondAb))

lemma isZero_zeroLC : IsZero zeroLC :=
  Classical.choose_spec (HasZeroObject.zero (C := LightCondAb))

instance : Zero LightCondAb := ⟨zeroLC⟩

/-- The sections of the zero object of light condensed abelian groups are trivial. -/
theorem subsingleton_zero_obj (T : LightProfinite.{0}) :
    Subsingleton ((0 : LightCondAb).obj.obj (Opposite.op T)) := by
  refine ⟨fun x y => ?_⟩
  haveI : Subsingleton ((free ℤ).obj T.toCondensed ⟶ (0 : LightCondAb)) :=
    ⟨fun f g => IsZero.eq_of_tgt isZero_zeroLC f g⟩
  obtain ⟨f, rfl⟩ := (homEquivSection T (0 : LightCondAb)).surjective x
  obtain ⟨g, rfl⟩ := (homEquivSection T (0 : LightCondAb)).surjective y
  rw [Subsingleton.elim f g]

/-- The morphism corresponding to the zero section of the free module is the zero morphism. -/
theorem homEquivSection_symm_zero (T : LightProfinite.{0}) (M : LightCondAb) :
    (homEquivSection T M).symm 0 = 0 := by
  rw [Equiv.symm_apply_eq]
  have key := homEquivSection_natural (M := (0 : LightCondAb)) (N := M) (0 : 0 ⟶ M) T
      (0 : (free ℤ).obj T.toCondensed ⟶ 0)
  simp only [zero_comp] at key
  rw [key]
  simp

variable {ι : Type} (S : ι → LightProfinite.{0})

/-- The index set of the reduced atom cover of `M`: pairs of a skeleton element `S i` and a
*nonzero* section of `M` over it. -/
abbrev RedIdx (M : LightCondAb) : Type :=
  {a : Σ i : ι, M.obj.obj (Opposite.op (S i)) // a.2 ≠ 0}

/-- The small sum of atoms covering `M`, omitting the zero section. -/
abbrev redCover (M : LightCondAb) : LightCondAb :=
  ∐ (fun a : RedIdx S M => (free ℤ).obj (S a.1.1).toCondensed)

/-- The action of the reduced cover on a morphism `f : M ⟶ N`: the summand indexed by the
nonzero section `x` is sent to the summand indexed by `f x` if `f x ≠ 0`, and to `0` otherwise. -/
abbrev redShift {M N : LightCondAb} (f : M ⟶ N) : redCover S M ⟶ redCover S N := by
  classical
  exact Sigma.desc (fun a : RedIdx S M =>
    if h : f.hom.app (Opposite.op (S a.1.1)) a.1.2 = 0 then 0
    else Sigma.ι (fun b : RedIdx S N => (free ℤ).obj (S b.1.1).toCondensed)
      ⟨⟨a.1.1, f.hom.app (Opposite.op (S a.1.1)) a.1.2⟩, h⟩)

section Functor

variable {M N P : LightCondAb}

/-- The component of `redShift f` on a summand, in the case where nothing is killed. -/
lemma redShift_ι (f : M ⟶ N) (a : RedIdx S M)
    (h : f.hom.app (Opposite.op (S a.1.1)) a.1.2 ≠ 0) :
    Sigma.ι (fun b : RedIdx S M => (free ℤ).obj (S b.1.1).toCondensed) a ≫ redShift S f =
      Sigma.ι (fun b : RedIdx S N => (free ℤ).obj (S b.1.1).toCondensed)
        ⟨⟨a.1.1, f.hom.app (Opposite.op (S a.1.1)) a.1.2⟩, h⟩ := by
  classical
  rw [redShift, Sigma.ι_comp_desc, dif_neg h]

/-- The component of `redShift f` on a summand, in the case where it is killed. -/
lemma redShift_ι_eq_zero (f : M ⟶ N) (a : RedIdx S M)
    (h : f.hom.app (Opposite.op (S a.1.1)) a.1.2 = 0) :
    Sigma.ι (fun b : RedIdx S M => (free ℤ).obj (S b.1.1).toCondensed) a ≫ redShift S f = 0 := by
  classical
  rw [redShift, Sigma.ι_comp_desc, dif_pos h]

/-- The unconditional component formula for `redShift`. -/
lemma redShift_ι_apply {M N : LightCondAb} (f : M ⟶ N) (a : RedIdx S M) :
    Sigma.ι (fun b : RedIdx S M => (free ℤ).obj (S b.1.1).toCondensed) a ≫ redShift S f =
      (if h : f.hom.app (Opposite.op (S a.1.1)) a.1.2 = 0 then 0
        else Sigma.ι (fun b : RedIdx S N => (free ℤ).obj (S b.1.1).toCondensed)
          ⟨⟨a.1.1, f.hom.app (Opposite.op (S a.1.1)) a.1.2⟩, h⟩) := by
  classical
  rw [redShift, Sigma.ι_comp_desc]

/-- The functor sending `M` to the reduced cover of `M`. -/
abbrev redCoverFunctor : LightCondAb ⥤ LightCondAb where
  obj := redCover S
  map f := redShift S f
  map_id M := by
    classical
    apply Sigma.hom_ext
    intro a
    rw [redShift_ι_apply S (𝟙 M) a]
    split_ifs with h
    · exact absurd h a.2
    · rw [Category.comp_id]
      change Sigma.ι (fun b : RedIdx S M => (free ℤ).obj (S b.1.1).toCondensed)
          ⟨⟨a.1.1, a.1.2⟩, h⟩ =
        Sigma.ι (fun b : RedIdx S M => (free ℤ).obj (S b.1.1).toCondensed) a
      rfl
  map_comp {M N P} f g := by
    classical
    apply Sigma.hom_ext
    intro a
    have key : (f ≫ g).hom.app (Opposite.op (S a.1.1)) a.1.2
        = g.hom.app (Opposite.op (S a.1.1)) (f.hom.app (Opposite.op (S a.1.1)) a.1.2) := by
      change (f.hom.app (Opposite.op (S a.1.1)) ≫ g.hom.app (Opposite.op (S a.1.1))) a.1.2 = _
      rw [ModuleCat.comp_apply]
    rw [redShift_ι_apply S (f ≫ g) a, key, ← Category.assoc, redShift_ι_apply S f a]
    by_cases h1 : g.hom.app (Opposite.op (S a.1.1))
        (f.hom.app (Opposite.op (S a.1.1)) a.1.2) = 0
    · simp only [dif_pos h1]
      by_cases h2 : f.hom.app (Opposite.op (S a.1.1)) a.1.2 = 0
      · simp only [dif_pos h2, zero_comp]
      · simp only [dif_neg h2]
        rw [redShift_ι_eq_zero S g ⟨⟨a.1.1, f.hom.app (Opposite.op (S a.1.1)) a.1.2⟩, h2⟩ h1]
    · simp only [dif_neg h1]
      have h2 : f.hom.app (Opposite.op (S a.1.1)) a.1.2 ≠ 0 :=
        fun h => h1 (by rw [h]; exact map_zero _)
      simp only [dif_neg h2]
      rw [redShift_ι S g ⟨⟨a.1.1, f.hom.app (Opposite.op (S a.1.1)) a.1.2⟩, h2⟩ h1]

/-- The natural transformation `redCoverFunctor S ⟶ 𝟭` given by the section indexed by `(i,x)`. -/
abbrev redCoverMap (M : LightCondAb) : redCover S M ⟶ M :=
  Sigma.desc (fun a : RedIdx S M =>
    (homEquivSection (S a.1.1) M).symm a.1.2)

/-- The component of `redCoverMap` on a summand. -/
lemma redCoverMap_ι {M : LightCondAb} (i : ι) (x : M.obj.obj (Opposite.op (S i))) (hx : x ≠ 0) :
    Sigma.ι (fun b : RedIdx S M => (free ℤ).obj (S b.1.1).toCondensed) ⟨⟨i, x⟩, hx⟩ ≫
      redCoverMap S M = (homEquivSection (S i) M).symm x := by
  rw [redCoverMap, Sigma.ι_comp_desc]

lemma redCoverMap_natural {M N : LightCondAb} (f : M ⟶ N) :
    redShift S f ≫ redCoverMap S N = redCoverMap S M ≫ f := by
  classical
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, redShift, Sigma.ι_comp_desc, ← Category.assoc, redCoverMap,
    Sigma.ι_comp_desc]
  have hkey : homEquivSection (S a.1.1) N
      ((homEquivSection (S a.1.1) M).symm a.1.2 ≫ f)
      = f.hom.app (Opposite.op (S a.1.1)) a.1.2 := by
    rw [homEquivSection_natural, Equiv.apply_symm_apply]
  have key2 : (homEquivSection (S a.1.1) M).symm a.1.2 ≫ f
      = (homEquivSection (S a.1.1) N).symm (f.hom.app (Opposite.op (S a.1.1)) a.1.2) := by
    rw [Equiv.eq_symm_apply]
    exact hkey
  by_cases h : f.hom.app (Opposite.op (S a.1.1)) a.1.2 = 0
  · rw [dif_pos h, zero_comp, key2, h]
    exact (homEquivSection_symm_zero (S a.1.1) N).symm
  · rw [dif_neg h, redCoverMap_ι (i := a.1.1)
      (x := f.hom.app (Opposite.op (S a.1.1)) a.1.2) (hx := h), key2]

end Functor

/-- The natural epimorphism `redCover ⟶ 𝟭`. -/
abbrev redCoverNat : redCoverFunctor S ⟶ 𝟭 LightCondAb where
  app M := redCoverMap S M
  naturality {M N} (f : M ⟶ N) := redCoverMap_natural S f

/-- The reduced atom cover of `M` is a small atomic sum. -/
theorem isAtomicSum_redCover (M : LightCondAb) : IsAtomicSum (redCover S M) := by
  refine ⟨RedIdx S M, fun a => S a.1.1, ?_, ?_, ?_⟩
  · exact colimit.cocone (Discrete.functor fun a : RedIdx S M => (free ℤ).obj (S a.1.1).toCondensed)
  · exact ⟨colimit.isColimit _⟩
  · exact ⟨Iso.refl _⟩

/-- The index set of the reduced cover of the zero object is empty. -/
lemma isEmpty_redIdx_zero : IsEmpty (RedIdx S (0 : LightCondAb)) := by
  refine ⟨fun a => a.2 ?_⟩
  haveI := subsingleton_zero_obj (S a.1.1)
  exact Subsingleton.elim _ _

/-- The reduced cover of `0` is a zero object. -/
theorem isZero_redCover_zero : IsZero (redCover S (0 : LightCondAb)) := by
  haveI := isEmpty_redIdx_zero S
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro a
  exact isEmptyElim a

/-- The reduced cover map is an epimorphism, provided every light profinite set is a retract of
some `S i`. -/
theorem epi_redCoverMap
    (h : ∀ X : LightProfinite.{0}, ∃ (i : ι) (e : X ⟶ S i) (r : S i ⟶ X),
      CategoryTheory.CategoryStruct.comp e r = CategoryTheory.CategoryStruct.id X)
    (M : LightCondAb) : Epi (redCoverMap S M) := by
  classical
  rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
  intro T y
  by_cases hy : y = 0
  · refine ⟨T, 𝟙 T, Function.surjective_id, 0, ?_⟩
    simp [hy]
  · obtain ⟨i, e, r, hr⟩ := h T
    set y' : M.obj.obj (Opposite.op (S i)) := M.obj.map r.op y with hy'
    have hcomp : M.obj.map e.op (M.obj.map r.op y) = y := by
      have hmap : M.obj.map r.op ≫ M.obj.map e.op = 𝟙 (M.obj.obj (Opposite.op T)) := by
        rw [← Functor.map_comp, ← CategoryTheory.op_comp, hr]
        simp
      have h2 := congrArg (fun (φ : M.obj.obj (Opposite.op T) ⟶ M.obj.obj (Opposite.op T)) =>
        φ y) hmap
      simpa using h2
    have hy'0 : y' ≠ 0 := by
      intro h0
      exact hy (by rw [← hcomp, ← hy', h0]; simp)
    set θ : (free ℤ).obj (S i).toCondensed ⟶ redCover S M :=
      Sigma.ι (fun b : RedIdx S M => (free ℤ).obj (S b.1.1).toCondensed)
        ⟨⟨i, y'⟩, hy'0⟩ with hθdef
    refine ⟨T, 𝟙 T, Function.surjective_id,
      homEquivSection T (redCover S M)
        ((lightProfiniteToLightCondSet ⋙ free ℤ).map e ≫ θ), ?_⟩
    have hθ : θ ≫ redCoverMap S M = (homEquivSection (S i) M).symm y' := by
      rw [hθdef, redCoverMap, Sigma.ι_comp_desc]
    rw [← homEquivSection_natural (M := redCover S M) (N := M) (redCoverMap S M) T]
    rw [Category.assoc, hθ]
    rw [homEquivSection_map e M ((homEquivSection (S i) M).symm y'), Equiv.apply_symm_apply]
    rw [hy']
    have hmap : M.obj.map r.op ≫ M.obj.map e.op = M.obj.map (Opposite.op (𝟙 T)) := by
      rw [← Functor.map_comp, ← CategoryTheory.op_comp, hr]
      rfl
    rw [← hmap]
    simp only [ModuleCat.comp_apply]

instance redCoverFunctor_preservesZeroMorphisms : (redCoverFunctor S).PreservesZeroMorphisms where
  map_zero M N := by
    classical
    apply Sigma.hom_ext
    intro a
    have h0 : (0 : M ⟶ N).hom.app (Opposite.op (S a.1.1)) a.1.2 = 0 := by simp
    rw [redShift_ι_apply S (0 : M ⟶ N) a, dif_pos h0, comp_zero]

end Work.RESOL
