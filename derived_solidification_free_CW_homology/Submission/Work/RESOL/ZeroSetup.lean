/-
AREA RESOL — machinery for functorial solid-cofibrant resolutions (B6).

This file contains the *definitions* of the resolution functor built from a zero-preserving
functorial atom cover (`HasAtomicCover₀`), together with the elementary lemmas about them
needed to state the pieces of the proof of `Work.RESOL.hasBoundedResolutionZero`.

Route (see `RESOL/DESIGN.md` and `NOTES_LEAD_solid_gaps1.md` §2):

* `Rco : LightCondAb ⤥ Cpx` is the degreewise resolution functor: `Λ.chainComplexFunctor`
  (Mathlib's `Abelian.LeftResolution`) re-indexed so that the resolution sits in cochain
  degrees `≤ 0` (`ComplexShape.embeddingDownNat.extendFunctor`).  Its augmentation
  `aug0 : (Rco.obj M).X 0 ⟶ M` is natural and induces a quasi-isomorphism
  `Rco.obj M ⟶ (single 0).obj M` at every object.
* For a cochain complex `B`, the resolution is the total complex of the "column" double complex
  with columns `Rco.obj (B.X q)`, placed in total degree `q`: `R B` has degree `n` given by the
  coproduct over `q` of `(Rco.obj (B.X q)).X (n - q)`, with differential the resolution
  differential plus `(-1)^(n-q)` times the differential induced by `B`.  The construction is
  indexed by a predicate `P : ℤ → Prop` on the column index, so that the *column truncations*
  `resTot (fun q => k ≤ q) B` are available for the filtration argument proving that
  `R B ⟶ B` is a quasi-isomorphism.
-/
import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.Instances

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M))

/-- The `LeftResolution` structure attached to a zero-preserving functorial cover `(F, π)`.
The natural transformation `π` of the resolution has the components of `π` itself. -/
abbrev LR : Abelian.LeftResolution (𝟭 LightCondAb) where
  F := F
  π := { app := fun M => π.app M
         naturality := fun {M N} f => by
           simp only [Functor.comp_map, Functor.id_map]
           exact π.naturality f }
  epi_π_app M := hπ M

/-- The components of the `π` field of the resolution are the components of `π`. -/
lemma LR_pi_app (M : LightCondAb) : (LR F π hπ).π.app M = π.app M := rfl

instance : (LR F π hπ).chainComplexFunctor.PreservesZeroMorphisms :=
  ⟨fun X Y => Abelian.LeftResolution.chainComplexMap_zero (LR F π hπ) X Y⟩

/-- The degreewise resolution functor of a light condensed abelian group, as a cochain complex
concentrated in degrees `≤ 0`. -/
abbrev Rco : LightCondAb ⥤ Cpx where
  obj M := ((LR F π hπ).chainComplex M).extend ComplexShape.embeddingDownNat
  map {M N} f := HomologicalComplex.extendMap ((LR F π hπ).chainComplexMap f)
    ComplexShape.embeddingDownNat
  map_id M := by simp
  map_comp {M N P} f g := by simp

instance : (Rco F π hπ).PreservesZeroMorphisms where
  map_zero {M N} := by
    rw [show ((Rco F π hπ).map (0 : M ⟶ N)) = HomologicalComplex.extendMap
      ((LR F π hπ).chainComplexMap (0 : M ⟶ N)) ComplexShape.embeddingDownNat from rfl,
      Abelian.LeftResolution.chainComplexMap_zero, HomologicalComplex.extendMap_zero]

lemma Rco_map_f_zero {M N : LightCondAb} (f : M ⟶ N) :
    ((Rco F π hπ).map f).f 0
      = (HomologicalComplex.extendXIso ((LR F π hπ).chainComplex M)
            ComplexShape.embeddingDownNat (by simp)).hom
          ≫ (Abelian.LeftResolution.chainComplexXZeroIso (LR F π hπ) M).hom
          ≫ F.map f
          ≫ (Abelian.LeftResolution.chainComplexXZeroIso (LR F π hπ) N).inv
          ≫ (HomologicalComplex.extendXIso ((LR F π hπ).chainComplex N)
              ComplexShape.embeddingDownNat (by simp)).inv := by
  have h0 : ComplexShape.embeddingDownNat.f (0 : ℕ) = (0 : ℤ) := by simp
  rw [show ((Rco F π hπ).map f).f 0
      = HomologicalComplex.extend.mapX ((LR F π hπ).chainComplexMap f)
          (ComplexShape.embeddingDownNat.r (0 : ℤ)) from rfl]
  rw [HomologicalComplex.extend.mapX_some ((LR F π hπ).chainComplexMap f)
    (ComplexShape.Embedding.r_eq_some ComplexShape.embeddingDownNat h0)]
  rw [Abelian.LeftResolution.chainComplexMap_f_0]
  rfl

/-- The augmentation `Rco.obj M ⟶ M` in degree `0`. -/
def aug0 (M : LightCondAb) : ((Rco F π hπ).obj M).X 0 ⟶ M :=
  (HomologicalComplex.extendXIso ((LR F π hπ).chainComplex M) ComplexShape.embeddingDownNat
      (by simp)).hom
    ≫ (Abelian.LeftResolution.chainComplexXZeroIso (LR F π hπ) M).hom
    ≫ π.app M

lemma aug0_comp_d (M : LightCondAb) :
    ((Rco F π hπ).obj M).d (-1) 0 ≫ aug0 F π hπ M = 0 := by
  have h1 : ComplexShape.embeddingDownNat.f (1 : ℕ) = (-1 : ℤ) := by simp
  have h0 : ComplexShape.embeddingDownNat.f (0 : ℕ) = (0 : ℤ) := by simp
  have hd : ((LR F π hπ).chainComplex M).d 1 0 =
      (Abelian.LeftResolution.chainComplexXOneIso (LR F π hπ) M).hom
        ≫ π.app (kernel (π.app M))
        ≫ kernel.ι (π.app M)
        ≫ (Abelian.LeftResolution.chainComplexXZeroIso (LR F π hπ) M).inv := by
    simpa using Abelian.LeftResolution.map_chainComplex_d_1_0 (Λ := LR F π hπ) (X := M)
  rw [show ((Rco F π hπ).obj M).d (-1) 0
      = (((LR F π hπ).chainComplex M).extend ComplexShape.embeddingDownNat).d (-1) 0 from rfl]
  rw [HomologicalComplex.extend_d_eq ((LR F π hπ).chainComplex M) _ h1 h0, hd, aug0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [kernel.condition]
  simp only [comp_zero]

lemma aug0_naturality {M N : LightCondAb} (f : M ⟶ N) :
    ((Rco F π hπ).map f).f 0 ≫ aug0 F π hπ N = aug0 F π hπ M ≫ f := by
  rw [Rco_map_f_zero, aug0, aug0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [π.naturality]
  simp only [Functor.id_map]

/-- The augmentation, as a natural transformation to the complex concentrated in degree `0`. -/
def augSingle : Rco F π hπ ⟶ HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0 where
  app M := HomologicalComplex.mkHomToSingle (aug0 F π hπ M) (by
    intro i hi
    rw [ComplexShape.up_Rel] at hi
    have hi' : i = -1 := by omega
    subst hi'
    exact aug0_comp_d F π hπ M)
  naturality {M N} f := by
    apply HomologicalComplex.to_single_hom_ext (j := 0)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f,
      HomologicalComplex.single_map_f_self]
    have hunf : (HomologicalComplex.extendMap ((LR F π hπ).chainComplexMap f)
        ComplexShape.embeddingDownNat).f 0 = ((Rco F π hπ).map f).f 0 := rfl
    rw [hunf, ← Category.assoc, aug0_naturality]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

#check @LR
#check @Rco
#check @aug0
#check @aug0_naturality
#check @augSingle

end Zero

end Work.RESOL
