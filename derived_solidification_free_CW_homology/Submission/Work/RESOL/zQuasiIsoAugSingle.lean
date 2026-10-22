/-
AREA RESOL — the augmentation of the degreewise resolution is a quasi-isomorphism.

For a zero-preserving functorial cover `(F, π)` of light condensed abelian groups
(`F : LightCondAb ⥤ LightCondAb`, `π : F ⟶ 𝟭` with every `π.app M` epimorphic), `ZeroSetup`
builds the degreewise resolution `Rco F π hπ : LightCondAb ⥤ Cpx` (the chain complex
`(LR F π hπ).chainComplex M` of `Abelian.LeftResolution`, re-indexed so that it sits in
cochain degrees `≤ 0`) together with its augmentation

  `Zero.augSingle F π hπ : Rco F π hπ ⟶ single LightCondAb (up ℤ) 0`.

This file proves that the augmentation is a quasi-isomorphism at every object, i.e. that the
resolution really is a resolution of `M`.

The mathematics.  With `C := (LR F π hπ).chainComplex M` (a chain complex in degrees `≥ 0`),
the augmentation is `π.app M` in degree `0`, and the construction of the left resolution
gives
* `C` is exact in degrees `≥ 1` (`Abelian.LeftResolution.exactAt_map_chainComplex_succ`),
* the sequence `C₁ --C.d 1 0--> C₀ --π.app M--> M` is exact, because `C.d 1 0` factors as an
  isomorphism, the epimorphism `π.app (kernel (π.app M))`, and `kernel.ι (π.app M)`
  (`Abelian.LeftResolution.map_chainComplex_d_1_0`).

The cochain complex `Rco F π hπ` is `C` re-indexed along `ComplexShape.embeddingDownNat`
(`n ↦ -n`).  Hence:
* in cochain degrees `i ≥ 1` both complexes are concentrated, so both are exact
  (`HomologicalComplex.extend_exactAt`);
* in cochain degrees `i ≤ -1` the source is exact (transport of the chain level exactness
  through `HomologicalComplex.extend_exactAt_iff`) and the target is `single`, hence exact
  (`HomologicalComplex.exactAt_single_obj`);
* in cochain degree `0` the map of short complexes `K.sc 0 ⟶ (single 0 M).sc 0` is a
  quasi-isomorphism, which by `ShortComplex.quasiIso_iff_of_zeros'` amounts to exactness of
  the augmented sequence `K.X (-1) → K.X 0 → L.X 0` together with epimorphy of its middle
  map.  Both are transported from the chain level along the isomorphisms
  `HomologicalComplex.extendXIso`.
-/
import Mathlib
import Submission.Work.RESOL.ZeroSetup

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.RESOL

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M))

/-- The chain complex underlying the degreewise resolution of `M`. -/
noncomputable abbrev zqC (M : LightCondAb) : ChainComplex LightCondAb ℕ :=
  (LR F π hπ).chainComplex M

/-- The isomorphism `(zqC M).X 0 ≅ F.obj M`. -/
noncomputable abbrev zqX0 (M : LightCondAb) : (zqC F π hπ M).X 0 ≅ F.obj M :=
  CategoryTheory.Abelian.LeftResolution.chainComplexXZeroIso (LR F π hπ) M

/-- The isomorphism `(zqC M).X 1 ≅ F.obj (kernel (π.app M))`. -/
noncomputable abbrev zqX1 (M : LightCondAb) : (zqC F π hπ M).X 1 ≅ F.obj (kernel (π.app M)) :=
  CategoryTheory.Abelian.LeftResolution.chainComplexXOneIso (LR F π hπ) M

/-- The zero condition `(zqC M).d 1 0 ≫ (π.app M ∘ zqX0) = 0`: the augmentation of the
resolution factors through the cokernel of its first differential. -/
lemma zqC_d_comp_aug (M : LightCondAb) : (zqC F π hπ M).d 1 0 ≫ ((zqX0 F π hπ M).hom ≫ π.app M) = 0 := by
  have h := CategoryTheory.Abelian.LeftResolution.map_chainComplex_d_1_0 (Λ := LR F π hπ) (X := M)
  simp only [Functor.id_map] at h
  rw [h, Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    Limits.kernel.condition, comp_zero, Limits.comp_zero]

/-- The (chain level) augmented short complex `(zqC M).X 1 ⟶ (zqC M).X 0 ⟶ F.obj M`
associated with the resolution. -/
noncomputable abbrev zqAugChainSC (M : LightCondAb) : ShortComplex LightCondAb :=
  ShortComplex.mk ((zqC F π hπ M).d 1 0) ((zqX0 F π hπ M).hom ≫ π.app M)
    (zqC_d_comp_aug F π hπ M)

/-- **The resolution is a resolution**: the augmented sequence
`(zqC M).X 1 ⟶ (zqC M).X 0 ⟶ F.obj M` is exact.  Indeed the first differential is, up to
isomorphisms, the epimorphism `π.app (kernel (π.app M))` followed by `kernel.ι (π.app M)`. -/
theorem zqAugChainSC_exact (M : LightCondAb) : (zqAugChainSC F π hπ M).Exact := by
  have h3 : (ShortComplex.mk
      ((zqX1 F π hπ M).hom ≫ π.app (kernel (π.app M)) ≫ kernel.ι (π.app M))
      (π.app M) (by simp [Category.assoc])).Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have hker : Limits.kernel.lift (π.app M)
        ((zqX1 F π hπ M).hom ≫ π.app (kernel (π.app M)) ≫ kernel.ι (π.app M))
        (by simp [Category.assoc]) =
        (zqX1 F π hπ M).hom ≫ π.app (kernel (π.app M)) := by
      rw [← cancel_mono (kernel.ι (π.app M)), Limits.kernel.lift_ι]
      simp
    rw [hker]
    infer_instance
  have eiso : (ShortComplex.mk
      ((zqX1 F π hπ M).hom ≫ π.app (kernel (π.app M)) ≫ kernel.ι (π.app M))
      (π.app M) (by simp [Category.assoc])) ≅ zqAugChainSC F π hπ M :=
    ShortComplex.isoMk (Iso.refl _) (zqX0 F π hπ M).symm (Iso.refl _)
      (by
        have h := CategoryTheory.Abelian.LeftResolution.map_chainComplex_d_1_0
          (Λ := LR F π hπ) (X := M)
        simp only [Functor.id_map] at h
        simpa using h)
      (by simp)
  exact (ShortComplex.exact_iff_of_iso eiso).mp h3

/-! ### The cochain level short complexes in degree `0` -/

/-- The short complex `K.X (-1) ⟶ K.X 0 ⟶ K.X 1` of the cochain resolution, written with
explicit objects so that the projections reduce. -/
noncomputable abbrev zqScSrc (M : LightCondAb) : ShortComplex LightCondAb :=
  { X₁ := ((Rco F π hπ).obj M).X (-1), X₂ := ((Rco F π hπ).obj M).X 0,
    X₃ := ((Rco F π hπ).obj M).X 1,
    f := ((Rco F π hπ).obj M).d (-1) 0, g := ((Rco F π hπ).obj M).d 0 1,
    zero := HomologicalComplex.d_comp_d _ (-1) 0 1 }

/-- The short complex `L.X (-1) ⟶ L.X 0 ⟶ L.X 1` of the single complex `L = single 0 M`. -/
noncomputable abbrev zqScTgt (M : LightCondAb) : ShortComplex LightCondAb :=
  { X₁ := ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj M).X (-1),
    X₂ := ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj M).X 0,
    X₃ := ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj M).X 1,
    f := ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj M).d (-1) 0,
    g := ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj M).d 0 1,
    zero := HomologicalComplex.d_comp_d _ (-1) 0 1 }

/-- The augmented cochain level short complex `K.X (-1) ⟶ K.X 0 ⟶ L.X 0`, whose middle map
is the degree `0` component of the augmentation. -/
noncomputable abbrev zqScAug (M : LightCondAb) : ShortComplex LightCondAb :=
  { X₁ := ((Rco F π hπ).obj M).X (-1), X₂ := ((Rco F π hπ).obj M).X 0,
    X₃ := ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj M).X 0,
    f := ((Rco F π hπ).obj M).d (-1) 0,
    g := ((augSingle F π hπ).app M).f 0,
    zero := by
      rw [show ((augSingle F π hπ).app M).f 0 = aug0 F π hπ M ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv from
        (by simp only [augSingle, HomologicalComplex.mkHomToSingle_f])]
      rw [← Category.assoc, aug0_comp_d F π hπ M, Limits.zero_comp] }

@[simp] lemma zqScAug_f (M : LightCondAb) : (zqScAug F π hπ M).f = ((Rco F π hπ).obj M).d (-1) 0 := rfl

@[simp] lemma zqScAug_g (M : LightCondAb) : (zqScAug F π hπ M).g = ((augSingle F π hπ).app M).f 0 := rfl

/-- The degree `0` component of `augSingle` in terms of the augmentation `aug0` of the
degreewise resolution. -/
lemma zqAugSingle_app_f_zero (M : LightCondAb) : ((augSingle F π hπ).app M).f 0 =
    aug0 F π hπ M ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv := by
  simp only [augSingle, HomologicalComplex.mkHomToSingle_f]

/-- The first differential of the cochain resolution, in terms of the chain level first
differential (`HomologicalComplex.extend_d_eq`). -/
lemma zqScSrc_f_eq (M : LightCondAb) : ((Rco F π hπ).obj M).d (-1) 0 =
    (HomologicalComplex.extendXIso ((LR F π hπ).chainComplex M) ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f (1:ℕ) = (-1:ℤ) by simp)).hom ≫
    ((LR F π hπ).chainComplex M).d 1 0 ≫
    (HomologicalComplex.extendXIso ((LR F π hπ).chainComplex M) ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f (0:ℕ) = (0:ℤ) by simp)).inv :=
  HomologicalComplex.extend_d_eq ((LR F π hπ).chainComplex M) ComplexShape.embeddingDownNat _ _

/-- **The augmented cochain complex is exact in degree `0`**: the sequence
`K.X (-1) ⟶ K.X 0 ⟶ L.X 0` is exact, transported from the chain level along the
isomorphisms `HomologicalComplex.extendXIso`. -/
lemma zqScAug_exact (M : LightCondAb) : (zqScAug F π hπ M).Exact := by
  have eiso : zqScAug F π hπ M ≅ zqAugChainSC F π hπ M := by
    refine ShortComplex.isoMk ?_ ?_ ?_ ?_ ?_
    · exact HomologicalComplex.extendXIso ((LR F π hπ).chainComplex M) ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f (1:ℕ) = (-1:ℤ) by simp)
    · exact HomologicalComplex.extendXIso ((LR F π hπ).chainComplex M) ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f (0:ℕ) = (0:ℤ) by simp)
    · exact HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M
    · rw [zqScAug_f, zqScSrc_f_eq F π hπ M]
      simp [Category.assoc]
    · rw [zqScAug_g, zqAugSingle_app_f_zero F π hπ M, aug0]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (ShortComplex.exact_iff_of_iso eiso).mpr (zqAugChainSC_exact F π hπ M)

/-- The degree `0` component of the augmentation is an epimorphism. -/
lemma zqEpi_aug0 (M : LightCondAb) : Epi (aug0 F π hπ M ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv) := by
  haveI : Epi (π.app M) := hπ M
  rw [aug0]
  infer_instance

/-- **The augmentation is a quasi-isomorphism in degree `0`.** -/
theorem zQuasiIsoAt_zero (M : LightCondAb) : QuasiIsoAt ((augSingle F π hπ).app M) 0 := by
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
  simp only [HomologicalComplex.shortComplexFunctor']
  have hg1 : (zqScSrc F π hπ M).g = 0 := by
    show ((Rco F π hπ).obj M).d 0 1 = 0
    exact IsZero.eq_of_tgt (HomologicalComplex.isZero_extend_X ((LR F π hπ).chainComplex M)
      ComplexShape.embeddingDownNat 1 (by
        intro i hi
        simp only [ComplexShape.embeddingDownNat_f] at hi
        omega)) _ _
  have hf2 : (zqScTgt M).f = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 M (-1) 0
  have hg2 : (zqScTgt M).g = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 M 0 1
  refine (ShortComplex.quasiIso_iff_of_zeros' _ hg1 hf2 hg2).mpr ?_
  constructor
  · exact zqScAug_exact F π hπ M
  · change Epi (((augSingle F π hπ).app M).f 0)
    rw [zqAugSingle_app_f_zero F π hπ M]
    exact zqEpi_aug0 F π hπ M

/-- **The augmentation is a quasi-isomorphism in every degree `≠ 0`**: the source resolution
is exact there (transport of the exactness of the chain complex `zqC M`), and the target is
the single complex concentrated in degree `0`. -/
lemma zQuasiIsoAt_ne (M : LightCondAb) (i : ℤ) (hi : i ≠ 0) : QuasiIsoAt ((augSingle F π hπ).app M) i := by
  have hK : ((Rco F π hπ).obj M).ExactAt i := by
    by_cases h : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = i
    · obtain ⟨n, hn⟩ := h
      have hn' : (n : ℤ) = -i := by
        have h2 := hn
        simp only [ComplexShape.embeddingDownNat_f] at h2
        omega
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
      refine (HomologicalComplex.extend_exactAt_iff ((LR F π hπ).chainComplex M)
        ComplexShape.embeddingDownNat hn).mpr ?_
      exact CategoryTheory.Abelian.LeftResolution.exactAt_map_chainComplex_succ (LR F π hπ) M m
    · exact HomologicalComplex.extend_exactAt _ _ i (by intro j hj; exact h ⟨j, hj⟩)
  exact (quasiIsoAt_iff_exactAt _ _ (hK := hK)).mpr
    (HomologicalComplex.exactAt_single_obj (ComplexShape.up ℤ) 0 M i hi)

end Zero

/-- The augmentation of the degreewise resolution by a zero-preserving functorial cover is a
quasi-isomorphism. -/
theorem zQuasiIsoAugSingle (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M, CategoryTheory.Epi (π.app M)) (M : LightCondAb) :
    QuasiIso ((Work.RESOL.Zero.augSingle F π hπ).app M) := by
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = 0
  · subst hi
    exact Zero.zQuasiIsoAt_zero F π hπ M
  · exact Zero.zQuasiIsoAt_ne F π hπ M i hi

end Work.RESOL
