import Mathlib
import Submission.Work.RESOL.ZeroTruncSES
import Submission.Work.RESOL.zQuasiIsoAugSingle
import Submission.Work.RESOL.quasiIso_restrictionMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.RESOL

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M))

/-! ## The canonical isomorphism `singleShift k M ≅ (single k).obj M`

`Zero.singleShift k M` is the single complex `(single 0).obj M` re-indexed along the shape
embedding `n ↦ n - k`; it is concentrated in degree `k`, with zero differentials.  We build the
canonical isomorphism to the single complex concentrated in degree `k` componentwise, using the
fact that both complexes have zero differentials. -/

/-- The degree `n` component of the canonical isomorphism `singleShift k M ≅ (single k).obj M`:
in degree `k` it is the re-indexing isomorphism, elsewhere it is an isomorphism between the
two (zero) objects. -/
noncomputable def zColAugIsoComp (k : ℤ) (M : LightCondAb) (n : ℤ) :
    (singleShift k M).X n ≅
      ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) k).obj M).X n :=
  if h : n = k then
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M (n - k) (by omega)).trans
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k M).symm).trans
        (HomologicalComplex.XIsoOfEq ((HomologicalComplex.single LightCondAb
          (ComplexShape.up ℤ) k).obj M) h.symm))
  else
    IsZero.iso (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M (n - k) (by omega))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) k M n h)

/-- The re-indexed single complex `Zero.singleShift k M` is (canonically) the single complex
concentrated in degree `k`.  Both complexes have zero differentials, so the degreewise
isomorphisms `zColAugIsoComp` are automatically compatible with them. -/
noncomputable def zColAugIso (k : ℤ) (M : LightCondAb) :
    singleShift k M ≅ (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) k).obj M :=
  HomologicalComplex.Hom.isoOfComponents (zColAugIsoComp k M) (by
    intro i j hij
    rw [show ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) k).obj M).d i j = 0
        from rfl, comp_zero,
      show (singleShift k M).d i j = 0 from rfl, zero_comp])

@[simp]
lemma zColAugIso_hom_f (k : ℤ) (M : LightCondAb) (n : ℤ) :
    (zColAugIso k M).hom.f n = (zColAugIsoComp k M n).hom := rfl

/-- The degree `k` component of `zColAugIso`, in explicit form. -/
lemma zColAugIsoComp_self_hom (k : ℤ) (M : LightCondAb) (h : k - k = 0) :
    (zColAugIsoComp k M k).hom =
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M (k - k) h).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k M).inv := by
  unfold zColAugIsoComp
  rw [dite_eq_left rfl]
  simp

/-! ## The degreewise components of the augmentation of the resolution -/

/-- The component in degree `0` of the augmentation `Zero.augSingle`, in explicit form. -/
lemma zColAug_augSingle_app_f_eq (M : LightCondAb) {i : ℤ} (hi : i = 0) :
    ((augSingle F π hπ).app M).f i =
      (((Rco F π hπ).obj M).XIsoOfEq hi).hom ≫ aug0 F π hπ M ≫
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M i hi).inv := by
  simp only [augSingle, HomologicalComplex.mkHomToSingle, dite_eq_left hi]

/-- The components of the augmentation `Zero.augSingle` in degrees `≠ 0` vanish. -/
lemma zColAug_augSingle_app_f_ne (M : LightCondAb) {i : ℤ} (hi : i ≠ 0) :
    ((augSingle F π hπ).app M).f i = 0 := by
  simp only [augSingle, HomologicalComplex.mkHomToSingle, dite_eq_right hi]

/-- The degree `k` component of `Zero.colAugFam`, in explicit form. -/
lemma zColAugFam_self (k : ℤ) (B : Cpx) (h : k - k = 0) :
    colAugFam F π hπ k B k =
      (((Rco F π hπ).obj (B.X k)).XIsoOfEq h).hom ≫ aug0 F π hπ (B.X k) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k (B.X k)).inv := by
  unfold colAugFam
  rw [dite_eq_left rfl]
  congr 1

/-! ## The main comparison -/

/-- The composite of the augmentation of the `k`-th column with the canonical isomorphism
`zColAugIso` has degreewise components `Zero.colAugFam`. -/
lemma zColAugRestr_comp_iso (k : ℤ) (B : Cpx) (n : ℤ) :
    (colAugRestr F π hπ k B).f n ≫ (zColAugIso k (B.X k)).hom.f n = colAugFam F π hπ k B n := by
  by_cases h : n = k
  · rw [h]
    rw [colAugRestr_f, zColAugIso_hom_f,
      zColAug_augSingle_app_f_eq F π hπ (B.X k) (show k - k = 0 by omega),
      zColAugIsoComp_self_hom k (B.X k) (show k - k = 0 by omega),
      zColAugFam_self F π hπ k B (show k - k = 0 by omega)]
    simp
  · rw [zColAugIso_hom_f, colAugRestr_f,
      zColAug_augSingle_app_f_ne F π hπ (B.X k) (by omega : n - k ≠ 0), zero_comp]
    unfold colAugFam
    rw [dite_eq_right h]

end Zero

/-- There is a chain map from the `k`-th column `colCpx k B` to the single complex
`(single k).obj (B.X k)` whose degree `n` component is `colAugFam`, and it is a
quasi-isomorphism.

Route (all the ingredients are in the workspace):
* the chain-map property: the target `(single k).obj (B.X k)` has zero differentials
  (`HomologicalComplex.single_obj_d`), and in degree `k - 1` the composite with the differential of
  `colCpx k B` is `(Rco.obj (B.X k)).d (-1) 0 ≫ aug0 = 0` by `Work.RESOL.Zero.aug0_comp_d`;
* the quasi-isomorphism: the composite `colAugFam` is the restriction
  `Work.RESOL.Zero.colAugRestr F π hπ k B = HomologicalComplex.restrictionMap
  ((Work.RESOL.Zero.augSingle F π hπ).app (B.X k)) (Work.RESOL.Zero.shiftEmb k)` composed with the
  isomorphism of complexes
  `Work.RESOL.Zero.singleShift k (B.X k) ≅
  (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) k).obj (B.X k)`
  (the canonical one which is the identity in degree `k` and zero elsewhere; it can be built with
  `HomologicalComplex.single_obj_X_self` and `HomologicalComplex.isZero_single_obj_X`);
  `QuasiIso` of the first factor follows from `Work.RESOL.zQuasiIsoAugSingle` if one has that
  restricting cochain complexes along the shape embedding `Zero.shiftEmb k` preserves
  quasi-isomorphisms (`Work.RESOL.quasiIso_restrictionMap`, proved in
  `Submission/Work/RESOL/quasiIso_restrictionMap.lean`, can be used once it is available; otherwise
  prove it here from `HomologicalComplex.restrictionHomologyIso` and its naturality lemmas).
  `QuasiIso` of the second factor is an instance, and `QuasiIso` is closed under composition
  (`QuasiIso.comp`). -/
theorem zColAug (F : CategoryTheory.Functor LightCondAb LightCondAb) [F.PreservesZeroMorphisms]
    (π : F ⟶ CategoryTheory.Functor.id LightCondAb) (hπ : ∀ M, CategoryTheory.Epi (π.app M))
    (k : ℤ) (B : Work.RESOL.Cpx) :
    ∃ (g : Work.RESOL.Zero.colCpx F π hπ k B ⟶
      (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) k).obj (B.X k)),
      (∀ n : ℤ, g.f n = Work.RESOL.Zero.colAugFam F π hπ k B n) ∧ QuasiIso g := by
  refine ⟨Zero.colAugRestr F π hπ k B ≫ (Zero.zColAugIso k (B.X k)).hom, ?_, ?_⟩
  · intro n
    exact Zero.zColAugRestr_comp_iso F π hπ k B n
  · have : QuasiIso (Zero.colAugRestr F π hπ k B) :=
      quasiIso_restrictionMap (Zero.shiftEmb k) ((Zero.augSingle F π hπ).app (B.X k))
        (zQuasiIsoAugSingle F π hπ (B.X k))
    infer_instance

end Work.RESOL
