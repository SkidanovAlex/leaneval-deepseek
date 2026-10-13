import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Cech.cechSpec_quasiIso
import Submission.Work.DSF1.Cech.exists_cechZ_lift
import Submission.Work.DSF1.Cech.CechOLocal
import Submission.Work.DSF1.Cech.isIsoDeletion_Qo
import Submission.Work.DSF1.Cech.isAffineOpen_Eobj
import Submission.Work.DSF1.Cech.specPresheaf_loc_affine
import Submission.Work.DSF1.Cech.exists_pow_smul_mem_range_locO
import Submission.Work.DSF1.Cech.eq_zero_of_loc_eq_zero_O
import Submission.Work.DSF1.Cech.quasiIso_coaugMapO
import Submission.Work.DSF1.Cech.cechAffineCover_aux

/-!
# The Čech complex of a finite affine cover of `Spec R` resolves `R`

This is the file of the theorem `Work.DSF1.Cech.cechAffineCover_quasiIso`.  The mathematical
content and the intermediate lemmas are explained in `cechAffineCover_aux`; here they are
assembled into the statement: for a finite cover of `Spec R` by affine opens `U` there is a
chain map `cc` from `R[0]` to the Čech complex of `U` whose degree zero component is the
coaugmentation and which is a quasi-isomorphism.
-/

namespace Work.DSF1.Cech

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

theorem cechAffineCover_quasiIso (R : Type u) [CommRing R] {ι : Type u} [Finite ι]
    (U : ι → (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens)
    (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i))
    (hcov : sSup (Set.range U) = ⊤) :
    ∃ cc : (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
          (ModuleCat.of R R) ⟶
        DSMap.cechZ R (AlgebraicGeometry.Spec (CommRingCat.of R))
          (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of R))) U,
      CategoryTheory.CategoryStruct.comp (cc.f 0)
        ((DSMap.cech R (AlgebraicGeometry.Spec (CommRingCat.of R))
          (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of R))) U).extendXIso
            ComplexShape.embeddingUpNat (i := 0) rfl).hom =
        CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).hom
          (DSMap.coaug0 R (AlgebraicGeometry.Spec (CommRingCat.of R))
            (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of R))) U) ∧
      HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) cc := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  -- The family of elements whose basic open lies in some member of the cover.
  let G : Set R := setOf fun g : R => ∃ i : ι, PrimeSpectrum.basicOpen g ≤ U i
  have hG : ∀ g ∈ G, ∃ i : ι, PrimeSpectrum.basicOpen g ≤ U i := fun g hg => hg
  have hspan : Ideal.span G = ⊤ := span_basicOpen_le_generates R U hcov
  -- The unit case for every localized complex.
  have hunit : ∀ g ∈ G,
      (coaug U (Qo (specPresheaf R) (PrimeSpectrum.basicOpen g)) ≫
          (cechOQ R U (PrimeSpectrum.basicOpen g)).d 0 1 = 0) ∧
        (∀ (n : ℕ) (s : (cechOQ R U (PrimeSpectrum.basicOpen g)).X (n + 1)),
          (cechOQ R U (PrimeSpectrum.basicOpen g)).d (n + 1) (n + 2) s = 0 →
            ∃ t : (cechOQ R U (PrimeSpectrum.basicOpen g)).X n,
              (cechOQ R U (PrimeSpectrum.basicOpen g)).d n (n + 1) t = s) ∧
        Function.Injective (coaug U (Qo (specPresheaf R)
          (PrimeSpectrum.basicOpen g))).hom ∧
        (∀ s : (cechOQ R U (PrimeSpectrum.basicOpen g)).X 0,
          (cechOQ R U (PrimeSpectrum.basicOpen g)).d 0 1 s = 0 →
            ∃ z : (Qo (specPresheaf R) (PrimeSpectrum.basicOpen g)).obj (op ⊤),
              (coaug U (Qo (specPresheaf R) (PrimeSpectrum.basicOpen g))).hom z = s) :=
    fun g hg => unitCase_Qo R U (PrimeSpectrum.basicOpen g) (hG g hg).choose
      (hG g hg).choose_spec
  -- Clearing denominators, componentwise.
  have hsurj_comp : ∀ g ∈ G, ∀ (n : ℕ)
      (x : (E U).obj (op (SimplexCategory.mk n)) |>.I),
      ∀ z : (specPresheaf R).obj (op (Eobj U n x ⊓ PrimeSpectrum.basicOpen g)),
        ∃ (k : ℕ) (t : (specPresheaf R).obj (op (Eobj U n x))),
          ((specPresheaf R).map (homOfLE (inf_le_left :
            Eobj U n x ⊓ PrimeSpectrum.basicOpen g ≤ Eobj U n x)).op).hom t = g ^ k • z :=
    fun g _ n x z => (specPresheaf_loc_affine R (isAffineOpen_Eobj R U hU n x) g).1 z
  have hker_comp : ∀ g ∈ G, ∀ (n : ℕ)
      (x : (E U).obj (op (SimplexCategory.mk n)) |>.I)
      (t : (specPresheaf R).obj (op (Eobj U n x))),
      ((specPresheaf R).map (homOfLE (inf_le_left :
        Eobj U n x ⊓ PrimeSpectrum.basicOpen g ≤ Eobj U n x)).op).hom t = 0 →
        ∃ k : ℕ, g ^ k • t = 0 :=
    fun g _ n x t ht => (specPresheaf_loc_affine R (isAffineOpen_Eobj R U hU n x) g).2 t ht
  have hsurj : ∀ g ∈ G, ∀ (n : ℕ) (z : (cechOQ R U (PrimeSpectrum.basicOpen g)).X n),
      ∃ (k : ℕ) (t : (cechO R U).X n),
        (locO R U (PrimeSpectrum.basicOpen g)).f n t = g ^ k • z :=
    fun g hg n z => exists_pow_smul_mem_range_locO R U (PrimeSpectrum.basicOpen g) g
      (hsurj_comp g hg) n z
  have hker : ∀ g ∈ G, ∀ (n : ℕ) (t : (cechO R U).X n),
      (locO R U (PrimeSpectrum.basicOpen g)).f n t = 0 → ∃ k : ℕ, g ^ k • t = 0 :=
    fun g hg n t ht => eq_zero_of_loc_eq_zero_O R U (PrimeSpectrum.basicOpen g) g
      (hker_comp g hg) n t ht
  -- Exactness in positive degrees.
  have hexactpos : ∀ (n : ℕ) (s : (cechO R U).X (n + 1)),
      (cechO R U).d (n + 1) (n + 2) s = 0 →
        ∃ t : (cechO R U).X n, (cechO R U).d n (n + 1) t = s :=
    exact_positive_cechO R U G hspan hsurj hker (fun g hg => (hunit g hg).2.1)
  -- The degree zero statements.
  have h1 : ∀ q : R, (coaugO R U).hom q = 0 → q = 0 :=
    coaugO_injective_of_localized R U G hspan (fun g hg => (hunit g hg).2.2.1)
      (fun g _ q hq => eta_top_global_eq_zero R g q hq)
  have h2 : ∀ s : (cechO R U).X 0, (cechO R U).d 0 1 s = 0 →
      ∃ q : R, (coaugO R U).hom q = s :=
    coaugO_surjective_of_localized R U G hspan (fun g hg => (hunit g hg).2.2.2)
      (fun g _ z => specPresheaf_loc_lift R g z) (fun g hg t ht => hker g hg 0 t ht)
  -- The coaugmentation is a quasi-isomorphism in `ℕ`-degrees.
  have hqi : HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℕ)
      (coaugMapO R U) := quasiIso_coaugMapO R U hexactpos h1 h2
  -- Transport to `ℤ`-degrees.
  refine ⟨(HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (ModuleCat.of R R)
      0 0 rfl).inv ≫ HomologicalComplex.extendMap (coaugMapO R U) ComplexShape.embeddingUpNat,
    ?_, ?_⟩
  · -- the compatibility with the coaugmentation
    show ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (ModuleCat.of R R)
        0 0 rfl).inv ≫ HomologicalComplex.extendMap (coaugMapO R U)
          ComplexShape.embeddingUpNat).f 0 ≫
        ((cechO R U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).hom ≫
        coaugO R U
    rw [HomologicalComplex.comp_f]
    rw [HomologicalComplex.extendSingleIso_inv_f (ComplexShape.embeddingUpNat)
      (ModuleCat.of R R) 0 0 rfl]
    rw [HomologicalComplex.extendMap_f (coaugMapO R U) ComplexShape.embeddingUpNat
      (i := 0) (i' := 0) rfl]
    rw [CochainComplex.single₀ObjXSelf, coaugMapO_f_zero R U]
    simp only [Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id]
    simp
  · -- the quasi-isomorphism
    show QuasiIso ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      (ModuleCat.of R R) 0 0 rfl).inv ≫ HomologicalComplex.extendMap (coaugMapO R U)
        ComplexShape.embeddingUpNat)
    haveI : QuasiIso (HomologicalComplex.extendMap (coaugMapO R U)
        ComplexShape.embeddingUpNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff (coaugMapO R U)
        ComplexShape.embeddingUpNat).2 hqi
    infer_instance

end Work.DSF1.Cech
