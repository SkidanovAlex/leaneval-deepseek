import Mathlib
import Submission.Work.DSEQ0.AugDefs
import Submission.Work.DSF1.Sheaf.FlasqueDevissage
import Submission.Work.DSF1.Sheaf.cechTrivAll_of_restrP
import Submission.Work.DSEQ0.cechTrivAll_sectionsV
import Submission.Work.DSEQ0.cechSh_sectionsV_iso
import Submission.Work.DSEQ0.sectionsV_mono_app
import Submission.Work.DSEQ0.coaugAb_comp_d
import Submission.Work.DSEQ0.cech_d_comp_pi
import Submission.Work.DSEQ0.coaugAb_sectionsV_unit_case

/-!
# The augmented Čech complex of the structure sheaf is a resolution

This module contains the development of the proof of `Work.DSEQ0.quasiIso_augZ`, phrased in
terms of the private copies `Work.DSEQ0.C.*` of the definitions (see `AugBasic.lean`); the
final file `Submission/Work/DSEQ0/quasiIso_augZ.lean` transfers the result to the original
definitions, which are definitionally equal.

## The mathematics

Let `X` be a scheme, `U : ι → X.Opens` a covering family, `S = (j_⊤)_* 𝒪_⊤`, and let
`Č = (cechComplexFunctor U).obj (cechShPresheaf X)` be the sheaf-level Čech complex, so that
`Čⁿ = ∏_{x : Fin (n+1) → ι} (j_{U_x})_* 𝒪`.  The augmentation `aug : S ⟶ Č` is a
quasi-isomorphism: the augmented Čech complex is a resolution of the structure sheaf.

The proof never computes stalks.  It rests on two facts:

* for every open `V` contained in some member (`V ≤ U i₀`), the complex of *sections* of `Č`
  over `V` is contractible (the "unit case"), transferred along the canonical isomorphism
  between `Γ(V, Čⁿ)` and the presheaf-level Čech complex of the coefficients
  `W ↦ Γ(V, (j_W)_* 𝒪_W)` (`Work.DSEQ0.cechSh_sectionsV_iso`);
* exactness of a sequence of sheaves of `𝒪_X`-modules can be tested by the elementwise
  criterion `ShortComplex.exact_iff_epi_kernel_lift`; a morphism is epi as soon as every
  section is locally in its image (`epi_of_local_lift` below), and local triviality of cocycles
  is available on any open contained in a member of the covering family.
-/

namespace Work.DSEQ0

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Limits Opposite

open scoped Simplicial BigOperators

universe u

variable (X : AlgebraicGeometry.Scheme.{u})

/-! ## Sections of morphisms of sheaves of modules -/

/-- The sections of a morphism of sheaves of `𝒪_X`-modules are natural with respect to
restriction. -/
lemma sections_app_naturality {M N : X.Modules} (φ : M ⟶ N) {V V' : X.Opens} (h : V' ≤ V)
    (s : (Scheme.Modules.presheaf M).obj (Opposite.op V)) :
    (Scheme.Modules.Hom.app φ V') ((Scheme.Modules.presheaf M).map (homOfLE h).op s)
      = (Scheme.Modules.presheaf N).map (homOfLE h).op
          ((Scheme.Modules.Hom.app φ V) s) := by
  have hnat := (Scheme.Modules.Hom.mapPresheaf φ).naturality (homOfLE h).op
  have h2 := congrArg
    (fun (g : (Scheme.Modules.presheaf M).obj (Opposite.op V) ⟶
        (Scheme.Modules.presheaf N).obj (Opposite.op V')) => (ConcreteCategory.hom g) s) hnat
  simpa only [AddCommGrpCat.comp_apply, Scheme.Modules.mapPresheaf_app] using h2

/-- **Separation for sheaves of `𝒪_X`-modules.**  Two sections of a sheaf of modules which agree
on a family of opens covering `V` agree. -/
lemma sections_sep {M : X.Modules} {ι' : Type u} (W : ι' → X.Opens) {V : X.Opens}
    (hW : ∀ i, W i ≤ V) (hcov : V ≤ iSup W)
    {s t : (Scheme.Modules.presheaf M).obj (Opposite.op V)}
    (h : ∀ i, (Scheme.Modules.presheaf M).map (homOfLE (hW i)).op s
      = (Scheme.Modules.presheaf M).map (homOfLE (hW i)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq'
    (⟨Scheme.Modules.presheaf M, Scheme.Modules.isSheaf M⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    W V (fun i => homOfLE (hW i)) hcov s t h

/-! ## Epimorphisms from local surjectivity of sections -/

/-- **Local surjectivity implies epimorphy.**  If a morphism `φ : A ⟶ B` of sheaves of
`𝒪_X`-modules has the property that every section of `B` over an open `V` is, locally on a
cover of `V` by opens `W j`, the image of a section of `A`, then `φ` is an epimorphism. -/
theorem epi_of_local_lift {A B : X.Modules} (φ : A ⟶ B)
    (h : ∀ (V : X.Opens) (b : (Scheme.Modules.presheaf B).obj (Opposite.op V)),
      ∃ (ι' : Type u) (W : ι' → X.Opens) (hW : ∀ j, W j ≤ V) (hcov : V ≤ iSup W),
        ∀ j, ∃ a : (Scheme.Modules.presheaf A).obj (Opposite.op (W j)),
          (Scheme.Modules.Hom.app φ (W j)) a
            = (Scheme.Modules.presheaf B).map (homOfLE (hW j)).op b) :
    Epi φ := by
  refine ⟨fun {T} p q hpq => ?_⟩
  refine Scheme.Modules.hom_ext p q (fun V => ?_)
  ext b
  obtain ⟨ι', W, hW, hcov, hlift⟩ := h V b
  refine sections_sep X W hW hcov (fun j => ?_)
  obtain ⟨a, ha⟩ := hlift j
  rw [← sections_app_naturality X p (hW j) b, ← sections_app_naturality X q (hW j) b, ← ha]
  have h1 : (ConcreteCategory.hom (Scheme.Modules.Hom.app (φ ≫ p) (W j))) a
      = (ConcreteCategory.hom (Scheme.Modules.Hom.app p (W j)))
          ((ConcreteCategory.hom (Scheme.Modules.Hom.app φ (W j))) a) := by
    rw [Scheme.Modules.Hom.comp_app (U := W j) φ p, AddCommGrpCat.comp_apply]
  have h2 : (ConcreteCategory.hom (Scheme.Modules.Hom.app (φ ≫ q) (W j))) a
      = (ConcreteCategory.hom (Scheme.Modules.Hom.app q (W j)))
          ((ConcreteCategory.hom (Scheme.Modules.Hom.app φ (W j))) a) := by
    rw [Scheme.Modules.Hom.comp_app (U := W j) φ q, AddCommGrpCat.comp_apply]
  have h3 : (ConcreteCategory.hom (Scheme.Modules.Hom.app (φ ≫ p) (W j))) a
      = (ConcreteCategory.hom (Scheme.Modules.Hom.app (φ ≫ q) (W j))) a := by
    rw [hpq]
  exact h1.symm.trans (h3.trans h2)

namespace C

variable {ι : Type u}

/-! ## The augmentation as a map into the degree-`0` cycles -/

/-- The degree-`0` component of `augN` is the augmentation. -/
lemma augN_f_zero (U : ι → X.Opens) (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    (augN X U h).f 0 = aug0 X U := by
  rw [augN, HomologicalComplex.mkHomFromSingle_f]
  simp

/-- The augmentation of the Čech complex, as a map into the degree-`0` cycles. -/
noncomputable def augCycles (U : ι → X.Opens) (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    (cechShPresheaf X).obj (op ⊤) ⟶ (cechSh X U).cycles 0 :=
  (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
      ((cechShPresheaf X).obj (op ⊤))).inv ≫ HomologicalComplex.cyclesMap (augN X U h) 0

/-- The map into the cycles is the augmentation. -/
lemma augCycles_iCycles (U : ι → X.Opens) (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    augCycles X U h ≫ (cechSh X U).iCycles 0 = aug0 X U := by
  have hstep : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
      ((cechShPresheaf X).obj (op ⊤))).inv ≫
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0).obj
        ((cechShPresheaf X).obj (op ⊤))).iCycles 0 = 𝟙 ((cechShPresheaf X).obj (op ⊤)) := by
    rw [HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles, CochainComplex.single₀ObjXSelf]
    rfl
  rw [augCycles, Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, hstep,
    Category.id_comp, augN_f_zero]

/-- `cyclesMap` in degree `0`, with the domain identification made explicit. -/
lemma cyclesMap_augN_zero (U : ι → X.Opens) (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    HomologicalComplex.cyclesMap (augN X U h) 0 =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
        ((cechShPresheaf X).obj (op ⊤))).hom ≫ augCycles X U h := by
  rw [augCycles, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **The augmentation induces an isomorphism on `H⁰`** as soon as it is a mono- and
epimorphism onto the degree-`0` cycles. -/
theorem isIso_homologyMap_augN_zero (U : ι → X.Opens) (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0)
    [Mono (augCycles X U h)] [Epi (augCycles X U h)] :
    IsIso (HomologicalComplex.homologyMap (augN X U h) 0) := by
  have hhom : HomologicalComplex.homologyMap (augN X U h) 0 =
      (CochainComplex.isoHomologyπ₀ ((CochainComplex.single₀ X.Modules).obj
          ((cechShPresheaf X).obj (op ⊤)))).inv ≫
        HomologicalComplex.cyclesMap (augN X U h) 0 ≫
        (CochainComplex.isoHomologyπ₀ (cechSh X U)).hom := by
    rw [← cancel_mono (CochainComplex.isoHomologyπ₀ (cechSh X U)).inv,
      CochainComplex.isoHomologyπ₀_inv_naturality]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : IsIso (augCycles X U h) := isIso_of_mono_of_epi _
  rw [hhom, cyclesMap_augN_zero X U h]
  infer_instance

/-- **The augmentation in `ℕ`-degrees is a quasi-isomorphism**, given the exactness of the Čech
complex in positive degrees and that the augmentation is an isomorphism onto the cycles. -/
theorem quasiIso_augN_of (U : ι → X.Opens) (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0)
    (hexact : ∀ n : ℕ, (cechSh X U).ExactAt (n+1))
    [Mono (augCycles X U h)] [Epi (augCycles X U h)] :
    QuasiIso (augN X U h) := by
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
      rw [quasiIsoAt_iff_isIso_homologyMap]
      exact isIso_homologyMap_augN_zero X U h
  | succ n =>
      rw [quasiIsoAt_iff_exactAt (augN X U h) (n+1)
        (CochainComplex.exactAt_succ_single_obj ((cechShPresheaf X).obj (op ⊤)) n)]
      exact hexact n

/-- **The augmentation in `ℤ`-degrees is a quasi-isomorphism** if it is in `ℕ`-degrees (the two
complexes are related by the extension functor `ComplexShape.embeddingUpNat`). -/
theorem quasiIso_augZ_of (U : ι → X.Opens) (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0)
    (hN : QuasiIso (augN X U h)) : QuasiIso (augZ X U h) := by
  haveI : QuasiIso (HomologicalComplex.extendMap (augN X U h) ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff (augN X U h) ComplexShape.embeddingUpNat).2 hN
  exact quasiIso_comp _ _

/-! ## The local inputs and the assembly of the quasi-isomorphism -/

/-- **Local triviality of Čech cocycles.**  On an open `V` contained in a member `U i` of the
covering family, every cocycle of the Čech complex is a coboundary. -/
def LocalTrivial (U : ι → X.Opens) : Prop :=
  ∀ (V : X.Opens) (i : ι), V ≤ U i → ∀ n : ℕ,
    ∀ z : (sectionsV X V).obj ((cechSh X U).X (n+1)),
      (sectionsV X V).map ((cechSh X U).d (n+1) (n+2)) z = 0 →
      ∃ t : (sectionsV X V).obj ((cechSh X U).X n),
        (sectionsV X V).map ((cechSh X U).d n (n+1)) t = z

/-- **The degree-`0` unit case.**  On an open `V` contained in a member `U i`, the augmentation
is injective and every degree-`0` cocycle is a value of the augmentation. -/
def LocalCoaug (U : ι → X.Opens) : Prop :=
  (∀ (V : X.Opens) (i : ι), V ≤ U i →
      Function.Injective (ConcreteCategory.hom (Scheme.Modules.Hom.app (aug0 X U) V))) ∧
    (∀ (V : X.Opens) (i : ι), V ≤ U i →
      ∀ z : (sectionsV X V).obj ((cechSh X U).X 0),
        (sectionsV X V).map ((cechSh X U).d 0 1) z = 0 →
        ∃ s : (sectionsV X V).obj ((cechShPresheaf X).obj (op ⊤)),
          (sectionsV X V).map (aug0 X U) s = z)

/-- **Injectivity of sections of a monomorphism of sheaves of modules.** -/
def MonoSections : Prop :=
  ∀ {M N : X.Modules} (φ : M ⟶ N), Mono φ → ∀ V : X.Opens,
    Function.Injective (ConcreteCategory.hom (Scheme.Modules.Hom.app φ V))

/-- The sections of the kernel inclusion are killed by the map itself. -/
lemma sections_map_kernel_ι_comp {M N : X.Modules} (φ : M ⟶ N) (V : X.Opens)
    (w : (sectionsV X V).obj (kernel φ)) :
    (sectionsV X V).map φ ((sectionsV X V).map (kernel.ι φ) w) = 0 := by
  have h : (sectionsV X V).map (kernel.ι φ) ≫ (sectionsV X V).map φ = 0 := by
    rw [← Functor.map_comp, CategoryTheory.Limits.kernel.condition]
    exact Functor.map_zero (sectionsV X V) (kernel φ) N
  simpa using
    congrArg (fun (g : (sectionsV X V).obj (kernel φ) ⟶ (sectionsV X V).obj N) =>
      (ConcreteCategory.hom g) w) h

/-- The sections of the cycle inclusion are cycles. -/
lemma sections_map_iCycles_d {K : CochainComplex X.Modules ℕ} (i : ℕ) (V : X.Opens)
    (w : (sectionsV X V).obj (K.cycles i)) :
    (sectionsV X V).map (K.d i (i+1)) ((sectionsV X V).map (K.iCycles i) w) = 0 := by
  have h : (sectionsV X V).map (K.iCycles i) ≫ (sectionsV X V).map (K.d i (i+1)) = 0 := by
    rw [← Functor.map_comp, HomologicalComplex.iCycles_d]
    exact Functor.map_zero (sectionsV X V) (K.cycles i) (K.X (i+1))
  simpa using
    congrArg (fun (g : (sectionsV X V).obj (K.cycles i) ⟶
        (sectionsV X V).obj (K.X (i+1))) => (ConcreteCategory.hom g) w) h

/-- A morphism of sheaves of `𝒪_X`-modules whose sections are injective on every open is a
monomorphism. -/
theorem mono_of_sections_injective {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ V : X.Opens, Function.Injective
      (ConcreteCategory.hom (Scheme.Modules.Hom.app φ V))) : Mono φ := by
  refine ⟨fun {T} p q hpq => ?_⟩
  refine Scheme.Modules.hom_ext p q (fun V => ?_)
  ext s
  exact h V (by
    rw [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app, hpq,
      Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply])

/-- **The augmentation is a monomorphism**, from the degree-`0` unit case (via separation for
sheaves of modules). -/
theorem mono_aug0_of (U : ι → X.Opens) (hcov : iSup U = ⊤) (hco : LocalCoaug X U) :
    Mono (aug0 X U) := by
  refine mono_of_sections_injective X (aug0 X U) (fun V s t hst => ?_)
  refine sections_sep X (fun i : ι => V ⊓ U i) (fun i => inf_le_left) ?_ (fun i => ?_)
  · have hsup : iSup (fun i : ι => V ⊓ U i) = V := by rw [← inf_iSup_eq, hcov, inf_top_eq]
    exact le_of_eq hsup.symm
  · refine hco.1 (V ⊓ U i) i inf_le_right ?_
    rw [sections_app_naturality X (aug0 X U) inf_le_left s,
      sections_app_naturality X (aug0 X U) inf_le_left t, hst]

/-- **Exactness of the Čech complex in positive degrees**, from the local triviality of
cocycles. -/
theorem exactAt_succ_of_localTriv (U : ι → X.Opens) (hmono : MonoSections X)
    (hlocal : LocalTrivial X U) (hcov : iSup U = ⊤) (n : ℕ) :
    (cechSh X U).ExactAt (n+1) := by
  have hp : (ComplexShape.up ℕ).prev (n + 1) = n :=
    ComplexShape.prev_eq' (c := ComplexShape.up ℕ) (by rfl)
  have hn : (ComplexShape.up ℕ).next (n + 1) = n + 2 :=
    ComplexShape.next_eq' (c := ComplexShape.up ℕ) (by rfl)
  rw [HomologicalComplex.exactAt_iff' (cechSh X U) n (n+1) (n+2) hp hn,
    ShortComplex.exact_iff_epi_kernel_lift]
  set S : ShortComplex X.Modules := (cechSh X U).sc' n (n+1) (n+2) with hS
  refine epi_of_local_lift X _ (fun V z => ?_)
  refine ⟨ι, (fun i : ι => V ⊓ U i), (fun i => inf_le_left), ?_, ?_⟩
  · have hsup : iSup (fun i : ι => V ⊓ U i) = V := by rw [← inf_iSup_eq, hcov, inf_top_eq]
    exact le_of_eq hsup.symm
  · intro i
    obtain ⟨t, ht⟩ := hlocal (V ⊓ U i) i inf_le_right n
      ((kernel.ι S.g).app (V ⊓ U i) ((kernel S.g).presheaf.map
        (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op z))
      (sections_map_kernel_ι_comp X S.g (V ⊓ U i)
        ((kernel S.g).presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op z))
    refine ⟨t, ?_⟩
    refine hmono (kernel.ι S.g) inferInstance (V ⊓ U i) ?_
    rw [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app,
      CategoryTheory.Limits.kernel.lift_ι]
    exact ht

/-- **The augmentation is an isomorphism onto the degree-`0` cycles**, from the degree-`0`
unit case. -/
theorem mono_epi_augCycles_of (U : ι → X.Opens) (hcov : iSup U = ⊤) (hco : LocalCoaug X U)
    (hmono : MonoSections X) (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) :
    Mono (augCycles X U h) ∧ Epi (augCycles X U h) := by
  have hm : Mono (aug0 X U) := mono_aug0_of X U hcov hco
  have hmc : Mono (augCycles X U h) := by
    refine ⟨fun {Z} p q hpq => ?_⟩
    refine hm.right_cancellation p q ?_
    rw [← augCycles_iCycles X U h, ← Category.assoc, ← Category.assoc, hpq]
  refine ⟨hmc, ?_⟩
  refine epi_of_local_lift X (augCycles X U h) (fun V z => ?_)
  refine ⟨ι, (fun i : ι => V ⊓ U i), (fun i => inf_le_left), ?_, ?_⟩
  · have hsup : iSup (fun i : ι => V ⊓ U i) = V := by rw [← inf_iSup_eq, hcov, inf_top_eq]
    exact le_of_eq hsup.symm
  · intro i
    obtain ⟨s, hs⟩ := hco.2 (V ⊓ U i) i inf_le_right
      (((cechSh X U).iCycles 0).app (V ⊓ U i) (((cechSh X U).cycles 0).presheaf.map
        (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op z))
      (sections_map_iCycles_d X 0 (V ⊓ U i) (((cechSh X U).cycles 0).presheaf.map
        (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op z))
    refine ⟨s, ?_⟩
    refine hmono ((cechSh X U).iCycles 0) inferInstance (V ⊓ U i) ?_
    rw [← AddCommGrpCat.comp_apply, ← Scheme.Modules.Hom.comp_app, augCycles_iCycles X U h]
    exact hs

/-! ## Instantiation of the local inputs and the final assembly -/

/-- **The augmentation is a cycle.**  The composite `aug0 ≫ d 0 1` is zero: it is zero on
sections over any open, because the chain map of `cechSh_sectionsV_iso` identifies it with
`coaugAb ≫ d 0 1 = 0`. -/
theorem aug0_comp_d (U : ι → X.Opens) : aug0 X U ≫ (cechSh X U).d 0 1 = 0 := by
  refine Pi.hom_ext _ _ (fun y => ?_)
  simp only [zero_comp]
  change (aug0 X U ≫ (cechSh X U).d 0 1) ≫
      Pi.π (fun z => (C.cechShPresheaf X).obj (op (Work.DSF1.Cech.Eobj U 1 z))) y = 0
  rw [Category.assoc]
  rw [show (cechSh X U).d 0 1 ≫ Pi.π (fun z => (C.cechShPresheaf X).obj
        (op (Work.DSF1.Cech.Eobj U 1 z))) y =
      ∑ a : Fin 2, (-1:ℤ)^(a:ℕ) •
        (Pi.π (fun z => (C.cechShPresheaf X).obj (op (Work.DSF1.Cech.Eobj U 0 z)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f y) ≫
          (C.cechShPresheaf X).map
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).φ y).op) from
      cech_d_comp_pi X U 0 y]
  rw [Preadditive.comp_sum]
  rw [Finset.sum_congr rfl (fun a _ => Preadditive.comp_zsmul _ _ _)]
  have hterm : ∀ a : Fin 2,
      (aug0 X U ≫ (Pi.π (fun z => (C.cechShPresheaf X).obj
              (op (Work.DSF1.Cech.Eobj U 0 z)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f y) ≫
          (C.cechShPresheaf X).map
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).φ y).op)) =
        (C.cechShPresheaf X).map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 1 y ≤ ⊤)).op := by
    intro a
    rw [← Category.assoc]
    rw [show aug0 X U ≫ Pi.π (fun z => (C.cechShPresheaf X).obj
          (op (Work.DSF1.Cech.Eobj U 0 z)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f y) =
        (C.cechShPresheaf X).map (homOfLE le_top).op from Pi.lift_comp_π _ _]
    rw [← (C.cechShPresheaf X).map_comp]
    congr 1
  simp only [hterm]
  rw [Fin.sum_univ_two]
  simp

/-- **Local triviality of the Čech cocycles**, from the contractibility of the Čech complex of
the sections over an open contained in a member of the covering family. -/
theorem localTrivial (U : ι → X.Opens) : LocalTrivial X U := by
  intro V i hV n z hz
  obtain ⟨e, he, -⟩ := cechSh_sectionsV_iso X U V
  haveI := he
  have htriv := Work.DSF1.Sheaf.cechTrivAll_of_iso e (cechTrivAll_sectionsV X U V i hV)
  obtain ⟨t, ht⟩ := htriv n z (by simpa using hz)
  exact ⟨t, by simpa using ht⟩

/-- **Injectivity of the sections of monomorphisms.** -/
theorem monoSections : MonoSections X :=
  fun {M N} φ hmono V => @sectionsV_mono_app X M N φ hmono V

/-- **Exactness of the Čech complex in positive degrees.** -/
theorem exactAt_succ_cechSh (U : ι → X.Opens) (hcov : iSup U = ⊤) (n : ℕ) :
    (cechSh X U).ExactAt (n+1) :=
  exactAt_succ_of_localTriv X U (monoSections X) (localTrivial X U) hcov n

/-- **The augmentation of the sheaf-level Čech complex is a quasi-isomorphism in `ℕ`-degrees.** -/
theorem quasiIso_augN (U : ι → X.Opens) (hcov : iSup U = ⊤)
    (h : aug0 X U ≫ (cechSh X U).d 0 1 = 0) (hlocal0 : LocalCoaug X U) :
    QuasiIso (augN X U h) := by
  obtain ⟨hmc, hec⟩ := mono_epi_augCycles_of X U hcov hlocal0 (monoSections X) h
  haveI := hmc
  haveI := hec
  exact quasiIso_augN_of X U h (fun n => exactAt_succ_cechSh X U hcov n)

/-- **The augmentation of the sheaf-level Čech complex is a quasi-isomorphism in `ℤ`-degrees.** -/
theorem quasiIso_augZ_C (U : ι → X.Opens) (hcov : iSup U = ⊤) (hlocal0 : LocalCoaug X U) :
    ∃ h : aug0 X U ≫ (cechSh X U).d 0 1 = 0, QuasiIso (augZ X U h) :=
  ⟨aug0_comp_d X U, quasiIso_augZ_of X U _ (quasiIso_augN X U hcov _ hlocal0)⟩

/-- **The degree-`0` unit case** for the augmentation, obtained from the corresponding statement
(concerning the presheaf-level Čech complex of the coefficients `W ↦ Γ(W ⊓ V, 𝒪_X)`) by
transport along the comparison isomorphism of `cechSh_sectionsV_iso`. -/
theorem localCoaug (U : ι → X.Opens) : LocalCoaug X U := by
  refine ⟨fun V i hV s t hst => ?_, fun V i hV z hz => ?_⟩
  · obtain ⟨e, he, hcompat⟩ := cechSh_sectionsV_iso X U V
    haveI := he
    have hRV := (coaugAb_sectionsV_unit_case X U V i hV).1
    refine hRV ?_
    have hcomm1 : coaugAb X U (C.cechShPresheaf X ⋙ sectionsV X V) s
        = (e.hom.f 0) ((Scheme.Modules.Hom.app (aug0 X U) V) s) := by
      rw [← hcompat, AddCommGrpCat.comp_apply]
      rfl
    have hcomm2 : coaugAb X U (C.cechShPresheaf X ⋙ sectionsV X V) t
        = (e.hom.f 0) ((Scheme.Modules.Hom.app (aug0 X U) V) t) := by
      rw [← hcompat, AddCommGrpCat.comp_apply]
      rfl
    rw [hcomm1, hcomm2, hst]
  · obtain ⟨e, he, hcompat⟩ := cechSh_sectionsV_iso X U V
    haveI := he
    have hsurj := (coaugAb_sectionsV_unit_case X U V i hV).2
    have hz' : ((cechComplexFunctor U).obj (C.cechShPresheaf X ⋙ sectionsV X V)).d 0 1
        (e.hom.f 0 z) = 0 := by
      have hc := congrArg (fun g => (ConcreteCategory.hom g) z) (e.hom.comm 0 1)
      simp only [AddCommGrpCat.comp_apply] at hc
      rw [hc]
      have hz2 : (sectionsV X V).map
          (((cechComplexFunctor U).obj (C.cechShPresheaf X)).d 0 1) z = 0 := hz
      erw [hz2]
      exact map_zero _
    obtain ⟨s, hs⟩ := hsurj (e.hom.f 0 z) hz'
    refine ⟨s, ?_⟩
    have hcomm1 : coaugAb X U (C.cechShPresheaf X ⋙ sectionsV X V) s
        = (e.hom.f 0) ((Scheme.Modules.Hom.app (aug0 X U) V) s) := by
      rw [← hcompat, AddCommGrpCat.comp_apply]
      rfl
    have heq : (e.hom.f 0) ((Scheme.Modules.Hom.app (aug0 X U) V) s) = (e.hom.f 0) z := by
      rw [← hcomm1, hs]
    have hcomp : e.hom.f 0 ≫ e.inv.f 0 = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, e.hom_inv_id, HomologicalComplex.id_f]
    have h5 := congrArg (fun y => (ConcreteCategory.hom (e.inv.f 0)) y) heq
    simp only [← AddCommGrpCat.comp_apply, hcomp, AddCommGrpCat.id_apply] at h5
    exact h5

/-- **The augmentation of the sheaf-level Čech complex is a quasi-isomorphism.** -/
theorem quasiIso_augZ_C_uncond (U : ι → X.Opens) (hcov : iSup U = ⊤) :
    ∃ h : aug0 X U ≫ (cechSh X U).d 0 1 = 0, QuasiIso (augZ X U h) :=
  quasiIso_augZ_C X U hcov (localCoaug X U)

end C

end Work.DSEQ0
