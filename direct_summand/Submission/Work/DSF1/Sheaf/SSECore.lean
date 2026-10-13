import Mathlib
import ChallengeDeps
import Submission.Work.DSF1.Sheaf.SSEBasic

/-!
# Auxiliary lemmas for the Čech descent (`DSF1` lemma `sections_surjective_of_cechTriv`)

Transport of sections along equalities of opens, the pair-tuples of the Čech nerve, and the
components of the differential `d 0 1` (elementwise).
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Sheaf

variable {X : Scheme.{u}} {ι : Type u}

lemma piFin1' (f : Fin 1 → X.Opens) : (∏ᶜ f : X.Opens) = f 0 := by
  apply le_antisymm
  · exact (Pi.π f 0).down.down
  · refine (Pi.lift (fun a : Fin 1 => homOfLE ?_) : f 0 ⟶ (∏ᶜ f : X.Opens)).down.down
    fin_cases a
    exact le_rfl

lemma resAt_self (M : SheafOfModules X.ringCatSheaf) (V : X.Opens) :
    resAt M (le_refl V) = 𝟙 (sectionsAt M V) := by
  have h : (homOfLE (le_refl V) : V ⟶ V) = 𝟙 V := Subsingleton.elim _ _
  dsimp only [resAt]
  rw [h]
  exact CategoryTheory.Functor.map_id _ _

lemma resAt_apply_eq (M : SheafOfModules X.ringCatSheaf) {V W : X.Opens} (h : V ≤ W) (h' : W ≤ V)
    (x : ↥(sectionsAt M W)) : (resAt M h') ((resAt M h) x) = x := by
  change ((resAt M h ≫ resAt M h') : sectionsAt M W ⟶ sectionsAt M W) x = x
  rw [resAt_comp,
    show resAt M (h'.trans h) = 𝟙 (sectionsAt M W) from by
      rw [show h'.trans h = le_refl W from Subsingleton.elim _ _, resAt_self]]
  rfl

/-- transport of sections along an equality of opens -/
noncomputable def trIso (M : SheafOfModules X.ringCatSheaf) {V W : X.Opens} (e : V = W) :
    sectionsAt M V ≅ sectionsAt M W :=
  ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.mapIso (eqToIso e.symm).op

lemma trIso_hom (M : SheafOfModules X.ringCatSheaf) {V W : X.Opens} (e : V = W) :
    (trIso M e).hom = ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map (eqToHom e.symm).op := rfl

lemma trIso_hom_eq_resAt (M : SheafOfModules X.ringCatSheaf) {V W : X.Opens} (e : V = W) :
    (trIso M e).hom = resAt M (le_of_eq e.symm) := by
  dsimp only [trIso, resAt]
  congr 1

lemma comp_map_op_trIso (M : SheafOfModules X.ringCatSheaf) {A B C : X.Opens} (e : A = B)
    {φ : A ⟶ C} (h : B ≤ C) :
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map φ.op ≫ (trIso M e).hom
      = resAt M h := by
  rw [trIso_hom]
  dsimp only [resAt]
  rw [← Functor.map_comp, ← op_comp]
  congr 1

noncomputable def pairTuple (U : ι → X.Opens) (i j : (cechN U 0).I) : (cechN U 1).I :=
  fun a => if (a : ℕ) = 0 then i 0 else j 0

lemma pairTuple_zero (U : ι → X.Opens) (i j : (cechN U 0).I) :
    pairTuple U i j 0 = i 0 := by
  simp [pairTuple]

lemma pairTuple_one (U : ι → X.Opens) (i j : (cechN U 0).I) :
    pairTuple U i j 1 = j 0 := by
  simp [pairTuple]

lemma pairTuple_comp_succAbove_zero (U : ι → X.Opens) (i j : (cechN U 0).I) :
    pairTuple U i j ∘ Fin.succAbove 0 = j := by
  funext a
  fin_cases a
  simp [Function.comp_apply, pairTuple]

lemma pairTuple_comp_succAbove_one (U : ι → X.Opens) (i j : (cechN U 0).I) :
    pairTuple U i j ∘ Fin.succAbove 1 = i := by
  funext a
  fin_cases a
  simp [Function.comp_apply, pairTuple]

lemma cechN1_obj_pair (U : ι → X.Opens) (i j : (cechN U 0).I) :
    (cechN U 1).obj (pairTuple U i j) = (cechN U 0).obj i ⊓ (cechN U 0).obj j := by
  rw [cechN_obj, cechN_obj, cechN_obj, piFin2, piFin1', piFin1']
  simp only [Function.comp_apply, pairTuple_zero, pairTuple_one]

lemma hom_sub_apply {G H : AddCommGrpCat.{u}} (f g : G ⟶ H) (x : ↥G) :
    (f - g) x = f x - g x := by simp

theorem d01_apply (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    (u : ↥(((cechComplexFunctor U).obj P).X 0)) (x : (cechN U 1).I) :
    (Pi.π (fun i : (cechN U 1).I => P.obj (op ((cechN U 1).obj i))) x)
        ((((cechComplexFunctor U).obj P).d 0 1) u)
      = (P.map (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 0)).φ x).op)
          ((Pi.π (fun i : (cechN U 0).I => P.obj (op ((cechN U 0).obj i))) (x ∘ Fin.succAbove 0)) u)
        - (P.map (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 1)).φ x).op)
          ((Pi.π (fun i : (cechN U 0).I => P.obj (op ((cechN U 0).obj i))) (x ∘ Fin.succAbove 1)) u) := by
  have h := congrArg (fun ψ => (ConcreteCategory.hom ψ) u) (d01_fac_morph (U := U) (P := P) x)
  rw [ConcreteCategory.comp_apply, hom_sub_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply] at h
  exact h


/-- The components of the projection are compatible with the transport along an equality
of the opens. -/
lemma trIso_π_apply (M : SheafOfModules X.ringCatSheaf) {I : Type u}
    (f : I → X.Opens) {a b : I} (hab : a = b) (u : ↥(∏ᶜ (fun i => sectionsAt M (f i)))) :
    (trIso M (congrArg f hab)).hom ((Pi.π (fun i => sectionsAt M (f i)) a) u)
      = (Pi.π (fun i => sectionsAt M (f i)) b) u := by
  subst hab
  rw [trIso_hom_eq_resAt]
  rw [show resAt M (le_of_eq (rfl : f a = f a).symm) = 𝟙 (sectionsAt M (f a)) from by
    rw [show (le_of_eq (rfl : f a = f a).symm : f a ≤ f a) = le_refl (f a) from
      Subsingleton.elim _ _, resAt_self]]
  rfl

theorem compat_of_d01 (U : ι → X.Opens) (M : SheafOfModules X.ringCatSheaf)
    (u : ↥((cechComplex U M).X 0)) (hu : ((cechComplex U M).d 0 1) u = 0)
    (i j : (cechN U 0).I) :
    resAt M (inf_le_left : (cechN U 0).obj i ⊓ (cechN U 0).obj j ≤ (cechN U 0).obj i)
        ((Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a)) i) u)
      = resAt M (inf_le_right : (cechN U 0).obj i ⊓ (cechN U 0).obj j ≤ (cechN U 0).obj j)
        ((Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a)) j) u) := by
  set x := pairTuple U i j with hx
  -- the two cofaces
  set φ0 := (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 0)).φ x) with hφ0
  set φ1 := (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 1)).φ x) with hφ1
  -- the tuples
  have e0 : x ∘ Fin.succAbove 0 = j := pairTuple_comp_succAbove_zero U i j
  have e1 : x ∘ Fin.succAbove 1 = i := pairTuple_comp_succAbove_one U i j
  -- the pair open
  have ep : (cechN U 1).obj x = (cechN U 0).obj i ⊓ (cechN U 0).obj j := cechN1_obj_pair U i j
  -- the elementwise relation
  have hraw : (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map φ0.op)
        ((Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a))
          (x ∘ Fin.succAbove 0)) u)
      = (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map φ1.op)
        ((Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a))
          (x ∘ Fin.succAbove 1)) u) := by
    have hd := d01_apply (U := U) (P := ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj)
      u x
    rw [hu] at hd
    simp only [map_zero] at hd
    exact sub_eq_zero.mp hd.symm
  -- morphism identity for the first coface
  have hΦ0 : (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map φ0.op) ≫
        (trIso M ep).hom
      = (trIso M (congrArg (fun t => (cechN U 0).obj t) e0)).hom ≫
        resAt M (inf_le_right : (cechN U 0).obj i ⊓ (cechN U 0).obj j ≤ (cechN U 0).obj j) := by
    rw [trIso_hom, trIso_hom, resAt]
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
    congr 1
  have hΦ1 : (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map φ1.op) ≫
        (trIso M ep).hom
      = (trIso M (congrArg (fun t => (cechN U 0).obj t) e1)).hom ≫
        resAt M (inf_le_left : (cechN U 0).obj i ⊓ (cechN U 0).obj j ≤ (cechN U 0).obj i) := by
    rw [trIso_hom, trIso_hom, resAt]
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
    congr 1
  have key0 : (trIso M ep).hom
      (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map φ0.op
        ((Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a))
          (x ∘ Fin.succAbove 0)) u))
      = resAt M (inf_le_right : (cechN U 0).obj i ⊓ (cechN U 0).obj j ≤ (cechN U 0).obj j)
        ((Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a)) j) u) := by
    have h := congrArg (fun ψ => (ConcreteCategory.hom ψ)
      ((ConcreteCategory.hom (Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a))
        (x ∘ Fin.succAbove 0))) u)) hΦ0
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    have h2 : (ConcreteCategory.hom (trIso M (congrArg (fun t => (cechN U 0).obj t) e0)).hom)
        ((ConcreteCategory.hom (Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a))
          (x ∘ Fin.succAbove 0))) u)
        = (ConcreteCategory.hom (Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a))
          j)) u := trIso_π_apply M (fun t => (cechN U 0).obj t) e0 u
    exact h.trans (congrArg (fun z => (ConcreteCategory.hom
      (resAt M (inf_le_right : (cechN U 0).obj i ⊓ (cechN U 0).obj j ≤ (cechN U 0).obj j))) z) h2)
  have key1 : (trIso M ep).hom
      (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map φ1.op
        ((Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a))
          (x ∘ Fin.succAbove 1)) u))
      = resAt M (inf_le_left : (cechN U 0).obj i ⊓ (cechN U 0).obj j ≤ (cechN U 0).obj i)
        ((Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a)) i) u) := by
    have h := congrArg (fun ψ => (ConcreteCategory.hom ψ)
      ((ConcreteCategory.hom (Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a))
        (x ∘ Fin.succAbove 1))) u)) hΦ1
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    have h2 : (ConcreteCategory.hom (trIso M (congrArg (fun t => (cechN U 0).obj t) e1)).hom)
        ((ConcreteCategory.hom (Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a))
          (x ∘ Fin.succAbove 1))) u)
        = (ConcreteCategory.hom (Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a))
          i)) u := trIso_π_apply M (fun t => (cechN U 0).obj t) e1 u
    exact h.trans (congrArg (fun z => (ConcreteCategory.hom
      (resAt M (inf_le_left : (cechN U 0).obj i ⊓ (cechN U 0).obj j ≤ (cechN U 0).obj i))) z) h2)
  have h2 := congrArg (fun z => (trIso M ep).hom z) hraw
  rw [key0, key1] at h2
  exact h2.symm


/-- The family of opens `(cechN U 0).obj i` still covers `⊤`. -/
lemma indexCover (U : ι → X.Opens) (hcov : iSup U = ⊤) :
    iSup (fun i : (cechN U 0).I => (cechN U 0).obj i) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hcov]
  refine iSup_le fun k => ?_
  have h : (cechN U 0).obj (fun _ : Fin 1 => k) = U k := by
    rw [cechN_obj, piFin1']
    rfl
  exact (le_of_eq h.symm).trans (le_iSup (fun i : (cechN U 0).I => (cechN U 0).obj i) (fun _ : Fin 1 => k))

/-- Gluing of a compatible family of sections (Mathlib's gluing axiom). -/
theorem exists_glue_compatible (M : SheafOfModules X.ringCatSheaf) {ι' : Type u}
    (V : ι' → X.Opens) (hcov : iSup V = ⊤) (s : ∀ i, sectionsAt M (V i))
    (hcompat : ∀ i j, resAt M (inf_le_left : V i ⊓ V j ≤ V i) (s i) =
      resAt M (inf_le_right : V i ⊓ V j ≤ V j) (s j)) :
    ∃ x : sectionsAt M ⊤, ∀ i, resAt M (le_top : V i ≤ ⊤) x = s i := by
  obtain ⟨x, hx, -⟩ := TopCat.Sheaf.existsUnique_gluing' (C := AddCommGrpCat.{u})
    (X := TopCat.of X) ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) V ⊤
    (fun i => homOfLE le_top) (le_of_eq hcov.symm) s hcompat
  exact ⟨x, hx⟩

/-- **Descent.** A `0`-cochain of the Čech complex whose differential vanishes is the
restriction of a global section. -/
theorem descent (U : ι → X.Opens) (M : SheafOfModules X.ringCatSheaf) (hcov : iSup U = ⊤)
    (u : ↥((cechComplex U M).X 0)) (hu : ((cechComplex U M).d 0 1) u = 0) :
    ∃ x : sectionsAt M ⊤, ∀ i : (cechN U 0).I,
      resAt M (le_top : (cechN U 0).obj i ≤ ⊤) x =
        (Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a)) i) u :=
  exists_glue_compatible M (fun i : (cechN U 0).I => (cechN U 0).obj i) (indexCover U hcov)
    (fun i => (Pi.π (fun a : (cechN U 0).I => sectionsAt M ((cechN U 0).obj a)) i) u)
    (fun i j => compat_of_d01 U M u hu i j)


lemma resAt_comp_apply (M : SheafOfModules X.ringCatSheaf) {V W Z : X.Opens} (h : W ≤ V)
    (h' : Z ≤ W) (x : ↥(sectionsAt M V)) :
    (resAt M h') ((resAt M h) x) = (resAt M (h'.trans h)) x := by
  rw [← ConcreteCategory.comp_apply, resAt_comp]

lemma sectionsMap_resAt {M N : SheafOfModules X.ringCatSheaf} (f : M ⟶ N) {V W : X.Opens}
    (h : W ≤ V) (x : ↥(sectionsAt M V)) :
    (sectionsMap f W) ((resAt M h) x) = (resAt N h) ((sectionsMap f V) x) := by
  have hnat := (((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom.naturality (homOfLE h).op)
  simp only [sectionsMap, resAt]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hnat]

lemma trIso_symm_hom_hom (M : SheafOfModules X.ringCatSheaf) {V W : X.Opens} (e : V = W)
    (x : ↥(sectionsAt M V)) : (trIso M e.symm).hom ((trIso M e).hom x) = x := by
  rw [trIso_hom_eq_resAt M e, trIso_hom_eq_resAt M e.symm]
  exact resAt_apply_eq M (le_of_eq e.symm) (le_of_eq e) x

lemma sectionsMap_trIso_hom {M N : SheafOfModules X.ringCatSheaf} (f : M ⟶ N) {V W : X.Opens}
    (e : V = W) (x : ↥(sectionsAt M V)) :
    (sectionsMap f W) ((trIso M e).hom x) = (trIso N e).hom ((sectionsMap f V) x) := by
  rw [trIso_hom_eq_resAt M e, trIso_hom_eq_resAt N e]
  exact sectionsMap_resAt f (le_of_eq e.symm) x


lemma map_op_eq_resAt (M : SheafOfModules X.ringCatSheaf) {V W : X.Opens} (φ : W ⟶ V) :
    (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map φ.op) = resAt M (leOfHom φ) := by
  dsimp only [resAt]
  congr 1

lemma eq_zero_of_π_eq_zero {I : Type u} (G : I → AddCommGrpCat.{u}) (u : ↥(∏ᶜ G))
    (h : ∀ i, (Pi.π G i) u = 0) : u = 0 := by
  refine Concrete.isLimit_ext (Discrete.functor G) (Limits.productIsProduct G) u 0 ?_
  rintro ⟨i⟩
  show (ConcreteCategory.hom (Fan.proj (Fan.mk (∏ᶜ G) (Pi.π G)) i)) u =
    (ConcreteCategory.hom (Fan.proj (Fan.mk (∏ᶜ G) (Pi.π G)) i)) 0
  rw [fan_mk_proj]
  simpa using h i

lemma eq_of_π_eq {I : Type u} (G : I → AddCommGrpCat.{u}) (u v : ↥(∏ᶜ G))
    (h : ∀ i, (Pi.π G i) u = (Pi.π G i) v) : u = v := by
  refine Concrete.isLimit_ext (Discrete.functor G) (Limits.productIsProduct G) u v ?_
  rintro ⟨i⟩
  show (ConcreteCategory.hom (Fan.proj (Fan.mk (∏ᶜ G) (Pi.π G)) i)) u =
    (ConcreteCategory.hom (Fan.proj (Fan.mk (∏ᶜ G) (Pi.π G)) i)) v
  rw [fan_mk_proj]
  exact h i

lemma map_f_apply_π (U : ι → X.Opens) {P Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (n : ℕ)
    (x : (cechN U n).I) (u : ↥(((cechComplexFunctor U).obj P).X n)) :
    (Pi.π (fun i : (cechN U n).I => Q.obj (op ((cechN U n).obj i))) x)
        ((((cechComplexFunctor U).map φ).f n) u)
      = (φ.app (op ((cechN U n).obj x)))
          ((Pi.π (fun i : (cechN U n).I => P.obj (op ((cechN U n).obj i))) x) u) := by
  have h := congrArg (fun ψ => (ConcreteCategory.hom ψ) u)
    (Work.DSF1.Cech.cechComplexFunctor_map_pi (U := U) φ n x)
  rw [ConcreteCategory.comp_apply] at h
  exact h

lemma map_f_injective (U : ι → X.Opens) {P Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q)
    (hφ : ∀ V : (X.Opens)ᵒᵖ, Function.Injective (φ.app V)) (n : ℕ) :
    Function.Injective (((cechComplexFunctor U).map φ).f n) := by
  intro u v huv
  apply eq_of_π_eq
  intro x
  refine hφ (op ((cechN U n).obj x)) ?_
  rw [← map_f_apply_π (U := U) φ n x u, huv, map_f_apply_π (U := U) φ n x v]

lemma injective_sectionsMap_of_shortExact (S : ShortComplex (SheafOfModules X.ringCatSheaf))
    (hS : S.ShortExact) (V : X.Opens) : Function.Injective (sectionsMap S.f V) := by
  have h := (CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (SheafOfModules.toSheaf X.ringCatSheaf)).mp inferInstance S hS
  have hm : Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map S.f) := h.2
  have hm1 : Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map S.f).hom :=
    (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mp hm
  have hm2 : Mono (((SheafOfModules.toSheaf X.ringCatSheaf).map S.f).hom.app (op V)) :=
    (NatTrans.mono_iff_mono_app ((SheafOfModules.toSheaf X.ringCatSheaf).map S.f).hom).mp hm1 (op V)
  exact (AddCommGrpCat.mono_iff_injective _).mp hm2


lemma sectionsMap_map {M N : SheafOfModules X.ringCatSheaf} (f : M ⟶ N) {V W : X.Opens}
    (φ : W ⟶ V) (z : ↥(sectionsAt M V)) :
    (sectionsMap f W) ((((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.map φ.op) z)
      = (((SheafOfModules.toSheaf X.ringCatSheaf).obj N).obj.map φ.op) ((sectionsMap f V) z) := by
  have hnat := (((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom.naturality φ.op)
  simp only [sectionsMap]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hnat]

lemma sectionsMap_comp' {M N P : SheafOfModules X.ringCatSheaf} (f : M ⟶ N) (g : N ⟶ P)
    (V : X.Opens) (z : ↥(sectionsAt M V)) :
    (sectionsMap g V) ((sectionsMap f V) z) = (sectionsMap (f ≫ g) V) z := by
  simp only [sectionsMap]
  rw [Functor.map_comp]
  rfl

lemma sectionsMap_gf_zero {M N P : SheafOfModules X.ringCatSheaf} (f : M ⟶ N) (g : N ⟶ P)
    (h : f ≫ g = 0) (V : X.Opens) (z : ↥(sectionsAt M V)) :
    (sectionsMap g V) ((sectionsMap f V) z) = 0 := by
  rw [sectionsMap_comp', h]
  rfl


lemma resAt_leOfHom_leTop (M : SheafOfModules X.ringCatSheaf) {A B : X.Opens} (φ : A ⟶ B)
    (z : ↥(sectionsAt M ⊤)) :
    (resAt M (leOfHom φ)) ((resAt M (le_top : B ≤ ⊤)) z) = (resAt M (le_top : A ≤ ⊤)) z := by
  rw [resAt_comp_apply (M := M) (h := (le_top : B ≤ ⊤)) (h' := leOfHom φ)]

end Work.DSF1.Sheaf






