import Mathlib
import Submission.Work.DSG4a.cechZBaseChangeDefs

/-! DSG4a: the coaugmentation under the Čech base-change comparison. -/

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped ChangeOfRings TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

/-! ## Products in `ModuleCat`, elementwise -/

section PiElem

variable {R : Type u} [CommRing R]

/-- The projection of a `Pi.lift` in `ModuleCat`, evaluated at an element. -/
lemma bcCoaugC_pi_lift_apply {β : Type u} {F : β → ModuleCat.{u} R} [HasProduct F]
    {Y : ModuleCat.{u} R} (g : ∀ i, Y ⟶ F i) (y : Y) (i : β) :
    ConcreteCategory.hom (Pi.π F i) (ConcreteCategory.hom (Pi.lift g) y) =
      ConcreteCategory.hom (g i) y := by
  rw [← ConcreteCategory.comp_apply, Pi.lift_comp_π]

/-- Elements of a product of modules are determined by their components. -/
lemma bcCoaugC_pi_ext_apply {β : Type u} {F : β → ModuleCat.{u} R} [HasProduct F]
    {u v : ↥(∏ᶜ F)} (h : ∀ x, ConcreteCategory.hom (Pi.π F x) u =
      ConcreteCategory.hom (Pi.π F x) v) : u = v := by
  have h1 : ConcreteCategory.hom (ModuleCat.piIsoPi F).hom u =
      ConcreteCategory.hom (ModuleCat.piIsoPi F).hom v := by
    funext x
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    exact h x
  exact (ConcreteCategory.bijective_of_isIso (ModuleCat.piIsoPi F).hom).1 h1

end PiElem

lemma bcCoaugC_cechPresheaf_map_apply (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {V W : X.Opens}
    (i : W ⟶ V) (y : ↥Γ(X, V)) :
    ConcreteCategory.hom ((DSMap.cechPresheaf A X f).map i.op) y =
      (X.presheaf.map i.op).hom y := rfl

/-- The image of the global unit section under the `V`-component of the Čech coaugmentation. -/
noncomputable def bcCoaugC_unitS (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (V : X.Opens) :
    (DSMap.cechPresheaf A X f).obj (op V) :=
  ConcreteCategory.hom (DSMap.unitTop A X f ≫
    (DSMap.cechPresheaf A X f).map (homOfLE (le_top : V ≤ ⊤)).op) (1 : A)

/-- The structure map `A ⟶ Γ(X,V)` sends `1` to `1`. -/
lemma bcCoaugC_phiU_one (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (V : X.Opens) :
    DSMap.phiU A X f V (1 : A) = 1 := by
  rw [DSMap.phiU, RingHom.coe_comp, Function.comp_apply, map_one (DSMap.phi A X f)]
  exact map_one _

/-- The global unit section is the image of `1` under the structure map. -/
lemma bcCoaugC_unitTop_apply (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (a : A) :
    ConcreteCategory.hom (DSMap.unitTop A X f) a = DSMap.phiU A X f ⊤ a := by
  letI : Algebra A ↥Γ(X, ⊤) := (DSMap.phiU A X f ⊤).toAlgebra
  change (Algebra.linearMap A ↥Γ(X, ⊤)) a = DSMap.phiU A X f ⊤ a
  rw [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]

/-- The unit section, written through the map on the presheaf side. -/
lemma bcCoaugC_unitS_eq_mor (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (V : X.Opens) :
    bcCoaugC_unitS X f V = ConcreteCategory.hom ((DSMap.cechPresheaf A X f).map
      (homOfLE (le_top : V ≤ ⊤)).op)
        (ConcreteCategory.hom (DSMap.unitTop A X f) (1 : A)) := by
  unfold bcCoaugC_unitS
  rw [ConcreteCategory.comp_apply]

/-- The unit section, written through the restriction map `Γ(X,⊤) ⟶ Γ(X,V)`. -/
lemma bcCoaugC_unitS_eq_resLE (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (V : X.Opens) :
    bcCoaugC_unitS X f V = ConcreteCategory.hom (resLE (V := V) (U := ⊤) le_top)
      (ConcreteCategory.hom (DSMap.unitTop A X f) (1 : A)) := by
  unfold bcCoaugC_unitS resLE
  rw [ConcreteCategory.comp_apply]
  exact bcCoaugC_cechPresheaf_map_apply (A := A) X f (homOfLE (le_top : V ≤ ⊤))
    (ConcreteCategory.hom (DSMap.unitTop A X f) (1 : A))

/-- The unit section, written through the structure map `A ⟶ Γ(X,⊤)`. -/
lemma bcCoaugC_unitS_eq_phi (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (V : X.Opens) :
    bcCoaugC_unitS X f V = ConcreteCategory.hom (resLE (V := V) (U := ⊤) le_top)
      ((DSMap.phiU A X f ⊤) (1 : A)) := by
  rw [bcCoaugC_unitS_eq_resLE, bcCoaugC_unitTop_apply]

/-- Restricting the unit section is the unit section. -/
lemma bcCoaugC_resLE_unitS (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {V W : X.Opens}
    (h : V ≤ W) :
    ConcreteCategory.hom (resLE h) (bcCoaugC_unitS X f W) = bcCoaugC_unitS X f V := by
  have hkey : resLE (V := W) (U := ⊤) (le_top : W ≤ ⊤) ≫ resLE h =
      resLE (V := V) (U := ⊤) (le_top : V ≤ ⊤) := by
    unfold resLE
    rw [← Functor.map_comp]
    exact congrArg (fun g => X.presheaf.map g) (Subsingleton.elim _ _)
  have h1 : ∀ y : ↥Γ(X, ⊤),
      ConcreteCategory.hom (resLE h)
        (ConcreteCategory.hom (resLE (V := W) (U := ⊤) (le_top : W ≤ ⊤)) y) =
      ConcreteCategory.hom (resLE (V := V) (U := ⊤) (le_top : V ≤ ⊤)) y := by
    intro y
    rw [← ConcreteCategory.comp_apply]
    exact ConcreteCategory.congr_hom hkey y
  rw [bcCoaugC_unitS_eq_resLE (A := A) X f W, bcCoaugC_unitS_eq_resLE (A := A) X f V]
  exact h1 (ConcreteCategory.hom (DSMap.unitTop A X f) (1 : A))

/-! ## The base change of the unit section -/

/-- The top unit section base changes to the top unit section. -/
lemma bcCoaugC_fst_unitTop_top (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) :
    ConcreteCategory.hom ((baseChangeFst (A := A) (A' := A') X f).app ⊤)
        ((DSMap.phiU A X f ⊤) (1 : A)) =
      bcCoaugC_unitS (A := A') (baseChangeScheme X f) (baseChangeSnd X f)
        (baseChangeOpen X f ⊤) := by
  rw [phiU_baseChange (A := A) (A' := A') X f ⊤ (1 : A), map_one (algebraMap A A'),
    bcCoaugC_phiU_one]
  rw [bcCoaugC_unitS_eq_phi, bcCoaugC_phiU_one]
  exact (map_one (ConcreteCategory.hom
    (resLE (V := baseChangeOpen X f ⊤) (U := ⊤) le_top))).symm

/-- The base change comparison sends the unit section to the unit section. -/
lemma bcCoaugC_sectionBaseChange_resLE (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (V : X.Opens) :
    sectionBaseChange (A := A) (A' := A') X f V
      (tmulElem f V (ConcreteCategory.hom (resLE (V := V) (U := ⊤) le_top)
        ((DSMap.phiU A X f ⊤) (1 : A))) (1 : A')) =
      bcCoaugC_unitS (A := A') (baseChangeScheme X f) (baseChangeSnd X f)
        (baseChangeOpen X f V) := by
  have hnat := sectionBaseChange_naturality_fst (A := A) (A' := A') X f (U := ⊤) (V := V)
    le_top ((DSMap.phiU A X f ⊤) (1 : A))
  have hres := bcCoaugC_resLE_unitS (A := A') (X := baseChangeScheme X f)
    (f := baseChangeSnd X f) (V := baseChangeOpen X f V) (W := baseChangeOpen X f ⊤)
    (fun x hx => (le_top : V ≤ ⊤) hx)
  unfold tmulElem
  rw [sectionBaseChange_tmul]
  rw [hnat, bcCoaugC_fst_unitTop_top, hres, bcCoaugC_phiU_one, mul_one]

/-- The base change comparison sends the unit section to the unit section. -/
lemma bcCoaugC_sectionBaseChange_unit (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (V : X.Opens) :
    sectionBaseChange (A := A) (A' := A') X f V
      (tmulElem f V (bcCoaugC_unitS X f V) (1 : A')) =
      bcCoaugC_unitS (A := A') (baseChangeScheme X f) (baseChangeSnd X f)
        (baseChangeOpen X f V) :=
  bcCoaugC_sectionBaseChange_resLE (A := A) (A' := A') X f V

/-! ## The comparison on `1 ⊗ g` -/

/-- The `A'`-linear comparison map sends `a' ⊗ g` to `a'` times the image of `1 ⊗ g`. -/
lemma bcCoaugC_sectionBaseChangeA'_tmul' (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (V : X.Opens) (a' : A') (g : (DSMap.cechPresheaf A X f).obj (op V)) :
    ConcreteCategory.hom (sectionBaseChangeA' (A := A) (A' := A') X f V)
        (a' ⊗ₜ[A, algebraMap A A'] g) =
      a' • ConcreteCategory.hom (sectionBaseChangeA' (A := A) (A' := A') X f V)
        ((1 : A') ⊗ₜ[A, algebraMap A A'] g) := by
  have h1 : a' ⊗ₜ[A, algebraMap A A'] g =
      a' • ((1 : A') ⊗ₜ[A, algebraMap A A'] g) := by
    have h := ModuleCat.ExtendScalars.smul_tmul (f := algebraMap A A') a' (1 : A') g
    rw [mul_one] at h
    exact h.symm
  rw [h1, map_smul]

/-- The `A'`-linear comparison map on `1 ⊗ g` is the comparison map of `SectionBaseChange`. -/
lemma bcCoaugC_sectionBaseChangeA'_tmul_hom (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (V : X.Opens) (g : (DSMap.cechPresheaf A X f).obj (op V)) :
    ConcreteCategory.hom (sectionBaseChangeA' (A := A) (A' := A') X f V)
        ((1 : A') ⊗ₜ[A, algebraMap A A'] g) =
      sectionBaseChange (A := A) (A' := A') X f V (tmulElem f V g (1 : A')) := by
  rw [show ConcreteCategory.hom (sectionBaseChangeA' (A := A) (A' := A') X f V)
      ((1 : A') ⊗ₜ[A, algebraMap A A'] g) =
      sectionBaseChangeA' (A := A) (A' := A') X f V
        ((1 : A') ⊗ₜ[A, algebraMap A A'] g) from rfl]
  rw [sectionBaseChangeA'_tmul]
  rfl

/-- Transporting the unit section along an equality of opens gives the unit section. -/
lemma bcCoaugC_cechPresheaf_eqToHom_unitS (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {V W : (baseChangeScheme X f).Opens} {h : V = W} :
    ConcreteCategory.hom (eqToHom (congrArg (fun U => (DSMap.cechPresheaf A'
        (baseChangeScheme X f) (baseChangeSnd X f)).obj (op U)) h))
      (bcCoaugC_unitS (A := A') (baseChangeScheme X f) (baseChangeSnd X f) V) =
      bcCoaugC_unitS (A := A') (baseChangeScheme X f) (baseChangeSnd X f) W := by
  cases h
  rfl

/-! ## The comparison on the coaugmentation -/

/-- The component of the coaugmentation `coaug0`, as an equation of morphisms. -/
lemma bcCoaugC_coaug0_π_mor (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u}
    (U : ι → X.Opens) (x : bcIdx U 0) :
    DSMap.coaug0 A X f U ≫ Pi.π _ x =
      DSMap.unitTop A X f ≫ (DSMap.cechPresheaf A X f).map (homOfLE le_top).op := by
  rw [show DSMap.coaug0 A X f U = Pi.lift (fun _ => DSMap.unitTop A X f ≫
      (DSMap.cechPresheaf A X f).map (homOfLE le_top).op) from rfl]
  rw [Pi.lift_comp_π]

/-- The component of the coaugmentation `coaug0` on `1` is the unit section. -/
lemma bcCoaugC_coaug0_π_unitS (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u}
    (U : ι → X.Opens) (x : bcIdx U 0) :
    ConcreteCategory.hom (Pi.π (fun y : bcIdx U 0 =>
        (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 y))) x)
      (ConcreteCategory.hom (DSMap.coaug0 A X f U) (1 : A)) =
        bcCoaugC_unitS X f (DSF1.Cech.Eobj U 0 x) := by
  have h2 := congrArg (fun (g : ModuleCat.of A A ⟶
      (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x))) =>
      ConcreteCategory.hom g (1 : A)) (bcCoaugC_coaug0_π_mor (A := A) X f U x)
  simp only [ConcreteCategory.comp_apply] at h2
  rw [bcCoaugC_unitS_eq_mor]
  exact h2

/-- The `x`-component of the comparison `bcMapT n`. -/
lemma bcCoaugC_bcMapT_π (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (n : ℕ) (x : bcIdx U n) :
    bcMapT (A := A) (A' := A') X f U n ≫
      Pi.π (fun y : bcIdx U n =>
        (DSMap.cechPresheaf A' (baseChangeScheme X f) (baseChangeSnd X f)).obj
          (op (DSF1.Cech.Eobj (fun i => baseChangeOpen X f (U i)) n y))) x
    = (bcExt (A := A) (A' := A')).map
        (Pi.π (fun y : bcIdx U n =>
          (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U n y))) x) ≫
      bcCompE (A := A) (A' := A') X f U n x := by
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype (bcIdx U n) := inferInstanceAs (Fintype (Fin (n + 1) → ι))
  haveI : DecidableEq ι := Classical.decEq ι
  haveI : DecidableEq (bcIdx U n) := inferInstanceAs (DecidableEq (Fin (n + 1) → ι))
  rw [show bcMapT (A := A) (A' := A') X f U n =
      (tensorPi_extendScalars (A := A) (A' := A')
        (M := fun x : bcIdx U n =>
          (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U n x)))).choose.hom ≫
      Pi.lift (fun x : bcIdx U n =>
        Pi.π (fun y : bcIdx U n =>
          (bcExt (A := A) (A' := A')).obj
            ((DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U n y)))) x ≫
        bcCompE (A := A) (A' := A') X f U n x) from rfl]
  rw [Category.assoc, Pi.lift_comp_π]
  exact congrArg (fun t => t ≫ bcCompE (A := A) (A' := A') X f U n x)
    ((tensorPi_extendScalars (A := A) (A' := A')
      (M := fun x : bcIdx U n =>
        (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U n x)))).choose_spec x)

/-- The degree-`0` comparison, on `a' ⊗ 1` in a single factor: `a'` times the unit section. -/
lemma bcCoaugC_bcCompE_unitS (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u}
    (U : ι → X.Opens) (x : bcIdx U 0) (a' : A') :
    ConcreteCategory.hom (bcCompE (A := A) (A' := A') X f U 0 x)
        (a' ⊗ₜ[A, algebraMap A A'] bcCoaugC_unitS X f (DSF1.Cech.Eobj U 0 x)) =
      a' • bcCoaugC_unitS (A := A') (baseChangeScheme (A := A) (A' := A') X f)
        (baseChangeSnd (A := A) (A' := A') X f)
        (DSF1.Cech.Eobj (fun i => baseChangeOpen (A := A) (A' := A') X f (U i)) 0 x) := by
  have hbc : bcCompE (A := A) (A' := A') X f U 0 x =
      sectionBaseChangeA' (A := A) (A' := A') X f (DSF1.Cech.Eobj U 0 x) ≫
        eqToHom (congrArg (fun U : (baseChangeScheme (A := A) (A' := A') X f).Opens =>
          (DSMap.cechPresheaf A' (baseChangeScheme (A := A) (A' := A') X f)
            (baseChangeSnd (A := A) (A' := A') X f)).obj (op U))
          (show baseChangeOpen (A := A) (A' := A') X f (DSF1.Cech.Eobj U 0 x) =
            DSF1.Cech.Eobj (fun i => baseChangeOpen (A := A) (A' := A') X f (U i)) 0 x from
              (Eobj_baseChangeOpen (A := A) (A' := A') X f U 0 x).symm)) := rfl
  rw [hbc, bcCoaugC_unitS_eq_phi (A := A) X f (DSF1.Cech.Eobj U 0 x)]
  rw [ConcreteCategory.comp_apply, bcCoaugC_sectionBaseChangeA'_tmul', map_smul,
    bcCoaugC_sectionBaseChangeA'_tmul_hom, bcCoaugC_sectionBaseChange_resLE]
  exact congrArg (fun (y : ↥((DSMap.cechPresheaf A' (baseChangeScheme (A := A) (A' := A') X f)
      (baseChangeSnd (A := A) (A' := A') X f)).obj
      (op (DSF1.Cech.Eobj (fun i => baseChangeOpen (A := A) (A' := A') X f (U i)) 0 x)))) =>
        a' • y)
    (bcCoaugC_cechPresheaf_eqToHom_unitS (X := X) (f := f)
      (h := (show baseChangeOpen (A := A) (A' := A') X f (DSF1.Cech.Eobj U 0 x) =
          DSF1.Cech.Eobj (fun i => baseChangeOpen (A := A) (A' := A') X f (U i)) 0 x from
        (Eobj_baseChangeOpen (A := A) (A' := A') X f U 0 x).symm)))

/-- The extension of scalars of a pure tensor, in the form used below. -/
lemma bcCoaugC_bcExt_map_tmul {M M' : ModuleCat.{u} A} (g : M ⟶ M') (s : A') (m : M) :
    ConcreteCategory.hom ((bcExt (A := A) (A' := A')).map g)
        (s ⊗ₜ[A, algebraMap A A'] m) =
      s ⊗ₜ[A, algebraMap A A'] ConcreteCategory.hom g m := rfl

/-- The extension of scalars of the coaugmentation, followed by the comparison of the
remaining factor. -/
lemma bcCoaugC_ext_map_coaug (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u}
    (U : ι → X.Opens) (x : bcIdx U 0) (a' : A') :
    ConcreteCategory.hom ((bcExt (A := A) (A' := A')).map
        (Pi.π (fun y : bcIdx U 0 =>
          (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 y))) x))
        (a' ⊗ₜ[A, algebraMap A A']
          (ConcreteCategory.hom (DSMap.coaug0 A X f U) (1 : A))) =
      a' ⊗ₜ[A, algebraMap A A'] bcCoaugC_unitS X f (DSF1.Cech.Eobj U 0 x) := by
  have h := bcCoaugC_bcExt_map_tmul (A := A) (A' := A')
    (g := (Pi.π (fun y : bcIdx U 0 =>
      (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 y))) x)) a'
    (ConcreteCategory.hom (DSMap.coaug0 A X f U) (1 : A))
  rw [bcCoaugC_coaug0_π_unitS] at h
  exact h

theorem bcMapT_coaug_aux {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (a' : A') :
    (Work.DSG4a.bcMapT (A := A) (A' := A') X f U 0)
        (a' ⊗ₜ[A, algebraMap A A'] (DSMap.coaug0 A X f U 1)) =
      a' • (DSMap.coaug0 A'
        (Work.DSG4a.baseChangeScheme X f) (Work.DSG4a.baseChangeSnd X f)
        (fun i => Work.DSG4a.baseChangeOpen X f (U i)) 1) := by
  refine bcCoaugC_pi_ext_apply (F := fun y : bcIdx U 0 =>
      (DSMap.cechPresheaf A' (Work.DSG4a.baseChangeScheme X f)
        (Work.DSG4a.baseChangeSnd X f)).obj
        (op (DSF1.Cech.Eobj (fun i => Work.DSG4a.baseChangeOpen X f (U i)) 0 y))) ?_
  intro x
  rw [map_smul]
  have h1 : ConcreteCategory.hom (Pi.π (fun y : bcIdx U 0 =>
        (DSMap.cechPresheaf A' (Work.DSG4a.baseChangeScheme X f)
          (Work.DSG4a.baseChangeSnd X f)).obj
          (op (DSF1.Cech.Eobj (fun i => Work.DSG4a.baseChangeOpen X f (U i)) 0 y))) x)
      (ConcreteCategory.hom (Work.DSG4a.bcMapT (A := A) (A' := A') X f U 0)
        (a' ⊗ₜ[A, algebraMap A A'] (DSMap.coaug0 A X f U 1))) =
      ConcreteCategory.hom (bcCompE (A := A) (A' := A') X f U 0 x)
        (ConcreteCategory.hom ((bcExt (A := A) (A' := A')).map
          (Pi.π (fun y : bcIdx U 0 =>
            (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 y))) x))
          (a' ⊗ₜ[A, algebraMap A A'] (DSMap.coaug0 A X f U 1))) := by
    have hc := congrArg (fun (g : (bcCN (A := A) (A' := A') X f U).X 0 ⟶
        (DSMap.cechPresheaf A' (Work.DSG4a.baseChangeScheme X f)
          (Work.DSG4a.baseChangeSnd X f)).obj
          (op (DSF1.Cech.Eobj (fun i => Work.DSG4a.baseChangeOpen X f (U i)) 0 x))) =>
        ConcreteCategory.hom g (a' ⊗ₜ[A, algebraMap A A'] (DSMap.coaug0 A X f U 1)))
      (bcCoaugC_bcMapT_π (A := A) (A' := A') X f U 0 x)
    simp only [ConcreteCategory.comp_apply] at hc
    exact hc
  have h2 : ConcreteCategory.hom (bcCompE (A := A) (A' := A') X f U 0 x)
        (ConcreteCategory.hom ((bcExt (A := A) (A' := A')).map
          (Pi.π (fun y : bcIdx U 0 =>
            (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 y))) x))
          (a' ⊗ₜ[A, algebraMap A A'] (DSMap.coaug0 A X f U 1))) =
      ConcreteCategory.hom (bcCompE (A := A) (A' := A') X f U 0 x)
        (a' ⊗ₜ[A, algebraMap A A'] bcCoaugC_unitS X f (DSF1.Cech.Eobj U 0 x)) := by
    refine congrArg (fun (y : ↥((bcExt (A := A) (A' := A')).obj
      ((DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x))))) =>
        ConcreteCategory.hom (bcCompE (A := A) (A' := A') X f U 0 x) y) ?_
    exact bcCoaugC_ext_map_coaug (A := A) (A' := A') X f U x a'
  have h3 := bcCoaugC_bcCompE_unitS (A := A) (A' := A') X f U x a'
  have h4 : ConcreteCategory.hom (Pi.π (fun y : bcIdx U 0 =>
        (DSMap.cechPresheaf A' (Work.DSG4a.baseChangeScheme X f)
          (Work.DSG4a.baseChangeSnd X f)).obj
          (op (DSF1.Cech.Eobj (fun i => Work.DSG4a.baseChangeOpen X f (U i)) 0 y))) x)
      (ConcreteCategory.hom (DSMap.coaug0 A' (Work.DSG4a.baseChangeScheme X f)
        (Work.DSG4a.baseChangeSnd X f) (fun i => Work.DSG4a.baseChangeOpen X f (U i)))
        (1 : A')) =
      bcCoaugC_unitS (A := A') (Work.DSG4a.baseChangeScheme X f)
        (Work.DSG4a.baseChangeSnd X f)
        (DSF1.Cech.Eobj (fun i => Work.DSG4a.baseChangeOpen X f (U i)) 0 x) :=
    bcCoaugC_coaug0_π_unitS (A := A') (Work.DSG4a.baseChangeScheme X f)
      (Work.DSG4a.baseChangeSnd X f) (fun i => Work.DSG4a.baseChangeOpen X f (U i)) x
  rw [h1.trans (h2.trans h3), h4]



end Work.DSG4a
