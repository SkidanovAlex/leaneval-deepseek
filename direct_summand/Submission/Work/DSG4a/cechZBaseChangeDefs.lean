import Mathlib
import Submission.Work.DSG4a.BaseChange
import Submission.Work.DSG4a.BaseChangeComplex
import Submission.Work.DSG4a.CechBaseChange
import Submission.Work.DSG4a.CechCompare
import Submission.Work.DSG4a.SectionBaseChange
import Submission.Work.DSG4a.sectionBaseChange_bijective
import Submission.Work.DSG4a.sectionBaseChange_naturality
import Submission.Work.DSG4a.tensorPi_extendScalars
import Submission.Work.DSG4a.preimageOpen_pi
import Submission.Work.DSG4a.Eobj_baseChangeOpen
import Submission.Work.DSF1.Cech.CechSetup
import Submission.Work.DSF1.Cech.CechComponents
import Submission.Work.DSF1.Cech.eq_zero_of_loc_eq_zero
import Submission.Work.DSF1.Cech.UnitCaseSetup
import Submission.Work.DSM5b.CechIsoDefs
import Submission.Work.DSMap.Map

/-!
DSG4a: definitions and small lemmas for the Čech base-change comparison.
-/

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped ChangeOfRings TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

/-! ## Vocabulary -/

/-- The extension of scalars functor `A' ⊗[A] -`. -/
noncomputable abbrev bcExt : ModuleCat.{u} A ⥤ ModuleCat.{u} A' :=
  ModuleCat.extendScalars (algebraMap A A')

/-- The index type of the `n`-th Čech term of a family of opens (it only depends on the family
of opens through its index type `ι`). -/
noncomputable abbrev bcIdx {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (n : ℕ) : Type u :=
  ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n))).I

/-- The base change of the `ℕ`-indexed Čech complex of `X` along `A ⟶ A'`. -/
noncomputable abbrev bcCN (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} A') ℕ :=
  (Functor.mapHomologicalComplex (bcExt (A := A) (A' := A')) (ComplexShape.up ℕ)).obj
    (DSMap.cech A X f U)

/-- The `ℕ`-indexed Čech complex of the base change `X' ⟶ Spec A'`. -/
noncomputable abbrev bcCT (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} A') ℕ :=
  DSMap.cech A' (baseChangeScheme X f) (baseChangeSnd X f)
    (fun i => baseChangeOpen X f (U i))

/-- The base change of the `ℤ`-indexed Čech complex of `X` along `A ⟶ A'`; this is
`baseChangeComplex (cechZ A X f U)` up to definitional unfolding. -/
noncomputable abbrev bcCZ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} A') ℤ :=
  (Functor.mapHomologicalComplex (bcExt (A := A) (A' := A')) (ComplexShape.up ℤ)).obj
    (DSMap.cechZ A X f U)

/-- The `ℤ`-indexed Čech complex of the base change `X' ⟶ Spec A'`. -/
noncomputable abbrev bcCZT (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} A') ℤ :=
  DSMap.cechZ A' (baseChangeScheme X f) (baseChangeSnd X f)
    (fun i => baseChangeOpen X f (U i))

/-! ## The termwise comparison -/

/-- The comparison `A' ⊗[A] Γ(X,V) ⟶ Γ(X',V')` of a single open, as an `A'`-linear map.  This
is `sectionBaseChangeA'` under a name suited to the constructions below. -/
noncomputable abbrev bcComp (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (V : X.Opens) :
    bcTerm (A := A) (A' := A') X f V ⟶ bcrTerm (A := A) (A' := A') X f V :=
  sectionBaseChangeA' (A := A) (A' := A') X f V

/-- The comparison of a single Čech factor: the open of `X'` attached to a simplex `x` is the
preimage of `Eobj U n x`, so the comparison map needs a transport of the target. -/
noncomputable def bcCompE (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens)
    (n : ℕ) (x : bcIdx U n) :
    (bcExt (A := A) (A' := A')).obj
        ((DSMap.cechPresheaf A X f).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x))) ⟶
      (DSMap.cechPresheaf A' (baseChangeScheme X f) (baseChangeSnd X f)).obj
        (Opposite.op (Work.DSF1.Cech.Eobj (fun i => baseChangeOpen X f (U i)) n x)) :=
  sectionBaseChangeA' (A := A) (A' := A') X f (Work.DSF1.Cech.Eobj U n x) ≫
    eqToHom (congrArg (fun V : (baseChangeScheme X f).Opens =>
        (DSMap.cechPresheaf A' (baseChangeScheme X f) (baseChangeSnd X f)).obj (Opposite.op V))
      (show baseChangeOpen X f (Work.DSF1.Cech.Eobj U n x) =
          Work.DSF1.Cech.Eobj (fun i => baseChangeOpen X f (U i)) n x from
        (Eobj_baseChangeOpen (A := A) (A' := A') X f U n x).symm))

/-- **The termwise comparison in degree `n`**: on each factor `x` of the Čech product, the
extension of scalars of the section comparison `sectionBaseChangeA'`. -/
noncomputable def bcMapT (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (n : ℕ) :
    (bcCN (A := A) (A' := A') X f U).X n ⟶ (bcCT (A := A) (A' := A') X f U).X n := by
  letI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype (bcIdx U n) := inferInstanceAs (Fintype (Fin (n + 1) → ι))
  haveI : DecidableEq ι := Classical.decEq ι
  haveI : DecidableEq (bcIdx U n) := inferInstanceAs (DecidableEq (Fin (n + 1) → ι))
  exact (tensorPi_extendScalars (A := A) (A' := A')
      (M := fun x : bcIdx U n =>
        (DSMap.cechPresheaf A X f).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x)))).choose.hom ≫
    Pi.lift (fun x : bcIdx U n =>
      Pi.π (fun y : bcIdx U n =>
          (bcExt (A := A) (A' := A')).obj
            ((DSMap.cechPresheaf A X f).obj (Opposite.op (Work.DSF1.Cech.Eobj U n y)))) x ≫
        bcCompE (A := A) (A' := A') X f U n x)

/-! ## The componentwise identification of the extension of a complex

The base change of the extension of `cech` (in `ℤ`-degrees, extended by zero) is not
definitionally the extension of the base change, but the two have the same terms; `bcPhiO`
provides the componentwise identification on the level of the individual factors, and `bcChi`
assembles it into an isomorphism of complexes. -/

/-- The componentwise identification `A' ⊗[A] (X K o) ≅ X M o`, where `M` is the base change of
`K`: the identity in the degrees lying in the image of `ℕ ↪ ℤ`, and an isomorphism between the
two zero objects otherwise. -/
noncomputable def bcPhiO (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u}
    (U : ι → X.Opens) (o : Option ℕ) :
    (bcExt (A := A) (A' := A')).obj
        (HomologicalComplex.extend.X (DSMap.cech A X f U) o) ≅
      HomologicalComplex.extend.X (bcCN (A := A) (A' := A') X f U) o :=
  match o with
  | some _ => Iso.refl _
  | none => IsZero.iso ((bcExt (A := A) (A' := A')).map_isZero (isZero_zero _)) (isZero_zero _)

/-- **The componentwise identification of the two extensions of complexes.** -/
noncomputable def bcChi (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens) :
    (Functor.mapHomologicalComplex (bcExt (A := A) (A' := A')) (ComplexShape.up ℤ)).obj
        (DSMap.cechZ A X f U) ≅
      (bcCN (A := A) (A' := A') X f U).extend ComplexShape.embeddingUpNat := by
  let e := ComplexShape.embeddingUpNat
  let M : CochainComplex (ModuleCat.{u} A') ℕ := bcCN (A := A) (A' := A') X f U
  have hA : ∀ (o o' : Option ℕ),
      (bcPhiO (A := A) (A' := A') X f U o).hom ≫ HomologicalComplex.extend.d M o o' =
      (bcExt (A := A) (A' := A')).map
          (HomologicalComplex.extend.d (DSMap.cech A X f U) o o') ≫
        (bcPhiO (A := A) (A' := A') X f U o').hom := by
    intro o o'
    rcases o with _ | n
    · rcases o' with _ | m
      · rw [HomologicalComplex.extend.d_none_eq_zero (DSMap.cech A X f U) none none rfl,
            HomologicalComplex.extend.d_none_eq_zero M none none rfl]
        simp
      · rw [HomologicalComplex.extend.d_none_eq_zero (DSMap.cech A X f U) none (some m) rfl,
            HomologicalComplex.extend.d_none_eq_zero M none (some m) rfl]
        simp
    · rcases o' with _ | m
      · rw [HomologicalComplex.extend.d_none_eq_zero' (DSMap.cech A X f U) (some n) none rfl,
            HomologicalComplex.extend.d_none_eq_zero' M (some n) none rfl]
        simp
      · rw [show HomologicalComplex.extend.d M (some n) (some m) = M.d n m from rfl,
            show HomologicalComplex.extend.d (DSMap.cech A X f U) (some n) (some m) =
              (DSMap.cech A X f U).d n m from rfl]
        show 𝟙 ((bcExt (A := A) (A' := A')).obj ((DSMap.cech A X f U).X n)) ≫
            (bcExt (A := A) (A' := A')).map ((DSMap.cech A X f U).d n m) =
          (bcExt (A := A) (A' := A')).map ((DSMap.cech A X f U).d n m) ≫
            𝟙 ((bcExt (A := A) (A' := A')).obj ((DSMap.cech A X f U).X m))
        rw [Category.id_comp, Category.comp_id]
  exact HomologicalComplex.Hom.isoOfComponents
    (fun i' => bcPhiO (A := A) (A' := A') X f U (e.r i'))
    (fun i' j' _ => hA _ _)

/-- The componentwise identification, composed with the identification of the extension. -/
theorem bcPhiO_hom_comp {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens)
    {n : ℕ} {o : Option ℕ} (h : o = some n) :
    (bcPhiO (A := A) (A' := A') X f U o).hom ≫
        (HomologicalComplex.extend.XIso (bcCN (A := A) (A' := A') X f U) h).hom =
      (bcExt (A := A) (A' := A')).map
        (HomologicalComplex.extend.XIso (DSMap.cech A X f U) h).hom := by
  subst h
  simp only [bcPhiO, HomologicalComplex.extend.XIso, Iso.refl_hom, Category.id_comp,
    eqToIso_refl]
  exact ((bcExt (A := A) (A' := A')).map_id
    (HomologicalComplex.extend.X (DSMap.cech A X f U) (some n))).symm

theorem bcPhiO_hom_comp_extendXIso {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens)
    {n : ℕ} {i' : ℤ} (h : ComplexShape.embeddingUpNat.f n = i') :
    (bcPhiO (A := A) (A' := A') X f U (ComplexShape.embeddingUpNat.r i')).hom ≫
        ((bcCN (A := A) (A' := A') X f U).extendXIso ComplexShape.embeddingUpNat h).hom =
      (bcExt (A := A) (A' := A')).map
        ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat h).hom := by
  rw [show (bcCN (A := A) (A' := A') X f U).extendXIso ComplexShape.embeddingUpNat h =
      HomologicalComplex.extend.XIso (bcCN (A := A) (A' := A') X f U)
        (ComplexShape.Embedding.r_eq_some ComplexShape.embeddingUpNat h) from rfl]
  rw [show (DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat h =
      HomologicalComplex.extend.XIso (DSMap.cech A X f U)
        (ComplexShape.Embedding.r_eq_some ComplexShape.embeddingUpNat h) from rfl]
  exact bcPhiO_hom_comp (A := A) (A' := A') X f U
    (ComplexShape.Embedding.r_eq_some ComplexShape.embeddingUpNat h)

/-- Elements of a product of modules are determined by their components. -/
theorem pi_ext_apply {R : Type u} [CommRing R] {β : Type u} (F : β → ModuleCat.{u} R)
    {u v : ↥(∏ᶜ F)} (h : ∀ x, Pi.π F x u = Pi.π F x v) : u = v := by
  have h1 : (ConcreteCategory.hom (ModuleCat.piIsoPi F).hom) u =
      (ConcreteCategory.hom (ModuleCat.piIsoPi F).hom) v := by
    funext x
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    exact h x
  exact (ConcreteCategory.bijective_of_isIso (ModuleCat.piIsoPi F).hom).1 h1

/-- An `eqToHom` is the obvious cast on elements. -/
theorem eqToHom_apply_eq {R : Type u} [CommRing R] {M N : ModuleCat.{u} R} (h : M = N)
    (y : ↥M) : ConcreteCategory.hom (eqToHom h) y = h ▸ y := by
  cases h; rfl

/-- The `x`-component of `bcMapT n`. -/
theorem bcMapT_π {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (n : ℕ) (x : bcIdx (fun i => baseChangeOpen X f (U i)) n) :
    bcMapT (A := A) (A' := A') X f U n ≫ Pi.π _ x =
      (bcExt (A := A) (A' := A')).map (Pi.π _ x) ≫
        bcCompE (A := A) (A' := A') X f U n x := by
  letI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype (bcIdx U n) := inferInstanceAs (Fintype (Fin (n + 1) → ι))
  haveI : DecidableEq ι := Classical.decEq ι
  haveI : DecidableEq (bcIdx U n) := inferInstanceAs (DecidableEq (Fin (n + 1) → ι))
  dsimp only [bcMapT]
  rw [Category.assoc, Pi.lift_comp_π, ← Category.assoc,
    (tensorPi_extendScalars (A := A) (A' := A')
      (M := fun x : bcIdx U n =>
        (DSMap.cechPresheaf A X f).obj (Opposite.op (DSF1.Cech.Eobj U n x)))).choose_spec x]
  rfl

/-- The component of the coaugmentation, as an equation of morphisms. -/
theorem coaug0_π_mor {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens) (x : bcIdx U 0) :
    DSMap.coaug0 A X f U ≫ Pi.π _ x =
      DSMap.unitTop A X f ≫ (DSMap.cechPresheaf A X f).map (homOfLE le_top).op := by
  rw [show DSMap.coaug0 A X f U = Pi.lift (fun _ => DSMap.unitTop A X f ≫
      (DSMap.cechPresheaf A X f).map (homOfLE le_top).op) from rfl]
  rw [Pi.lift_comp_π]


set_option maxHeartbeats 3200000 in
/-- **The coaugmentation is preserved by the base change comparison.** -/
theorem bcChi_extendMap_coaug {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens)
    (ΦN : bcCN (A := A) (A' := A') X f U ⟶
      bcCT (A := A) (A' := A') X f U)
    (hΦN : ∀ a' : A', (ΦN.f 0) (a' ⊗ₜ[A, algebraMap A A'] (DSMap.coaug0 A X f U 1)) =
      a' • (DSMap.coaug0 A' (baseChangeScheme X f)
        (baseChangeSnd X f)
        (fun i => baseChangeOpen X f (U i)) 1)) :
    ∀ a' : A',
      ((bcChi (A := A) (A' := A') X f U).hom ≫
          HomologicalComplex.extendMap ΦN ComplexShape.embeddingUpNat).f 0
        (a' ⊗ₜ[A, algebraMap A A'] coaugZElem A X f U) =
      a' • coaugZElem A' (baseChangeScheme X f)
        (baseChangeSnd X f)
        (fun i => baseChangeOpen X f (U i)) := by
  intro a'
  have hB : (HomologicalComplex.extendMap ΦN ComplexShape.embeddingUpNat).f
        (ComplexShape.embeddingUpNat.f 0) =
      ((bcCN (A := A) (A' := A') X f U).extendXIso ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f 0 = ComplexShape.embeddingUpNat.f 0)).hom ≫
        ΦN.f 0 ≫
          ((bcCT (A := A) (A' := A') X f U).extendXIso ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f 0 = ComplexShape.embeddingUpNat.f 0)).inv :=
    HomologicalComplex.extendMap_f (φ := ΦN) (e := ComplexShape.embeddingUpNat) (i := 0) rfl
  have hA' : (ConcreteCategory.hom
        ((bcCN (A := A) (A' := A') X f U).extendXIso ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f 0 = ComplexShape.embeddingUpNat.f 0)).hom)
        ((ConcreteCategory.hom
          (bcPhiO (A := A) (A' := A') X f U
            (ComplexShape.embeddingUpNat.r (ComplexShape.embeddingUpNat.f 0))).hom)
          (a' ⊗ₜ[A, algebraMap A A'] coaugZElem A X f U)) =
      (ConcreteCategory.hom
        ((bcExt (A := A) (A' := A')).map
          ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom))
        (a' ⊗ₜ[A, algebraMap A A'] coaugZElem A X f U) := by
    have h := ConcreteCategory.congr_hom
      (bcPhiO_hom_comp_extendXIso (A := A) (A' := A') X f U (n := 0)
        (i' := ComplexShape.embeddingUpNat.f 0) rfl)
      (a' ⊗ₜ[A, algebraMap A A'] coaugZElem A X f U)
    rwa [ConcreteCategory.comp_apply] at h
  have hC : (ConcreteCategory.hom
        ((bcExt (A := A) (A' := A')).map
          ((DSMap.cech A X f U).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom))
        (a' ⊗ₜ[A, algebraMap A A'] coaugZElem A X f U) =
      a' ⊗ₜ[A, algebraMap A A'] (DSMap.coaug0 A X f U 1) := by
    rw [ModuleCat.ExtendScalars.map_tmul]
    congr 1
    exact Iso.inv_hom_id_apply _ _
  show (ConcreteCategory.hom
      ((HomologicalComplex.extendMap ΦN ComplexShape.embeddingUpNat).f
        (ComplexShape.embeddingUpNat.f 0)))
        ((ConcreteCategory.hom
          (bcPhiO (A := A) (A' := A') X f U
            (ComplexShape.embeddingUpNat.r (ComplexShape.embeddingUpNat.f 0))).hom)
          (a' ⊗ₜ[A, algebraMap A A'] coaugZElem A X f U)) =
      a' • coaugZElem A' (baseChangeScheme X f) (baseChangeSnd X f)
        (fun i => baseChangeOpen X f (U i))
  rw [hB]
  simp only [ConcreteCategory.comp_apply]
  rw [hA', hC, hΦN a']
  simp only [LinearMap.map_smul]
  rfl


/-! ## The intersection of affine opens of the Čech nerve is affine -/

/-- Every object of the Čech nerve of a family of affine opens of a scheme with affine diagonal
is affine (it is the intersection of finitely many of them). -/
theorem isAffineOpen_Eobj {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    (x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n))).I) :
    IsAffineOpen (Work.DSF1.Cech.Eobj U n x) := by
  rw [show Work.DSF1.Cech.Eobj U n x = ∏ᶜ (U ∘ x) from rfl,
    Work.DSF1.Cech.piObj_eq_iInf]
  exact IsAffineOpen.iInf (fun a => hU (x a))


end Work.DSG4a
