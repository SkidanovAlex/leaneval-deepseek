import Mathlib
import Submission.Work.DSG4a.cechZBaseChangeDefs

/-! DSG4a: the termwise Čech base-change comparison is an isomorphism on affine opens. -/

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped ChangeOfRings TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

/-- The `A'`-module structure on the base-changed section ring `Γ(X', U')`
(`bcrTerm`, the target of `sectionBaseChangeA'`) is right multiplication by `phiU a'`. -/
lemma bcrTerm_smul_aux (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (V : X.Opens) (a' : A')
    (z : Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f V)) :
    letI : Algebra A' Γ(baseChangeScheme (A := A) (A' := A') X f,
        baseChangeOpen (A := A) (A' := A') X f V) :=
      (DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
        (baseChangeSnd (A := A) (A' := A') X f)
        (baseChangeOpen (A := A) (A' := A') X f V)).toAlgebra
    a' • z = z * DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
      (baseChangeSnd (A := A) (A' := A') X f)
      (baseChangeOpen (A := A) (A' := A') X f V) a' := by
  letI : Algebra A' Γ(baseChangeScheme (A := A) (A' := A') X f,
      baseChangeOpen (A := A) (A' := A') X f V) :=
    (DSMap.phiU A' (baseChangeScheme (A := A) (A' := A') X f)
      (baseChangeSnd (A := A) (A' := A') X f)
      (baseChangeOpen (A := A) (A' := A') X f V)).toAlgebra
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  exact mul_comm _ _

/-- **The base change comparison of a single Čech term, on a pure tensor:** the `A'`-linear map
`sectionBaseChangeA'` sends `a' ⊗ g` to the image of `g ⊗ a'` under the ring map
`sectionBaseChange`. -/
lemma sectionBaseChangeA'_tmul_apply_aux (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (V : X.Opens)
    (a' : A') (g : Γ(X, V)) :
    (sectionBaseChangeA' (A := A) (A' := A') X f V)
        (a' ⊗ₜ[A, algebraMap A A'] g) =
      (letI : Algebra A Γ(X, V) := (DSMap.phiU A X f V).toAlgebra
       sectionBaseChange (A := A) (A' := A') X f V (g ⊗ₜ[A] a')) := by
  letI : Algebra A Γ(X, V) := (DSMap.phiU A X f V).toAlgebra
  have h1 : (a' ⊗ₜ[A, algebraMap A A'] g) = a' • ((1 : A') ⊗ₜ[A, algebraMap A A'] g) := by
    have h := ModuleCat.ExtendScalars.smul_tmul (f := algebraMap A A')
      (M := (DSMap.cechPresheaf A X f).obj (Opposite.op V)) a' (1 : A') g
    rw [mul_one] at h
    exact h.symm
  rw [h1, map_smul, sectionBaseChangeA'_tmul]
  rw [show (g ⊗ₜ[A] a' : TensorProduct A Γ(X, V) A') =
      (TensorProduct.mk A Γ(X, V) A') g a' from rfl]
  rw [sectionBaseChange_tmul X f V g (1 : A'), sectionBaseChange_tmul X f V g a']
  simp only [map_one, mul_one]
  exact bcrTerm_smul_aux (A := A) (A' := A') X f V a'
    (((baseChangeFst (A := A) (A' := A') X f).app V).hom g)

/-- The identification of the two orderings of the tensor product
`A' ⊗[A] Γ(X,V)` and `Γ(X,V) ⊗[A] A'`: the instance change on both factors
(`TensorProduct.congr` of the two identity equivalences) followed by the swap
`TensorProduct.comm`. -/
noncomputable def flipEquiv_aux (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (V : X.Opens) :
    letI : Algebra A Γ(X, V) := (DSMap.phiU A X f V).toAlgebra
    (↑((ModuleCat.restrictScalars (algebraMap A A')).obj (ModuleCat.of A' A')) ⊗[A]
      ↑((DSMap.cechPresheaf A X f).obj (Opposite.op V))) ≃ₗ[A] TensorProduct A Γ(X, V) A' := by
  letI : Algebra A Γ(X, V) := (DSMap.phiU A X f V).toAlgebra
  let eN : (↑((ModuleCat.restrictScalars (algebraMap A A')).obj (ModuleCat.of A' A'))) ≃ₗ[A] A' :=
    { toFun := fun x => (x : A')
      invFun := fun y => y
      map_add' := fun x y => rfl
      map_smul' := fun r x => by simp [Algebra.smul_def, ModuleCat.restrictScalars.smul_def]
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  let eM : (↑((DSMap.cechPresheaf A X f).obj (Opposite.op V))) ≃ₗ[A] Γ(X, V) :=
    { toFun := fun x => (x : Γ(X, V))
      invFun := fun y => y
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  exact (TensorProduct.congr eN eM).trans (TensorProduct.comm A A' Γ(X, V))

/-- The computation rule of `flipEquiv_aux` on a pure tensor. -/
lemma flipEquiv_tmul_aux (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (V : X.Opens)
    (n : ↑((ModuleCat.restrictScalars (algebraMap A A')).obj (ModuleCat.of A' A')))
    (m : ↑((DSMap.cechPresheaf A X f).obj (Opposite.op V))) :
    letI : Algebra A Γ(X, V) := (DSMap.phiU A X f V).toAlgebra
    flipEquiv_aux (A := A) (A' := A') X f V (n ⊗ₜ[A] m) =
      ((m : Γ(X, V)) ⊗ₜ[A] (n : A') : TensorProduct A Γ(X, V) A') := by
  letI : Algebra A Γ(X, V) := (DSMap.phiU A X f V).toAlgebra
  dsimp only [flipEquiv_aux]
  simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul]
  exact TensorProduct.comm_tmul A A' Γ(X, V) (n : A') (m : Γ(X, V))

open CategoryTheory AlgebraicGeometry Limits Opposite in
open scoped ChangeOfRings TensorProduct in
theorem sectionBaseChangeAIsIso_aux {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    (V : X.Opens) (hV : AlgebraicGeometry.IsAffineOpen V) :
    IsIso (Work.DSG4a.sectionBaseChangeA' (A := A) (A' := A') X f V) := by
  letI : Algebra A Γ(X, V) := (DSMap.phiU A X f V).toAlgebra
  have hbij : Function.Bijective (sectionBaseChange (A := A) (A' := A') X f V) :=
    sectionBaseChange_bijective (A := A) (A' := A') X f V hV
  have hid : ∀ x : ↑(bcTerm (A := A) (A' := A') X f V),
      (sectionBaseChangeA' (A := A) (A' := A') X f V) x =
        sectionBaseChange (A := A) (A' := A') X f V
          (flipEquiv_aux (A := A) (A' := A') X f V x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul n m =>
        rw [flipEquiv_tmul_aux (A := A) (A' := A') X f V n m]
        exact sectionBaseChangeA'_tmul_apply_aux (A := A) (A' := A') X f V (n : A') (m : Γ(X, V))
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · have h2 : sectionBaseChange (A := A) (A' := A') X f V
          (flipEquiv_aux (A := A) (A' := A') X f V x) =
        sectionBaseChange (A := A) (A' := A') X f V
          (flipEquiv_aux (A := A) (A' := A') X f V y) := by
      rw [← hid x, h, hid y]
    exact (flipEquiv_aux (A := A) (A' := A') X f V).injective (hbij.1 h2)
  · obtain ⟨z, hz⟩ := hbij.2 y
    exact ⟨(flipEquiv_aux (A := A) (A' := A') X f V).symm z, by
      rw [hid, LinearEquiv.apply_symm_apply, hz]⟩


/-- The `Pi.lift` of a componentwise iso family is an isomorphism.  (This is `Pi.map` of the
family, which is how `bcMapT` is built out of the individual open comparisons.) -/
lemma isIso_piLift_aux {C : Type*} [Category* C] {β : Type*} {F G : β → C}
    [HasProduct F] [HasProduct G] (q : ∀ b, F b ⟶ G b) [∀ b, IsIso (q b)] :
    IsIso (CategoryTheory.Limits.Pi.lift (fun b => CategoryTheory.Limits.Pi.π F b ≫ q b)) := by
  have hq : ∀ b, q b ≫ (asIso (q b)).inv = 𝟙 (F b) := fun b => IsIso.hom_inv_id (q b)
  have hq' : ∀ b, (asIso (q b)).inv ≫ q b = 𝟙 (G b) := fun b => IsIso.inv_hom_id (q b)
  let e : (∏ᶜ F) ≅ (∏ᶜ G) :=
    { hom := CategoryTheory.Limits.Pi.lift (fun b => CategoryTheory.Limits.Pi.π F b ≫ q b)
      inv := CategoryTheory.Limits.Pi.lift
        (fun b => CategoryTheory.Limits.Pi.π G b ≫ (asIso (q b)).inv)
      hom_inv_id := by
        ext b
        simp [hq]
      inv_hom_id := by
        ext b
        simp [hq'] }
  exact Iso.isIso_hom e

/-- The termwise comparison of a single Čech factor is an isomorphism when the corresponding
open of `X` is affine. -/
lemma isIso_bcCompE_aux {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) (x : Work.DSG4a.bcIdx U n)
    (hV : AlgebraicGeometry.IsAffineOpen (Work.DSF1.Cech.Eobj U n x)) :
    IsIso (Work.DSG4a.bcCompE (A := A) (A' := A') X f U n x) := by
  unfold bcCompE
  haveI := sectionBaseChangeAIsIso_aux (A := A) (A' := A') X f (Work.DSF1.Cech.Eobj U n x) hV
  infer_instance

theorem bcMapT_isIso_aux {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    {ι : Type u} [Finite ι] [Nonempty ι]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (U : ι → X.Opens)
    (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (n : ℕ) :
    IsIso (Work.DSG4a.bcMapT (A := A) (A' := A') X f U n) := by
  rw [bcMapT]
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype (bcIdx U n) := inferInstanceAs (Fintype (Fin (n + 1) → ι))
  letI : DecidableEq ι := Classical.decEq ι
  letI : DecidableEq (bcIdx U n) := inferInstanceAs (DecidableEq (Fin (n + 1) → ι))
  haveI hcomp : ∀ x : bcIdx U n, IsIso (bcCompE (A := A) (A' := A') X f U n x) :=
    fun x => isIso_bcCompE_aux (A := A) (A' := A') X f U n x (isAffineOpen_Eobj X f U hU n x)
  refine IsIso.comp_isIso' (Iso.isIso_hom _) ?_
  exact isIso_piLift_aux (fun x : bcIdx U n => bcCompE (A := A) (A' := A') X f U n x)


end Work.DSG4a
