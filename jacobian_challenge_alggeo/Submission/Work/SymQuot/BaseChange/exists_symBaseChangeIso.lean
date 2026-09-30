import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.RelQuot.relQuot
import Submission.Work.SymQuot.Invariants.tensor_fixedPoints_of_flat
import Submission.Work.SymQuot.SymData
import Submission.Work.CurveBasics.BaseChangeScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option allowUnsafeReducibility true

attribute [local reducible] CategoryTheory.Over.pullback
attribute [local reducible] CategoryTheory.Over.map
attribute [local reducible] Work.SymQuot.Sym
attribute [local reducible] Work.SymQuot.Sym.quot

open CategoryTheory Limits AlgebraicGeometry
open scoped MonoidalCategory

universe u

namespace Work.SymQuot.BaseChange

variable {K : Type u} [Field K] {L : Type u} [Field L]
variable (f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))

/-! ### Base change of finite products

`Over.pullback f` is a right adjoint, hence preserves products: the base change of the `n`-fold
product `Xⁿ` is the `n`-fold product of the base change of `X`.  We record the comparison
isomorphism and its interaction with the permutation action on the factors. -/

/-- The comparison isomorphism `(Xⁿ)_L ≅ (X_L)ⁿ`. -/
noncomputable def pbPiIso (X : Work.GCBasics.Sch K) (n : ℕ) :
    (Over.pullback f).obj (Work.SymQuot.prod X n) ≅
      Work.SymQuot.prod ((Over.pullback f).obj X) n := by
  haveI : PreservesLimitsOfSize (Over.pullback f) :=
    (Over.mapPullbackAdj f).rightAdjoint_preservesLimits
  exact PreservesProduct.iso (Over.pullback f) (fun _ : Fin n => X)

theorem pbPiIso_hom_apply (X : Work.GCBasics.Sch K) (n : ℕ) :
    (pbPiIso f X n).hom = Pi.lift (fun m => (Over.pullback f).map (Work.SymQuot.proj X n m)) := by
  rw [pbPiIso, PreservesProduct.iso_hom]
  rfl

theorem pbPiIso_hom_proj (X : Work.GCBasics.Sch K) (n : ℕ) (m : Fin n) :
    (pbPiIso f X n).hom ≫ Work.SymQuot.proj ((Over.pullback f).obj X) n m =
      (Over.pullback f).map (Work.SymQuot.proj X n m) := by
  rw [pbPiIso_hom_apply]
  exact Pi.lift_comp_π _ m

/-- **The comparison isomorphism is compatible with the permutation of the factors.** -/
theorem pbPiIso_perm (X : Work.GCBasics.Sch K) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Over.pullback f).map ((Work.SymQuot.permIso X σ).hom) ≫ (pbPiIso f X n).hom =
      (pbPiIso f X n).hom ≫ (Work.SymQuot.permIso ((Over.pullback f).obj X) σ).hom := by
  apply Pi.hom_ext
  intro m
  calc
    ((Over.pullback f).map ((Work.SymQuot.permIso X σ).hom) ≫ (pbPiIso f X n).hom) ≫
        Pi.π (fun _ : Fin n => (Over.pullback f).obj X) m
        = (Over.pullback f).map ((Work.SymQuot.permIso X σ).hom) ≫
            ((pbPiIso f X n).hom ≫ Pi.π (fun _ : Fin n => (Over.pullback f).obj X) m) :=
          Category.assoc _ _ _
    _ = (Over.pullback f).map ((Work.SymQuot.permIso X σ).hom) ≫
            (Over.pullback f).map (Pi.π (fun _ : Fin n => X) m) := by
          rw [show (pbPiIso f X n).hom ≫ Pi.π (fun _ : Fin n => (Over.pullback f).obj X) m =
              (pbPiIso f X n).hom ≫ Work.SymQuot.proj ((Over.pullback f).obj X) n m from rfl,
            pbPiIso_hom_proj]
    _ = (Over.pullback f).map ((Work.SymQuot.permIso X σ).hom ≫ Pi.π (fun _ : Fin n => X) m) :=
          (Functor.map_comp (Over.pullback f) (Work.SymQuot.permIso X σ).hom
            (Pi.π (fun _ : Fin n => X) m)).symm
    _ = (Over.pullback f).map (Pi.π (fun _ : Fin n => X) (σ.symm m)) :=
          congrArg _ (Work.SymQuot.Product.permIso_hom_proj X σ m)
    _ = (pbPiIso f X n).hom ≫ Pi.π (fun _ : Fin n => (Over.pullback f).obj X) (σ.symm m) :=
          (show (pbPiIso f X n).hom ≫ Work.SymQuot.proj ((Over.pullback f).obj X) n (σ.symm m) =
              (Over.pullback f).map (Work.SymQuot.proj X n (σ.symm m)) from
            pbPiIso_hom_proj f X n (σ.symm m)).symm
    _ = (pbPiIso f X n).hom ≫
            ((Work.SymQuot.permIso ((Over.pullback f).obj X) σ).hom ≫
              Pi.π (fun _ : Fin n => (Over.pullback f).obj X) m) := by
          rw [Work.SymQuot.Product.permIso_hom_proj]
    _ = ((pbPiIso f X n).hom ≫ (Work.SymQuot.permIso ((Over.pullback f).obj X) σ).hom) ≫
            Pi.π (fun _ : Fin n => (Over.pullback f).obj X) m := (Category.assoc _ _ _).symm

variable (Y : Work.GCBasics.Sch K)

/-- The canonical identification of the base change of `X` (an object over `Spec L`) with the
fibre product `X ⊗ Y` (an object over `Spec K`): both have the same underlying scheme. -/
noncomputable def mapPullbackTensorIso (X : Work.GCBasics.Sch K) :
    (Over.map Y.hom).obj ((Over.pullback Y.hom).obj X) ≅ X ⊗ Y :=
  Over.isoMk (Iso.refl _) (by
    show (𝟙 _) ≫ (X ⊗ Y).hom = ((Over.map Y.hom).obj ((Over.pullback Y.hom).obj X)).hom
    simp only [Category.id_comp, Over.tensorObj_hom, Over.map_obj_hom, Over.pullback_obj_hom]
    exact pullback.condition)

@[simp]
theorem mapPullbackTensorIso_hom_left (X : Work.GCBasics.Sch K) :
    ((mapPullbackTensorIso Y X).hom).left = 𝟙 _ := rfl

@[simp]
theorem mapPullbackTensorIso_inv_left (X : Work.GCBasics.Sch K) :
    ((mapPullbackTensorIso Y X).inv).left =
      𝟙 ((Over.map Y.hom).obj ((Over.pullback Y.hom).obj X)).left := by
  have h := congrArg Over.Hom.left (mapPullbackTensorIso Y X).inv_hom_id
  simp only [Over.comp_left, mapPullbackTensorIso_hom_left, Over.id_left] at h
  simpa using h

/-- **Base change as a functor and as tensoring with `Y` agree on underlying morphisms.** -/
theorem pullback_map_left_eq_whiskerRight (X X' : Work.GCBasics.Sch K) (u : X ⟶ X') :
    ((Over.pullback Y.hom).map u).left = (u ▷ Y).left := by
  simp only [Over.pullback_map_left, Over.whiskerRight_left, Over.homMk_left]
  apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, Category.comp_id]

end Work.SymQuot.BaseChange

namespace Work.SymQuot.BaseChange

section Construction

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
variable (C : Work.CurveBasics.Curve K) [Work.SymQuot.CurveAffineCover C] (n : ℕ)

/-- The invariance of the structure morphism of `Cⁿ`, phrased with the action of the quotient
datum `symData C n` (which is `symAction C n` definitionally). -/
theorem symData_hbase :
    ∀ g : ULift.{u} (Equiv.Perm (Fin n)),
      (Work.SymQuot.symData C n).action.hom g ≫ (Work.SymQuot.prod C.toOver n).hom =
        (Work.SymQuot.prod C.toOver n).hom :=
  Work.SymQuot.sym_hom_invariant C n

/-- **The comparison `(Cⁿ)_L ≅ (C_L)ⁿ`**, in the raw form given by limit preservation. -/
noncomputable def symPiIsoRaw : (Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj
      (Work.SymQuot.prod C.toOver n) ≅
    Work.SymQuot.prod ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj C.toOver) n :=
  pbPiIso (Work.CurveBasics.Curve.specMap K L) C.toOver n

/-- **The comparison `(Cⁿ)_L ≅ (C_L)ⁿ`**, in the form in which it is consumed downstream. -/
noncomputable def symPiIso : (Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj
      (Work.SymQuot.prod C.toOver n) ≅
    Work.SymQuot.prod (C.baseChange L).toOver n :=
  pbPiIso (Work.CurveBasics.Curve.specMap K L) C.toOver n

theorem symPiIsoRaw_perm (σ : Equiv.Perm (Fin n)) :
    (Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
        ((Work.SymQuot.permIso C.toOver σ).hom) ≫ (symPiIsoRaw K L C n).hom =
      (symPiIsoRaw K L C n).hom ≫
        (Work.SymQuot.permIso
          ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj C.toOver) σ).hom :=
  pbPiIso_perm (Work.CurveBasics.Curve.specMap K L) C.toOver σ

theorem symPiIso_perm (σ : Equiv.Perm (Fin n)) :
    (Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
        ((Work.SymQuot.permIso C.toOver σ).hom) ≫ (symPiIso K L C n).hom =
      (symPiIso K L C n).hom ≫
        (Work.SymQuot.permIso (C.baseChange L).toOver σ).hom :=
  pbPiIso_perm (Work.CurveBasics.Curve.specMap K L) C.toOver σ

theorem symPiIsoRaw_perm_rev (σ : Equiv.Perm (Fin n)) :
    (Work.SymQuot.permIso
        ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj C.toOver) σ).hom ≫
      (symPiIsoRaw K L C n).inv =
    (symPiIsoRaw K L C n).inv ≫
      (Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
        ((Work.SymQuot.permIso C.toOver σ).hom) := by
  have h := symPiIsoRaw_perm K L C n σ
  have h2 : (symPiIsoRaw K L C n).inv ≫
        (Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
          ((Work.SymQuot.permIso C.toOver σ).hom) =
      (Work.SymQuot.permIso
          ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj C.toOver) σ).hom ≫
        (symPiIsoRaw K L C n).inv := by
    calc (symPiIsoRaw K L C n).inv ≫
          (Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
            ((Work.SymQuot.permIso C.toOver σ).hom)
        = (symPiIsoRaw K L C n).inv ≫
            (Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
              ((Work.SymQuot.permIso C.toOver σ).hom) ≫
            (symPiIsoRaw K L C n).hom ≫ (symPiIsoRaw K L C n).inv := by
          rw [Iso.hom_inv_id, Category.comp_id]
      _ = (symPiIsoRaw K L C n).inv ≫
            (((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
              ((Work.SymQuot.permIso C.toOver σ).hom)) ≫ (symPiIsoRaw K L C n).hom) ≫
            (symPiIsoRaw K L C n).inv := by rw [Category.assoc]
      _ = (symPiIsoRaw K L C n).inv ≫
            ((symPiIsoRaw K L C n).hom ≫
              (Work.SymQuot.permIso
                ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj C.toOver) σ).hom) ≫
            (symPiIsoRaw K L C n).inv := by rw [h]
      _ = (Work.SymQuot.permIso
            ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj C.toOver) σ).hom ≫
            (symPiIsoRaw K L C n).inv := by
          rw [← Category.assoc, Iso.inv_hom_id_assoc]
  exact h2.symm

/-- The inverse comparison is compatible with the permutation action on the factors. -/
theorem symPiIso_inv_perm (σ : Equiv.Perm (Fin n)) :
    (Work.SymQuot.permIso (C.baseChange L).toOver σ).hom ≫ (symPiIso K L C n).inv =
      (symPiIso K L C n).inv ≫ (Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
        ((Work.SymQuot.permIso C.toOver σ).hom) :=
  symPiIsoRaw_perm_rev K L C n σ

/-- The quotient map of `Cⁿ`, after base change to `Spec L`. -/
noncomputable def symqL : (Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj
      (Work.SymQuot.prod C.toOver n) ⟶
    (Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj (Work.SymQuot.Sym C n) :=
  (Over.pullback (Work.CurveBasics.Curve.specMap K L)).map (Work.SymQuot.Sym.quot C n)

/-- The base changed quotient map, as a morphism out of `(C_L)ⁿ`. -/
noncomputable def symfL : Work.SymQuot.prod (C.baseChange L).toOver n ⟶
    (Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj (Work.SymQuot.Sym C n) :=
  (symPiIso K L C n).inv ≫ symqL K L C n

theorem symfL_left : (symfL K L C n).left =
    (symPiIso K L C n).inv.left ≫ (symqL K L C n).left := rfl

theorem symqL_left : (symqL K L C n).left =
    ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map (Work.SymQuot.Sym.quot C n)).left :=
  rfl

/-- The permutation action on `(C_L)ⁿ` fixes the quotient map of `(C_L)ⁿ`. -/
theorem symQuot_baseChange_invariance (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    (Work.SymQuot.symAction (C.baseChange L) n).hom σ ≫
      (Work.SymQuot.Sym.quot (C.baseChange L) n).left =
      (Work.SymQuot.Sym.quot (C.baseChange L) n).left := by
  have h := (Work.SymQuot.QuotientData.quotientMap_isInvariant
    (Work.SymQuot.symData (C.baseChange L) n)) σ
  simp only [Work.SymQuot.symData, Work.SymQuot.symAction_hom, Work.SymQuot.permGAction] at h
  exact h

/-- The permutation action fixes the quotient map of `(C_L)ⁿ`, in terms of the permutation
isomorphism of `(C_L)ⁿ`. -/
theorem symQuot_perm_invariance (σ : Equiv.Perm (Fin n)) :
    ((Work.SymQuot.permIso (C.baseChange L).toOver σ).hom).left ≫
      (Work.SymQuot.Sym.quot (C.baseChange L) n).left =
      (Work.SymQuot.Sym.quot (C.baseChange L) n).left := by
  show (Work.SymQuot.symAction (C.baseChange L) n).hom (ULift.up σ) ≫
      (Work.SymQuot.Sym.quot (C.baseChange L) n).left =
      (Work.SymQuot.Sym.quot (C.baseChange L) n).left
  exact symQuot_baseChange_invariance K L C n (ULift.up σ)

/-- The base changed quotient map is invariant under the permutation action on `(C_L)ⁿ`. -/
theorem symfL_invariant (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    (Work.SymQuot.symAction (C.baseChange L) n).hom σ ≫ (symfL K L C n).left =
      (symfL K L C n).left := by
  have hstep := congrArg Over.Hom.left (symPiIso_inv_perm K L C n σ.down)
  simp only [Over.comp_left] at hstep
  have hmap : ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
        ((Work.SymQuot.permIso C.toOver σ.down).hom ≫ Work.SymQuot.Sym.quot C n)).left =
      ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
        (Work.SymQuot.Sym.quot C n)).left := by
    have h : (Work.SymQuot.permIso C.toOver σ.down).hom ≫ Work.SymQuot.Sym.quot C n =
        Work.SymQuot.Sym.quot C n := by
      apply Over.OverMorphism.ext
      have hg := (Work.SymQuot.QuotientData.quotientMap_isInvariant
        (Work.SymQuot.symData C n)) σ
      simp only [Work.SymQuot.symData, Work.SymQuot.symAction_hom, Work.SymQuot.permGAction] at hg
      exact hg
    exact congrArg Over.Hom.left (congrArg
      (fun u => (Over.pullback (Work.CurveBasics.Curve.specMap K L)).map u) h)
  have hact : (Work.SymQuot.symAction (C.baseChange L) n).hom σ =
      ((Work.SymQuot.permIso (C.baseChange L).toOver σ.down).hom).left := by
    simp only [Work.SymQuot.symAction_hom, Work.SymQuot.permGAction]
  rw [hact, symfL_left, symqL_left]
  calc ((Work.SymQuot.permIso (C.baseChange L).toOver σ.down).hom).left ≫
        ((symPiIso K L C n).inv.left ≫
          ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
            (Work.SymQuot.Sym.quot C n)).left)
      = (((Work.SymQuot.permIso (C.baseChange L).toOver σ.down).hom).left ≫
          (symPiIso K L C n).inv.left) ≫
          ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
            (Work.SymQuot.Sym.quot C n)).left := (Category.assoc _ _ _).symm
    _ = ((symPiIso K L C n).inv.left ≫
          ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
            ((Work.SymQuot.permIso C.toOver σ.down).hom)).left) ≫
          ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
            (Work.SymQuot.Sym.quot C n)).left := by rw [hstep]
    _ = (symPiIso K L C n).inv.left ≫
          (((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
            ((Work.SymQuot.permIso C.toOver σ.down).hom)).left ≫
          ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
            (Work.SymQuot.Sym.quot C n)).left) := Category.assoc _ _ _
    _ = (symPiIso K L C n).inv.left ≫
          (((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
            ((Work.SymQuot.permIso C.toOver σ.down).hom) ≫
            (Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
              (Work.SymQuot.Sym.quot C n)).left) := by rw [← Over.comp_left]
    _ = (symPiIso K L C n).inv.left ≫
          (((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
            ((Work.SymQuot.permIso C.toOver σ.down).hom ≫ Work.SymQuot.Sym.quot C n)).left) := by
        rw [show ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
              ((Work.SymQuot.permIso C.toOver σ.down).hom ≫ Work.SymQuot.Sym.quot C n)) =
            ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
              ((Work.SymQuot.permIso C.toOver σ.down).hom) ≫
              (Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
                (Work.SymQuot.Sym.quot C n)) from
          Functor.map_comp (Over.pullback (Work.CurveBasics.Curve.specMap K L))
            (Work.SymQuot.permIso C.toOver σ.down).hom (Work.SymQuot.Sym.quot C n)]
    _ = (symPiIso K L C n).inv.left ≫
          ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
            (Work.SymQuot.Sym.quot C n)).left := by rw [hmap]

/-- The canonical identification `(X_L) ≅ X ⊗ Spec L`, for the base change map. -/
noncomputable def mapPullbackTensorIsoSm (X : Work.GCBasics.Sch K) :
    (Over.map (Work.CurveBasics.Curve.specMap K L)).obj
        ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj X) ≅
      X ⊗ Work.GCBasics.specOf K L :=
  mapPullbackTensorIso (Work.GCBasics.specOf K L) X

theorem mapPullbackTensorIsoSm_hom_left (X : Work.GCBasics.Sch K) :
    ((mapPullbackTensorIsoSm K L X).hom).left = 𝟙 _ :=
  mapPullbackTensorIso_hom_left (Work.GCBasics.specOf K L) X

theorem mapPullbackTensorIsoSm_inv_left (X : Work.GCBasics.Sch K) :
    ((mapPullbackTensorIsoSm K L X).inv).left =
      𝟙 ((Over.map (Work.CurveBasics.Curve.specMap K L)).obj
        ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj X)).left :=
  mapPullbackTensorIso_inv_left (Work.GCBasics.specOf K L) X

/-- The morphism level form of `pullback_map_left_eq_whiskerRight`. -/
theorem pullback_map_left_eq_whiskerRight_sm (X X' : Work.GCBasics.Sch K) (u : X ⟶ X') :
    ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map u).left =
      (u ▷ Work.GCBasics.specOf K L).left :=
  pullback_map_left_eq_whiskerRight (Work.GCBasics.specOf K L) X X' u

/-- The descended quotient map `(C_L)ⁿ ⟶ Symⁿ(C_L)`, over `K`. -/
noncomputable def symu : (Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj
      (Work.SymQuot.prod C.toOver n) ⟶ Work.SymQuot.Sym (C.baseChange L) n :=
  (symPiIso K L C n).hom ≫ Work.SymQuot.Sym.quot (C.baseChange L) n

theorem symu_left : (symu K L C n).left =
    (symPiIso K L C n).hom.left ≫ (Work.SymQuot.Sym.quot (C.baseChange L) n).left := rfl

/-- The comparison `Cⁿ ⊗ Spec L ⟶ (C_L)ⁿ` of `K`-schemes. -/
noncomputable def symfK : Work.SymQuot.prod C.toOver n ⊗ Work.GCBasics.specOf K L ⟶
    (Over.map (Work.CurveBasics.Curve.specMap K L)).obj (Work.SymQuot.Sym (C.baseChange L) n) :=
  (mapPullbackTensorIsoSm K L (Work.SymQuot.prod C.toOver n)).inv ≫
    (Over.map (Work.CurveBasics.Curve.specMap K L)).map (symu K L C n)

theorem symfK_left : (symfK K L C n).left = (symu K L C n).left := by
  rw [symfK, Over.comp_left, mapPullbackTensorIsoSm_inv_left, Over.map_map_left]
  exact Category.id_comp _

/-- The invariance of the comparison map `Cⁿ ⊗ Spec L ⟶ (C_L)ⁿ`. -/
theorem symfK_invariant (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    (Work.SymQuot.actOver (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
        (symData_hbase K C n) σ ▷ Work.GCBasics.specOf K L) ≫ symfK K L C n =
      symfK K L C n := by
  have hact : Work.SymQuot.actOver (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
        (symData_hbase K C n) σ =
      (Work.SymQuot.permIso C.toOver σ.down).hom := by
    apply Over.OverMorphism.ext
    rfl
  have h3 := pullback_map_left_eq_whiskerRight_sm K L (Work.SymQuot.prod C.toOver n)
    (Work.SymQuot.prod C.toOver n) (Work.SymQuot.actOver (Work.SymQuot.prod C.toOver n)
      (Work.SymQuot.symData C n) (symData_hbase K C n) σ)
  apply Over.OverMorphism.ext
  rw [Over.comp_left, ← h3, hact, symfK_left, symu_left]
  rw [← Category.assoc, ← Over.comp_left, symPiIso_perm K L C n σ.down, Over.comp_left]
  rw [Category.assoc, symQuot_perm_invariance K L C n σ.down]

/-- **The comparison map `Symⁿ(C_L) ⟶ (Symⁿ C)_L`.** -/
noncomputable def symβ : Work.SymQuot.Sym (C.baseChange L) n ⟶
    (Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj (Work.SymQuot.Sym C n) :=
  (Work.SymQuot.Sym.desc (C.baseChange L) n (symfL K L C n) (symfL_invariant K L C n)).choose

theorem symβ_spec : Work.SymQuot.Sym.quot (C.baseChange L) n ≫ symβ K L C n = symfL K L C n :=
  (Work.SymQuot.Sym.desc (C.baseChange L) n (symfL K L C n)
    (symfL_invariant K L C n)).choose_spec.1

theorem symβ_spec_left : (Work.SymQuot.Sym.quot (C.baseChange L) n).left ≫
    (symβ K L C n).left = (symfL K L C n).left :=
  congrArg Over.Hom.left (symβ_spec K L C n)

/-- **The comparison map `(Symⁿ C)_L ⟶ Symⁿ(C_L)`**, from the relative quotient property. -/
noncomputable def symγK :
    (Work.SymQuot.relQuotScheme (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
        (symData_hbase K C n)) ⊗ Work.GCBasics.specOf K L ⟶
      (Over.map (Work.CurveBasics.Curve.specMap K L)).obj (Work.SymQuot.Sym (C.baseChange L) n) := by
  haveI : IsSeparated (Work.SymQuot.prod C.toOver n).hom := inferInstance
  haveI : IsSeparated (Work.GCBasics.specOf K L).hom :=
    show IsSeparated (Work.CurveBasics.Curve.specMap K L) from inferInstance
  exact (Work.SymQuot.RelQuot.relQuot (Work.SymQuot.prod C.toOver n) (Work.GCBasics.specOf K L)
    ((Over.map (Work.CurveBasics.Curve.specMap K L)).obj (Work.SymQuot.Sym (C.baseChange L) n))
    (Work.SymQuot.symData C n) (symData_hbase K C n) (symfK K L C n)
    (symfK_invariant K L C n)).choose

theorem symγK_spec :
    (Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
      (symData_hbase K C n) ▷ Work.GCBasics.specOf K L) ≫ symγK K L C n =
      symfK K L C n := by
  haveI : IsSeparated (Work.SymQuot.prod C.toOver n).hom := inferInstance
  haveI : IsSeparated (Work.GCBasics.specOf K L).hom :=
    show IsSeparated (Work.CurveBasics.Curve.specMap K L) from inferInstance
  exact (Work.SymQuot.RelQuot.relQuot (Work.SymQuot.prod C.toOver n) (Work.GCBasics.specOf K L)
    ((Over.map (Work.CurveBasics.Curve.specMap K L)).obj (Work.SymQuot.Sym (C.baseChange L) n))
    (Work.SymQuot.symData C n) (symData_hbase K C n) (symfK K L C n)
    (symfK_invariant K L C n)).choose_spec.1

theorem symγK_spec_left :
    (Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
      (symData_hbase K C n) ▷ Work.GCBasics.specOf K L).left ≫
      (symγK K L C n).left = (symfK K L C n).left :=
  congrArg Over.Hom.left (symγK_spec K L C n)

/-- The quotient map `(Cⁿ/S_n) × Spec L` agrees, on underlying schemes, with the base change of
the quotient map of `Cⁿ`. -/
theorem symqK_left :
    (Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
      (symData_hbase K C n) ▷ Work.GCBasics.specOf K L).left =
      ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).map
        (Work.SymQuot.Sym.quot C n)).left := by
  have h : Work.SymQuot.Sym.quot C n =
      Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
        (symData_hbase K C n) := by
    apply Over.OverMorphism.ext
    rfl
  rw [show (Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n)
        (Work.SymQuot.symData C n) (symData_hbase K C n)
        ▷ Work.GCBasics.specOf K L).left =
      (Work.SymQuot.Sym.quot C n ▷ Work.GCBasics.specOf K L).left from
    congrArg Over.Hom.left (congrArg (fun u => u ▷ Work.GCBasics.specOf K L) h.symm)]
  exact (pullback_map_left_eq_whiskerRight_sm K L (Work.SymQuot.prod C.toOver n)
    (Work.SymQuot.Sym C n) (Work.SymQuot.Sym.quot C n)).symm

/-- The two comparison maps are mutually inverse: `(Symⁿ C)_L ⟶ Symⁿ(C_L) ⟶ (Symⁿ C)_L` is the
identity, by the relative quotient property of finite group quotients. -/
theorem symγK_left_comp_symβ_left :
    (symγK K L C n).left ≫ (symβ K L C n).left = 𝟙 _ := by
  let ζ : (Work.SymQuot.relQuotScheme (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
        (symData_hbase K C n)) ⊗ Work.GCBasics.specOf K L ⟶
      (Work.SymQuot.relQuotScheme (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
        (symData_hbase K C n)) ⊗ Work.GCBasics.specOf K L :=
    (symγK K L C n ≫ (Over.map (Work.CurveBasics.Curve.specMap K L)).map (symβ K L C n)) ≫
      (mapPullbackTensorIsoSm K L (Work.SymQuot.Sym C n)).hom
  have hζleft : ζ.left = (symγK K L C n).left ≫ (symβ K L C n).left := by
    simp only [ζ, Over.comp_left, Over.map_map_left, mapPullbackTensorIsoSm_hom_left,
      Category.comp_id]
  have hqinv : ∀ σ : ULift.{u} (Equiv.Perm (Fin n)),
      (Work.SymQuot.actOver (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
        (symData_hbase K C n) σ ▷ Work.GCBasics.specOf K L) ≫
      (Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
        (symData_hbase K C n) ▷ Work.GCBasics.specOf K L) =
      (Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
        (symData_hbase K C n) ▷ Work.GCBasics.specOf K L) := by
    intro σ
    have h1 : Work.SymQuot.actOver (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
          (symData_hbase K C n) σ ≫
        Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
          (symData_hbase K C n) =
        Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
          (symData_hbase K C n) := by
      apply Over.OverMorphism.ext
      have hg := (Work.SymQuot.QuotientData.quotientMap_isInvariant
        (Work.SymQuot.symData C n)) σ
      simp only [Work.SymQuot.symData, Work.SymQuot.symAction_hom,
        Work.SymQuot.permGAction] at hg
      exact hg
    have h2 : (Work.SymQuot.actOver (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
          (symData_hbase K C n) σ ≫
        Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
          (symData_hbase K C n)) ▷ Work.GCBasics.specOf K L =
        (Work.SymQuot.actOver (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
          (symData_hbase K C n) σ ▷ Work.GCBasics.specOf K L) ≫
        (Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
          (symData_hbase K C n) ▷ Work.GCBasics.specOf K L) :=
      MonoidalCategory.comp_whiskerRight _ _ _
    rw [← h2, h1]
  have hInv :
      (Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
        (symData_hbase K C n) ▷ Work.GCBasics.specOf K L) ≫ ζ =
      (Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
        (symData_hbase K C n) ▷ Work.GCBasics.specOf K L) := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hζleft]
    rw [← Category.assoc, symγK_spec_left, symfK_left, symu_left]
    rw [Category.assoc, symβ_spec_left, symfL_left]
    rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    rw [symqL_left, ← symqK_left]
    exact Category.id_comp _
  haveI : IsSeparated (Work.SymQuot.prod C.toOver n).hom := inferInstance
  haveI : IsSeparated (Work.GCBasics.specOf K L).hom :=
    show IsSeparated (Work.CurveBasics.Curve.specMap K L) from inferInstance
  have huniq := (Work.SymQuot.RelQuot.relQuot (Work.SymQuot.prod C.toOver n)
    (Work.GCBasics.specOf K L)
    ((Work.SymQuot.relQuotScheme (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
      (symData_hbase K C n)) ⊗ Work.GCBasics.specOf K L)
    (Work.SymQuot.symData C n) (symData_hbase K C n)
    (Work.SymQuot.relQuotSchemeMap (Work.SymQuot.prod C.toOver n) (Work.SymQuot.symData C n)
      (symData_hbase K C n) ▷ Work.GCBasics.specOf K L) hqinv).unique hInv
    (Category.comp_id _)
  have h2 := congrArg Over.Hom.left huniq
  rw [hζleft, Over.id_left] at h2
  exact h2

/-- The inverse comparison, as a morphism of `L`-schemes. -/
noncomputable def symh :
    (Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj (Work.SymQuot.Sym C n) ⟶
      Work.SymQuot.Sym (C.baseChange L) n :=
  Over.homMk (symγK K L C n).left (by
    rw [← Over.w (symβ K L C n), ← Category.assoc, symγK_left_comp_symβ_left K L C n]
    exact Category.id_comp _)

theorem symh_left : (symh K L C n).left = (symγK K L C n).left := rfl

theorem symh_comp_symβ : symh K L C n ≫ symβ K L C n = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.id_left, symh_left]
  exact symγK_left_comp_symβ_left K L C n

/-- The other composite `Symⁿ(C_L) ⟶ (Symⁿ C)_L ⟶ Symⁿ(C_L)` is the identity, by the
universal property of `Symⁿ(C_L)`. -/
theorem symβ_comp_symh : symβ K L C n ≫ symh K L C n = 𝟙 _ := by
  have h1 : Work.SymQuot.Sym.quot (C.baseChange L) n ≫ (symβ K L C n ≫ symh K L C n) =
      Work.SymQuot.Sym.quot (C.baseChange L) n := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    rw [← Category.assoc, symβ_spec_left, symfL_left]
    rw [Category.assoc]
    rw [show (symh K L C n).left = (symγK K L C n).left from symh_left K L C n]
    rw [symqL_left, ← symqK_left]
    rw [symγK_spec_left, symfK_left, symu_left]
    rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    exact Category.id_comp _
  exact (Work.SymQuot.Sym.desc (C.baseChange L) n (Work.SymQuot.Sym.quot (C.baseChange L) n)
    (symQuot_baseChange_invariance K L C n)).unique h1 (Category.comp_id _)

/-- **Base change of the symmetric power: `Symⁿ(C_L) ≅ (Symⁿ C)_L`.** -/
noncomputable def symBaseChangeIso : Work.SymQuot.Sym (C.baseChange L) n ≅
    (Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj (Work.SymQuot.Sym C n) :=
  Iso.mk (symβ K L C n) (symh K L C n) (symβ_comp_symh K L C n) (symh_comp_symβ K L C n)

end Construction

open CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
theorem exists_symBaseChangeIso {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [Work.SymQuot.CurveAffineCover C] (n : ℕ) {L : Type u} [Field L] [Algebra K L] :
    ∃ β : Work.SymQuot.Sym (C.baseChange L) n ⟶
        (Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj (Work.SymQuot.Sym C n),
      IsIso β :=
  ⟨(symBaseChangeIso K L C n).hom, (symBaseChangeIso K L C n).isIso_hom⟩

end Work.SymQuot.BaseChange
