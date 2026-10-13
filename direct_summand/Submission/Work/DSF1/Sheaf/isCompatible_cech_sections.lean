import Mathlib
import Submission.Work.DSF1.Sheaf.CechSheafRestr
import Submission.Work.DSF1.Sheaf.SSECore

/-!
# Compatibility of the Čech sections of `restrP P W`

If `x` is a `0`-cocycle of the Čech complex of `U` with coefficients in the restriction
`restrP P W` (`V ↦ P (V ⊓ W)`), then the family of sections of `P` on the opens
`Uₐ ⊓ W` obtained as the components of `x` is compatible: the Čech-cocycle condition says
precisely that the components agree on the pairwise intersections.

This is the form of the descent condition consumed by
`Work.DSF1.Sheaf.cechTrivAll_of_restrP` and its neighbours.
-/

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

section Helpers

-- `restrP` is a plain `def`; its unfolding has to be visible to the `rw`-machinery used below.
set_option allowUnsafeReducibility true in
attribute [local reducible] restrP

/-- The component `π_b` of a product, transported along an equality of the indices `a = b`,
becomes the component `π_a`.  The transport is the canonical isomorphism of the presheaf
between the two (equal) opens. -/
lemma map_eqToHom_π {X : AlgebraicGeometry.Scheme.{u}} {Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}}
    {I : Type u} (f : I → X.Opens) {a b : I} (hab : a = b)
    (u : ↥(∏ᶜ (fun i => Q.obj (op (f i))))) :
    Q.map (eqToHom (congrArg f hab)).op ((Pi.π (fun i => Q.obj (op (f i))) b) u)
      = (Pi.π (fun i => Q.obj (op (f i))) a) u := by
  subst hab
  simp

/-- Precomposing a restriction `homOfLE h` with the transport along an equality of opens. -/
lemma eqToHom_map_homOfLE {X : AlgebraicGeometry.Scheme.{u}} (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {A' B' C : X.Opens} (e : A' = B') (h : A' ≤ C) (z : Q.obj (op C)) :
    Q.map (eqToHom e.symm).op (Q.map (homOfLE h).op z)
      = Q.map (homOfLE ((le_of_eq e.symm).trans h)).op z := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 1

/-- The two restriction maps of a `restrP` compose to a single one. -/
lemma restrP_map_map_apply {X : AlgebraicGeometry.Scheme.{u}}
    {P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} {W : X.Opens} {a b c : X.Opens}
    (γ : c ⟶ b) (δ : b ⟶ a) (z : P.obj (op (a ⊓ W))) :
    (restrP P W).map γ.op ((restrP P W).map δ.op z)
      = P.map (homOfLE (inf_le_inf_right W (leOfHom (γ ≫ δ)))).op z := by
  have hγ : (restrP P W).map γ.op
      = P.map (homOfLE (inf_le_inf_right W (leOfHom γ))).op := rfl
  have hδ : (restrP P W).map δ.op
      = P.map (homOfLE (inf_le_inf_right W (leOfHom δ))).op := rfl
  rw [hγ, hδ]
  rw [show P.map (homOfLE (inf_le_inf_right W (leOfHom γ))).op
        (P.map (homOfLE (inf_le_inf_right W (leOfHom δ))).op z)
      = P.map ((homOfLE (inf_le_inf_right W (leOfHom δ))).op
          ≫ (homOfLE (inf_le_inf_right W (leOfHom γ))).op) z from by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]]
  exact congrArg (fun m => P.map m z)
    (Subsingleton.elim (α := (op (a ⊓ W) ⟶ op (c ⊓ W))) _ _)

end Helpers

theorem isCompatible_cech_sections {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens)
    (P : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})) (W : X.Opens)
    (x : (((CategoryTheory.cechComplexFunctor U).obj (Work.DSF1.Sheaf.restrP P W)).X 0))
    (hx : ((CategoryTheory.cechComplexFunctor U).obj (Work.DSF1.Sheaf.restrP P W)).d 0 1 x = 0) :
    TopCat.Presheaf.IsCompatible (X := (X : TopCat.{u})) P
      (fun a : (Work.DSF1.Sheaf.cechN U 0).I => (Work.DSF1.Sheaf.cechN U 0).obj a ⊓ W)
      (fun a : (Work.DSF1.Sheaf.cechN U 0).I =>
        (CategoryTheory.Limits.Pi.π (fun a' : (Work.DSF1.Sheaf.cechN U 0).I =>
          P.obj (Opposite.op ((Work.DSF1.Sheaf.cechN U 0).obj a' ⊓ W))) a) x) := by
  intro i j
  -- the components of `x` at `i` and at `j`
  let πi := (Pi.π (fun a' : (cechN U 0).I => P.obj (op ((cechN U 0).obj a' ⊓ W))) i) x
  let πj := (Pi.π (fun a' : (cechN U 0).I => P.obj (op ((cechN U 0).obj a' ⊓ W))) j) x
  -- the `0`-cocycle condition, evaluated at the pair `(i,j)` of the Čech nerve
  have hraw := d01_apply (U := U) (P := restrP P W) x (pairTuple U i j)
  rw [hx] at hraw
  simp only [map_zero] at hraw
  have hkey := sub_eq_zero.mp hraw.symm
  -- replace the components at the two composite indices by the components at `i` and `j`
  rw [← map_eqToHom_π (Q := restrP P W) (f := fun a : (cechN U 0).I => (cechN U 0).obj a)
      (pairTuple_comp_succAbove_zero U i j) x] at hkey
  rw [← map_eqToHom_π (Q := restrP P W) (f := fun a : (cechN U 0).I => (cechN U 0).obj a)
      (pairTuple_comp_succAbove_one U i j) x] at hkey
  let φ0 := (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 0)).φ (pairTuple U i j))
  let φ1 := (((FormalCoproduct.mk ι U).mapPower (Fin.succAbove 1)).φ (pairTuple U i j))
  let ec0 := congrArg (fun a : (cechN U 0).I => (cechN U 0).obj a)
    (pairTuple_comp_succAbove_zero U i j)
  let ec1 := congrArg (fun a : (cechN U 0).I => (cechN U 0).obj a)
    (pairTuple_comp_succAbove_one U i j)
  have c0 : (restrP P W).map (φ0.op) ((restrP P W).map (eqToHom ec0).op πj)
      = P.map (homOfLE (inf_le_inf_right W (leOfHom (φ0 ≫ eqToHom ec0)))).op πj :=
    restrP_map_map_apply φ0 (eqToHom ec0) πj
  have c1 : (restrP P W).map (φ1.op) ((restrP P W).map (eqToHom ec1).op πi)
      = P.map (homOfLE (inf_le_inf_right W (leOfHom (φ1 ≫ eqToHom ec1)))).op πi :=
    restrP_map_map_apply φ1 (eqToHom ec1) πi
  have step : P.map (homOfLE (inf_le_inf_right W (leOfHom (φ0 ≫ eqToHom ec0)))).op πj
      = P.map (homOfLE (inf_le_inf_right W (leOfHom (φ1 ≫ eqToHom ec1)))).op πi :=
    (c0.symm.trans hkey).trans c1
  -- the two descriptions of the open over which both restrictions live
  have e : (cechN U 1).obj (pairTuple U i j) ⊓ W
      = ((cechN U 0).obj i ⊓ W) ⊓ ((cechN U 0).obj j ⊓ W) := by
    rw [cechN1_obj_pair U i j]
    apply le_antisymm
    · exact le_inf (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)
        (le_inf (le_trans inf_le_left inf_le_right) inf_le_right)
    · exact le_inf (le_inf (le_trans inf_le_left inf_le_left) (le_trans inf_le_right inf_le_left))
        (le_trans inf_le_right inf_le_right)
  have hse_i : Opens.infLELeft ((cechN U 0).obj i ⊓ W) ((cechN U 0).obj j ⊓ W)
      = homOfLE ((le_of_eq e.symm).trans
          (inf_le_inf_right W (leOfHom (φ1 ≫ eqToHom ec1)))) :=
    Subsingleton.elim _ _
  have hse_j : homOfLE ((le_of_eq e.symm).trans
        (inf_le_inf_right W (leOfHom (φ0 ≫ eqToHom ec0))))
      = Opens.infLERight ((cechN U 0).obj i ⊓ W) ((cechN U 0).obj j ⊓ W) :=
    Subsingleton.elim _ _
  have key_i : P.map (Opens.infLELeft ((cechN U 0).obj i ⊓ W)
        ((cechN U 0).obj j ⊓ W)).op πi
      = P.map (homOfLE ((le_of_eq e.symm).trans
          (inf_le_inf_right W (leOfHom (φ1 ≫ eqToHom ec1))))).op πi := by
    rw [hse_i]
  have key_j : P.map (homOfLE ((le_of_eq e.symm).trans
        (inf_le_inf_right W (leOfHom (φ0 ≫ eqToHom ec0))))).op πj
      = P.map (Opens.infLERight ((cechN U 0).obj i ⊓ W)
        ((cechN U 0).obj j ⊓ W)).op πj := by
    rw [hse_j]
  exact key_i.trans (((eqToHom_map_homOfLE P e
        (inf_le_inf_right W (leOfHom (φ1 ≫ eqToHom ec1))) πi).symm).trans
      ((congrArg (fun w => P.map (eqToHom e.symm).op w) step.symm).trans
        ((eqToHom_map_homOfLE P e
          (inf_le_inf_right W (leOfHom (φ0 ≫ eqToHom ec0))) πj).trans key_j)))

end Work.DSF1.Sheaf
