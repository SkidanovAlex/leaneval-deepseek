/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The base change of divisors as a `DivBase` instance (area SY)

Area `PR` consumes the interface `Work.SpecLin.DivBase C`: pullback of divisors along a field
extension `F → F'`, with its elementary properties.  The axioms of that interface do **not**
determine the pullback (in particular they do not constrain the *support* of `bc e D`), so
`SymGeom.divOf_map` can only be proved against a *concrete* realisation of `bc`.  This file
provides it: the ramification-weighted pullback of divisors along the tower square

`C_{F'} ⟶ C_F` over `Spec F' ⟶ Spec F`,

i.e. `bc e D = (bcSquareTower F F').divMap D`, where `Algebra F F'` is the algebra structure
induced by `e`.  This is *definitionally* the base change of area CB (their
`Curve.BCSquare.divMap` of the canonical tower square), so nothing here is a new mathematical
choice.

## Main results

* `Work.SymQuot.bcTower` — the pullback `Dv C F →+ Dv C F'` along the tower square;
* `Work.SymQuot.towerHom_comp`, `Work.SymQuot.bcSquareTower_comp` — the tower squares of a
  composable pair of field extensions compose (so pullback is functorial);
* `Work.SymQuot.instDivBase` — the `SpecLin.DivBase C` instance with `bc = bcTower`.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.TowerSquare
import Submission.Work.SymQuot.DivOf.divMap_self
import Submission.Work.RiemannRoch.ExportCB
import Submission.Work.CurveBasics.Curve.BCSquare.divMap_comp
import Submission.Work.CurveBasics.Curve.BCSquare.linEquiv_divMap_iff
import Submission.Work.SpecLin.Interface

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

open Work.CurveBasics

variable {K : Type u} [Field K] {C : Curve K}

/-- The `IsScalarTower` condition for the algebra structure `Algebra F F'` induced by an
algebra homomorphism `e : F →ₐ[K] F'`. -/
theorem isScalarTower_of_algHom {F F' : Type u} [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F →ₐ[K] F') :
    letI : Algebra F F' := e.toRingHom.toAlgebra
    IsScalarTower K F F' := by
  letI : Algebra F F' := e.toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)

section Tower

variable {F F' F'' : Type u} [Field F] [Field F'] [Field F'']
variable [Algebra K F] [Algebra K F'] [Algebra K F'']

/-- The `snd` component of the tower morphism, phrased with the raw pullback projection (this
is what the `rw` matcher sees, since `Curve.baseChangeHom` is not an `abbrev`). -/
theorem towerHom_snd_pullback [Algebra F F'] [IsScalarTower K F F'] :
    DivOf.BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F') ≫
        pullback.snd C.hom (Curve.specMap K F) =
      pullback.snd C.hom (Curve.specMap K F') ≫ Curve.specMap F F' := by
  have h : pullback.snd C.hom (Curve.specMap K F) = C.baseChangeHom F := rfl
  have h' : pullback.snd C.hom (Curve.specMap K F') = C.baseChangeHom F' := rfl
  rw [h, h', DivOf.BCSquareBaseChange.towerHom_snd]

/-- **The tower morphisms of a composable pair of field extensions compose.**  This is the
`π`-component of `bcSquareTower_comp`. -/
theorem towerHom_comp [Algebra F F'] [Algebra F' F''] [Algebra F F'']
    [IsScalarTower K F F'] [IsScalarTower K F' F''] [IsScalarTower K F F'']
    [IsScalarTower F F' F''] :
    DivOf.BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F'')
      = DivOf.BCSquareBaseChange.towerHom (C := C) (F := F') (F' := F'')
        ≫ DivOf.BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F') := by
  refine IsPullback.hom_ext (IsPullback.of_hasPullback C.hom (Curve.specMap K F)) ?_ ?_
  · rw [DivOf.BCSquareBaseChange.towerHom_fst (C := C) (F := F) (F' := F''),
      Category.assoc,
      DivOf.BCSquareBaseChange.towerHom_fst (C := C) (F := F) (F' := F'),
      DivOf.BCSquareBaseChange.towerHom_fst (C := C) (F := F') (F' := F'')]
  · rw [towerHom_snd_pullback (C := C) (F := F) (F' := F''),
      Category.assoc,
      towerHom_snd_pullback (C := C) (F := F) (F' := F'),
      ← Category.assoc,
      towerHom_snd_pullback (C := C) (F := F') (F' := F''),
      Category.assoc,
      ← DivOf.BCSquareBaseChange.specMap_tower (K := F) (F := F') (F' := F'')]

/-- Two base-change squares with the same projection are equal (the cartesianness is a
proposition). -/
theorem bcSquare_eq_of_pi {F : Type u} [Field F] [Algebra K F]
    {C₁ : Curve K} {C₂ : Curve F} {S T : Curve.BCSquare C₁ C₂} (h : S.π = T.π) : S = T := by
  cases S with
  | mk π hπ =>
    cases T with
    | mk π' hπ' =>
      simp only at h
      subst h
      rfl

/-- **The tower base-change squares of a composable pair of field extensions compose.** -/
theorem bcSquareTower_comp [Algebra F F'] [Algebra F' F''] [Algebra F F'']
    [IsScalarTower K F F'] [IsScalarTower K F' F''] [IsScalarTower K F F'']
    [IsScalarTower F F' F''] :
    DivOf.bcSquareTower (C := C) F F''
      = (DivOf.bcSquareTower (C := C) F F').comp (DivOf.bcSquareTower (C := C) F' F'') := by
  have hπ : (DivOf.bcSquareTower (C := C) F F'').π
      = ((DivOf.bcSquareTower (C := C) F F').comp
          (DivOf.bcSquareTower (C := C) F' F'')).π :=
    towerHom_comp (C := C) (F := F) (F' := F') (F'' := F'')
  exact bcSquare_eq_of_pi hπ

end Tower

/-- **Base change of divisors along a tower square**: the pullback of divisors
`Dv C F →+ Dv C F'` determined by the canonical morphism `C_{F'} ⟶ C_F`. -/
noncomputable def bcTower (F F' : Type u) [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] : SpecLin.Dv C F →+ SpecLin.Dv C F' :=
  (DivOf.bcSquareTower (C := C) F F').divMap

/-- **The pullback of divisors along a field extension, ramification-weighted**, as an instance
of the interface `Work.SpecLin.DivBase`. -/
noncomputable instance instDivBase (C : Curve K) : SpecLin.DivBase C where
  bc := fun {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F')
      (D : SpecLin.Dv C F) => by
    letI : Algebra F F' := e.toRingHom.toAlgebra
    haveI : IsScalarTower K F F' := isScalarTower_of_algHom e
    exact (DivOf.bcSquareTower (C := C) F F').divMap D
  bc_zero := by
    intro F F' _ _ _ _ e
    letI : Algebra F F' := e.toRingHom.toAlgebra
    haveI : IsScalarTower K F F' := isScalarTower_of_algHom e
    show (DivOf.bcSquareTower (C := C) F F').divMap (0 : SpecLin.Dv C F) = 0
    exact map_zero _
  bc_add := by
    intro F F' _ _ _ _ e D D'
    letI : Algebra F F' := e.toRingHom.toAlgebra
    haveI : IsScalarTower K F F' := isScalarTower_of_algHom e
    show (DivOf.bcSquareTower (C := C) F F').divMap (D + D')
      = (DivOf.bcSquareTower (C := C) F F').divMap D
        + (DivOf.bcSquareTower (C := C) F F').divMap D'
    exact map_add _ _ _
  bc_neg := by
    intro F F' _ _ _ _ e D
    letI : Algebra F F' := e.toRingHom.toAlgebra
    haveI : IsScalarTower K F F' := isScalarTower_of_algHom e
    show (DivOf.bcSquareTower (C := C) F F').divMap (-D)
      = -(DivOf.bcSquareTower (C := C) F F').divMap D
    exact map_neg _ _
  isEffective_bc := by
    intro F F' _ _ _ _ e D hD
    letI : Algebra F F' := e.toRingHom.toAlgebra
    haveI : IsScalarTower K F F' := isScalarTower_of_algHom e
    show ((DivOf.bcSquareTower (C := C) F F').divMap D).IsEffective
    exact Curve.BCSquare.divMap_isEffective _ hD
  deg_bc := by
    intro F F' _ _ _ _ e D
    letI : Algebra F F' := e.toRingHom.toAlgebra
    haveI : IsScalarTower K F F' := isScalarTower_of_algHom e
    show (C.baseChange F').deg ((DivOf.bcSquareTower (C := C) F F').divMap D)
      = (C.baseChange F).deg D
    exact RiemannRoch.Curve.deg_divMap _ D
  bc_id := by
    intro F _ _ D
    letI : Algebra F F := (AlgHom.id K F).toRingHom.toAlgebra
    haveI : IsScalarTower K F F := isScalarTower_of_algHom (AlgHom.id K F)
    show (DivOf.bcSquareTower (C := C) F F).divMap D = D
    exact DivOf.divMap_self F D
  bc_comp := by
    intro F F' F'' _ _ _ _ _ _ e e' D
    letI : Algebra F F' := e.toRingHom.toAlgebra
    letI : Algebra F' F'' := e'.toRingHom.toAlgebra
    letI : Algebra F F'' := (e'.comp e).toRingHom.toAlgebra
    haveI : IsScalarTower K F F' := isScalarTower_of_algHom e
    haveI : IsScalarTower K F' F'' := isScalarTower_of_algHom e'
    haveI : IsScalarTower K F F'' := isScalarTower_of_algHom (e'.comp e)
    haveI : IsScalarTower F F' F'' :=
      IsScalarTower.of_algebraMap_eq (fun x => rfl)
    show (DivOf.bcSquareTower (C := C) F F'').divMap D
      = (DivOf.bcSquareTower (C := C) F' F'').divMap
          ((DivOf.bcSquareTower (C := C) F F').divMap D)
    rw [bcSquareTower_comp (C := C) (F := F) (F' := F') (F'' := F''),
      Curve.BCSquare.divMap_comp]
    rfl
  linEquiv_bc := by
    intro F F' _ _ _ _ e D D' h
    letI : Algebra F F' := e.toRingHom.toAlgebra
    haveI : IsScalarTower K F F' := isScalarTower_of_algHom e
    exact (Curve.BCSquare.linEquiv_divMap_iff (DivOf.bcSquareTower (C := C) F F') D D').mpr h
  linEquiv_bc_iff := by
    intro F F' _ _ _ _ e D D'
    letI : Algebra F F' := e.toRingHom.toAlgebra
    haveI : IsScalarTower K F F' := isScalarTower_of_algHom e
    exact Curve.BCSquare.linEquiv_divMap_iff (DivOf.bcSquareTower (C := C) F F') D D'

end Work.SymQuot
