/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base change of the divisor function `divOf` of a point of `Symⁿ C`

This file proves the naturality of the point/divisor dictionary of the `n`-th symmetric power
along a field extension `F → F'`:

`divOf F' (RPt.map e p) = DivBase.bc e (divOf F p)`.

Since `DivBase.bc` is realised (`Submission/Work/SymQuot/DivBaseInst.lean`) as the
ramification-weighted pullback of divisors along the tower square `C_{F'} ⟶ C_F`, the statement
is a computation of `divOf` after base change.

## Proof

`divOf` is defined via a *non-canonically chosen* chart (`chartOf`), so the proof does not
compare charts directly.  Instead it computes both sides after base change to an algebraically
closed extension `Ω ⊇ F'`, where the hub lemma C1′ (`divMap_divOfChart`) is available by
construction.

* Choose `x : Fin n → C(Ω)` with `powMap x = RPt.map p` (`Sym.exists_powMap_eq`, which needs `Ω`
  algebraically closed).
* The base change of the right-hand side to `Ω` is
  `(bcSquareTower F' Ω).divMap ((bcSquareTower F F').divMap (divOf F p))`; by functoriality of
  the pullback of divisors along the composed tower (`bcSquareTower_comp`, `divMap_comp`) this is
  `(bcSquareTower F Ω).divMap (divOf F p)`, which is `∑ m, ptDiv (x m)` by C1′ at the chart
  `chartOf C n p`.
* The base change of the left-hand side to `Ω` is `∑ m, ptDiv (x m)` by C1′ at the chart
  `chartOf C n (RPt.map p)`, using the same lift `x`.
* Both sides therefore have the same image under the injective pullback
  `(bcSquareTower F' Ω).divMap` (`divMap_injective`), so they are equal.
-/
import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.DivOf.divMap_injective
import Submission.Work.SymQuot.Sym.exists_powMap_eq
import Submission.Work.SymQuot.Sym.exists_finite_lift
import Submission.Work.SymQuot.DivOf.DivOf
import Submission.Work.SymQuot.DivBaseInst
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SymQuot.DivOf.divMap_divOfChart
import Submission.Work.SymQuot.Sym.exists_finite_lift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

open Work.CurveBasics

/-- **`divOf` in the canonical tower.**  For a tower of fields `K → F → F'` and an auxiliary
algebraically closed field `Ω` above `F'`, the divisor of the base change of a point `p` of
`Symⁿ C` over `F` is the ramification-weighted pullback of the divisor of `p`, computed after
base change to `Ω`.

This is the technical core of `divOf_map`: the auxiliary field `Ω` is where the non-canonically
chosen chart of `divOf` can be replaced by a splitting `powMap x` of the base-changed point. -/
theorem divOf_map_tower {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C]
    {F F' Ω : Type u} [Field F] [Field F'] [Field Ω]
    [Algebra K F] [Algebra K F'] [Algebra F F']
    [Algebra K Ω] [Algebra F Ω] [Algebra F' Ω]
    [IsScalarTower K F F'] [IsScalarTower K F Ω] [IsScalarTower F F' Ω] [IsScalarTower K F' Ω]
    [IsAlgClosed Ω]
    (p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F) :
    divOf F' (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F') p) =
      (bcSquareTower (C := C) F F').divMap (divOf F p) := by
  classical
  -- Split the base change of `p` to `Ω` into `n` points of `C`.
  obtain ⟨x, hx⟩ := Work.SymQuot.Sym.exists_powMap_eq C n
    (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F Ω) p)
  -- The chosen charts are nonempty.
  have hnon : Nonempty (chartOf C n p).V := chartOf_nonempty C n p
  have hnon' : Nonempty (chartOf C n
      (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F') p)).V :=
    chartOf_nonempty C n _
  -- The two algebra maps `F → Ω` (directly and through `F'`) agree.
  have hcomp : (IsScalarTower.toAlgHom K F' Ω).comp (IsScalarTower.toAlgHom K F F') =
      IsScalarTower.toAlgHom K F Ω := by
    ext y
    exact (IsScalarTower.algebraMap_apply F F' Ω y).symm
  -- The same splitting `x` lifts the base change of `p` over `F'`.
  have hx' : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F' Ω)
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F') p) := by
    rw [← Work.SpecLin.RPt.map_comp, hcomp]
    exact hx
  -- Right-hand side, base changed to `Ω`: reassociate the tower and apply C1′ at `p`.
  have hR : (bcSquareTower (C := C) F' Ω).divMap
        ((bcSquareTower (C := C) F F').divMap (divOf F p)) = ∑ m, Work.SpecLin.ptDiv (x m) := by
    have hcomp2 : (bcSquareTower (C := C) F' Ω).divMap.comp
          (bcSquareTower (C := C) F F').divMap =
        (bcSquareTower (C := C) F Ω).divMap := by
      rw [← Work.CurveBasics.Curve.BCSquare.divMap_comp
        (S := bcSquareTower (C := C) F F') (T := bcSquareTower (C := C) F' Ω)]
      rw [Work.SymQuot.bcSquareTower_comp (C := C) (F := F) (F' := F') (F'' := Ω)]
    calc (bcSquareTower (C := C) F' Ω).divMap
            ((bcSquareTower (C := C) F F').divMap (divOf F p))
        = ((bcSquareTower (C := C) F' Ω).divMap.comp (bcSquareTower (C := C) F F').divMap)
            (divOf F p) := rfl
      _ = (bcSquareTower (C := C) F Ω).divMap (divOf F p) := by rw [hcomp2]
      _ = (bcSquareTower (C := C) F Ω).divMap (divOfChart F (chartOf C n p)) := rfl
      _ = ∑ m, Work.SpecLin.ptDiv (x m) := by
            exact divMap_divOfChart (C := C) (n := n) (F := F) (F' := Ω) (p := p)
              (chartOf C n p) x hx
  -- Left-hand side, base changed to `Ω`: C1′ at the base change of `p`.
  have hL : (bcSquareTower (C := C) F' Ω).divMap
        (divOf F' (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F') p)) =
        ∑ m, Work.SpecLin.ptDiv (x m) := by
    exact divMap_divOfChart (C := C) (n := n) (F := F') (F' := Ω)
      (p := Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F') p)
      (chartOf C n (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F') p)) x hx'
  -- Conclude by injectivity of the pullback along `F' → Ω`.
  exact Work.SymQuot.DivOf.divMap_injective (bcSquareTower (C := C) F' Ω) (by rw [hL, hR])

/-- **Naturality of `divOf` under a field extension** `e : F →ₐ[K] F'`: the divisor of the base
change of a point `p` of `Symⁿ C` is the base change of its divisor. -/
theorem divOf_map {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F F' : Type u} [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F')
    (p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F) :
    divOf F' (Work.SpecLin.RPt.map e p) = Work.SpecLin.DivBase.bc e (divOf F p) := by
  -- The `DivBase` instance uses the algebra structure on `F'` induced by `e`.
  letI : Algebra F F' := e.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := Work.SymQuot.isScalarTower_of_algHom e
  -- In that structure the structure map `F → F'` is `e`.
  have he : IsScalarTower.toAlgHom K F F' = e := by ext y; rfl
  -- Apply the canonical form with an algebraic closure of `F'`.
  have hcanon := divOf_map_tower (C := C) (n := n) (F := F) (F' := F')
    (Ω := AlgebraicClosure F') p
  rw [he] at hcanon
  rw [hcanon]
  -- `DivBase.bc e` is *defined* as the pullback along the tower square.
  rfl

end Work.SymQuot.DivOf
