/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — the chart datum in the shape consumed by area `GC`

`NOTES_LEAD_jacobian_GC.md` §3.6 declares the API of area `GC`
(`Submission/Work/GroupChunk/`).  Its class `Work.GroupChunk.Input` bundles the outputs of
areas SY, RR, CH and DM; the fields coming from area CH are `V`, `ell_eq_one_of_landsIn`,
`ι`, `fintype`, `E` and `cov`.  This file collects exactly those fields as a structure
`Work.Charts.ChartDatum`, shows that a `Charts` (the `BNData` + covering bundle of this area)
produces it, and records the named input `HasChartDatum`.

Nothing here is new mathematics: it is the interface between the two areas.
-/
import Submission.Work.Charts.Cover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.dupNamespace false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-! ### The chart, as a point of the open subscheme -/

/-- **The GC form of `ℓ = 1` on the chart**: for a point `p` of the open subscheme `V` itself,
the divisor of the associated point of `Sym^g C` has `ℓ = 1`.

This is the form in which area `GC` consumes the Brill–Noether chart (its field
`Input.ell_eq_one_of_landsIn`); it is `BNData.ell_eq_one_of_landsIn` together with the fact
that the inclusion `V ↪ Sym^g C` composed with `p` lands in `V`. -/
theorem BNData.ell_eq_one_of_landsIn' {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] (d : BNData C R) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver d.V) F) :
    ell C (divOf (p ≫ Opens.ιOver d.V)) = 1 :=
  d.ell_eq_one_of_landsIn _ ((RPt.landsIn_preimage p (Opens.ιOver d.V) d.V).mpr (by
    rw [Opens.ιOver_left, Scheme.Opens.ι_preimage_self]
    exact RPt.landsIn_top p))

/-! ### The chart datum of area `GC` -/

/-- **The chart datum of area `GC`.**  This is exactly the CH-part of the class
`Work.GroupChunk.Input`: the Brill–Noether chart `V ⊆ Sym^g C` (with `ℓ = 1` on its points),
a finite family of centres `E i` and the covering property `cov`. -/
structure ChartDatum (C : Curve K) [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (P0 : 𝟙_ (Sch K) ⟶ C.toOver) where
  /-- the Brill–Noether chart -/
  V : (Sym C R.g).left.Opens
  /-- the chart is affine (it is `D(δ)` inside the affine chart `Sym^g(U)`) -/
  isAffineOpen_V : IsAffineOpen V
  /-- `ℓ = 1` on the points of the chart (area CH; the Brill–Noether property) -/
  ell_eq_one_of_landsIn : ∀ {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver V) F), ell C (divOf (p ≫ Opens.ιOver V)) = 1
  /-- the index set of centres -/
  ι : Type u
  [fintype : Fintype ι]
  /-- the centres of the charts -/
  E : ι → FPt (Sym C R.g) K
  /-- COV: every degree-zero class over every field extension is representable in a chart -/
  cov : ∀ {F : Type u} [Field F] [Algebra K F] (c : Pic0 C F), ∃ i : ι,
    ∃ y : FPt (Sym C R.g) F, y.LandsIn V ∧
      chartClass y (RPt.map (IsScalarTower.toAlgHom K K F) (E i)) = c

/-- A `Charts` (chart datum + covering, with the Brill–Noether chart coming from a canonical
divisor) produces the chart datum of area `GC`. -/
def Charts.toChartDatum {C : Curve K} [Work.SpecLin.DivBase C] {R : RochData C}
    [Work.SpecLin.SymGeom C R.g] {P0 : 𝟙_ (Sch K) ⟶ C.toOver} (D : Charts C R P0) :
    ChartDatum C R P0 where
  V := D.d.V
  isAffineOpen_V := D.d.isAffineOpen_V
  ell_eq_one_of_landsIn := D.d.ell_eq_one_of_landsIn'
  ι := D.ι
  fintype := D.fintype
  E := D.E
  cov := D.cov

/-- **Area `CH`, named input: the chart datum.**  Every curve over a field carries the
Brill–Noether chart datum of §3.5. -/
class HasChartDatum (K : Type u) [Field K] : Prop where
  /-- the chart datum -/
  exists_chartDatum : ∀ (C : Curve K) [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (P0 : 𝟙_ (Sch K) ⟶ C.toOver), Nonempty (ChartDatum C R P0)

/-- The chart datum of area `GC`, from the named input of area `CH`. -/
theorem exists_chartDatum [HasChartDatum K] (C : Curve K) [Work.SpecLin.DivBase C]
    (R : RochData C) [Work.SpecLin.SymGeom C R.g] (P0 : 𝟙_ (Sch K) ⟶ C.toOver) :
    Nonempty (ChartDatum C R P0) :=
  HasChartDatum.exists_chartDatum C R P0

end

end Work.Charts
