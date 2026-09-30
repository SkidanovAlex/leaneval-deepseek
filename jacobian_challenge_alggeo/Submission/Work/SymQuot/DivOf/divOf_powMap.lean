/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `divOf (powMap x) = ∑ ptDiv (x m)`

The divisor of the point `powMap C n x` of `Symⁿ C` obtained from `n` `F`-points of `C` is the
sum of the point divisors.

The proof goes through the hub lemma `divMap_divOfChart` (C1′ of
`Submission/Work/NOTES_LEAD_jacobian_divof.md`, proved in
`Submission/Work/SymQuot/DivOf/divMap_divOfChart.lean`): for *any* chart `d` of a point `p` and
*any* field extension `F' ⊇ F` over which `p` has a lift `x : Fin n → C(F')`, the base change of
`divOfChart F d` along `C_{F'} → C_F` is `∑ m, ptDiv (x m)`.  Specialising to the identity
extension `F' = F` (where base change of divisors is the identity, `divMap_self`) and to the
chart `powMap C n x` chosen by `divOf` gives the claim.

The scaffolding of the alternative (chart-`χ_b`) route — the chosen chart `chartOf`, the value
maps `valAt`, the description of the `χ_b(b)` generators and the dictionary between the value
maps and the place ideals — lives in `Submission.Work.SymQuot.DivOf.powMapAux`.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.DivOf
import Submission.Work.SymQuot.DivOf.CharIdeal
import Submission.Work.SymQuot.DivOf.le_placeOrder_iff
import Submission.Work.SymQuot.DivOf.localIdealSet_mem_iff
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SymQuot.DivOf.powMapAux
import Submission.Work.SymQuot.DivOf.divMap_self
import Submission.Work.SymQuot.DivOf.divMap_divOfChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

open Work.CurveBasics

/-- **C1′ in the trivial case `F' = F`.**  The base change of the divisor of a point `p` of
`Symⁿ C` along the identity field extension is `divOfChart F d` itself, while
`divMap_divOfChart` identifies it with `∑ m, ptDiv (x m)` for any lift `x` of `p` over `F`. -/
theorem divOfChart_eq_sum_ptDiv {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p) [Nonempty d.V]
    (x : Fin n → Work.SpecLin.CurveFPt C F)
    (hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F) p) :
    divOfChart F d = ∑ m, Work.SpecLin.ptDiv (x m) := by
  have h := divMap_divOfChart (C := C) (n := n) (F := F) (F' := F) (p := p) (d := d) x hx
  rwa [divMap_self] at h

theorem divOf_powMap {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    (x : Fin n → Work.SpecLin.CurveFPt C F) :
    Work.SymQuot.DivOf.divOf F (Work.SymQuot.Sym.powMap C n x) =
      ∑ m, Work.SpecLin.ptDiv (x m) := by
  classical
  haveI : Nonempty (chartOf C n (Work.SymQuot.Sym.powMap C n x)).V :=
    chartOf_nonempty C n (Work.SymQuot.Sym.powMap C n x)
  have hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F) (Work.SymQuot.Sym.powMap C n x) := by
    rw [show IsScalarTower.toAlgHom K F F = AlgHom.id K F from
      AlgHom.ext (fun c => by simp [IsScalarTower.toAlgHom_apply]), Work.SpecLin.RPt.map_id]
  rw [show Work.SymQuot.DivOf.divOf F (Work.SymQuot.Sym.powMap C n x) =
      divOfChart F (chartOf C n (Work.SymQuot.Sym.powMap C n x)) from rfl]
  exact divOfChart_eq_sum_ptDiv (chartOf C n (Work.SymQuot.Sym.powMap C n x)) x hx

end Work.SymQuot.DivOf
