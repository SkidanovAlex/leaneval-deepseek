/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The lift of a point of `Symⁿ C` lands in the chart (area SY, `divOf`)

Let `p : Spec F ⟶ Symⁿ C` be a point of the `n`-th symmetric power of a curve `C`, let
`d : ChartPt C n p` be a chart of `p` (an affine open `V ⊆ C` whose chart `Spec A`,
`A = Γ(Cⁿ,Vⁿ)^{S_n}`, contains `p`), and let `F'' ⊇ F` be a field extension.

If `x : Fin n → C(F'')` is a family of `F''`-points of `C` with `powMap x = p` after base
change to `F''`, then the induced morphism `Π_m x_m : Spec F'' ⟶ Cⁿ` factors through the
open `Vⁿ = d.openOf ⊆ Cⁿ`.

This is the base-change version of `Work.SymQuot.DivOf.lift_mem_chartOpen`
(`Submission/Work/SymQuot/DivOf/powMapAux.lean`), which treats the case `F'' = F`: the proof
transports the chart along the base change `Spec F'' ⟶ Spec F` and then applies that lemma.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.C1Defs
import Submission.Work.SymQuot.DivOf.powMapAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
namespace Work.SymQuot.DivOf

theorem lift_mem_V {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) {F'' : Type u} [Field F''] [Algebra K F'']
    [Algebra F F''] [IsScalarTower K F F''] (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F'') p) :
    (⊤ : (Work.SpecLin.specOf (K := K) F'').left.Opens) ≤
      ((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F'' ⟶
        Work.SymQuot.prod C.toOver n)).left ⁻¹ᵁ d.openOf := by
  -- The same chart `d`, now regarded as a chart of the point `Sym.powMap C n x` over `F''`.
  let hd' : ChartPt C n (Work.SymQuot.Sym.powMap C n x) :=
    { V := d.V
      isAffineOpen_V := d.isAffineOpen_V
      q := (Work.SpecLin.specOfMap (K := K) (IsScalarTower.toAlgHom K F F'')).left ≫ d.q
      fac := by
        refine Eq.trans (Category.assoc _ _ _) ?_
        refine Eq.trans (congrArg (fun t => Over.Hom.left (Work.SpecLin.specOfMap (K := K)
          (IsScalarTower.toAlgHom K F F'')) ≫ t) d.fac) ?_
        rw [hx, Work.SpecLin.RPt.map, Over.comp_left]
        try rfl }
  have hopen : hd'.openOf = d.openOf := rfl
  rw [hopen]
  exact lift_mem_chartOpen (C := C) (n := n) (F := F'') x hd'

end Work.SymQuot.DivOf
