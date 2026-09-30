/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Definitions for the hub lemma C1 (area SY, `divOf`)

The hub lemma C1 of `Submission/Work/NOTES_LEAD_jacobian_divof.md` §2 compares the divisor ideal
of a point of `Symⁿ C` with the product of the maximal ideals of the lifted points, after
extending scalars from `F` to a field extension `F''`.  This file contains the definitions used
by that comparison:

* `bcSec` — the pullback of sections `Γ(C_F, V_F) → Γ(C_{F''}, V_{F''})` along the tower morphism
  `C_{F''} ⟶ C_F` (whose preimage of `V_F` is `V_{F''}`, `towerHom_preimage_bcOpens`);
* `ChartPt.valAtLift` — the value of a chart section at the `m`-th lifted point `x m`, over the
  extension field `F''`;
* `prodPtPlaceIdeal` — the ideal `∏_m m_{x_m}` cut out by the lifted points.
-/
import Submission.Work.SymQuot.DivOf.TowerSquare
import Submission.Work.SymQuot.DivOf.CharIdealGenDefs
import Submission.Work.SymQuot.DivOf.towerHom_preimage_bcOpens
import Submission.Work.SpecLin.Points.Basic

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

variable {K : Type u} [Field K] {C : Curve K}

/-- **Pullback of sections along the tower `C_{F''} ⟶ C_F`**, restricted to the base-changed
open `V_F` and `V_{F''}`: `Γ(C_F, V_F) →+* Γ(C_{F''}, V_{F''})`. -/
noncomputable def bcSec (F F'' : Type u) [Field F] [Field F''] [Algebra K F] [Algebra K F'']
    [Algebra F F''] [IsScalarTower K F F''] (V : C.left.Opens) :
    Γ((C.baseChange F).left, C.bcOpens F V) →+*
      Γ((C.baseChange F'').left, C.bcOpens F'' V) :=
  ((BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F'')).appLE (C.bcOpens F V)
    (C.bcOpens F'' V)
    (le_of_eq (towerHom_preimage_bcOpens (C := C) F F'' V).symm)).hom

variable {n : ℕ} [NeZero n] [CurveAffineCover C]

/-- **The value of a chart section at the `m`-th lifted point**, over the field extension `F''`:
the composite of the evaluation map `Γ(Cⁿ, Vⁿ) →+* F''` of the lift with the `m`-th coordinate
pullback. -/
noncomputable def valAtLift {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Sym C n) F} (d : ChartPt C n p)
    {F'' : Type u} [Field F''] [Algebra K F'']
    (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (h : ⊤ ≤ ((Limits.Pi.lift x :
      Work.SpecLin.specOf (K := K) F'' ⟶ prod C.toOver n)).left ⁻¹ᵁ d.openOf)
    (m : Fin n) : Γ(C.left, d.V) →+* F'' :=
  (d.evalMap x h).comp (coordPullbackAt C n d.V m)

@[simp]
theorem valAtLift_apply {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Sym C n) F} (d : ChartPt C n p)
    {F'' : Type u} [Field F''] [Algebra K F'']
    (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (h : ⊤ ≤ ((Limits.Pi.lift x :
      Work.SpecLin.specOf (K := K) F'' ⟶ prod C.toOver n)).left ⁻¹ᵁ d.openOf)
    (m : Fin n) (b : Γ(C.left, d.V)) :
    valAtLift d x h m b = d.evalMap x h (coordPullbackAt C n d.V m b) := rfl

/-- **The product of the maximal ideals of the lifted points** `∏_m m_{x_m}`: the ideal of
`Γ(C_{F''}, V_{F''})` cut out by the divisor `Σ_m [x_m]`. -/
noncomputable def prodPtPlaceIdeal {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Sym C n) F} (d : ChartPt C n p)
    {F'' : Type u} [Field F''] [Algebra K F''] (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (hmem : ∀ m, (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' d.V) :
    Ideal Γ((C.baseChange F'').left, C.bcOpens F'' d.V) :=
  ∏ m, placeIdeal (C.baseChange F'') (C.bcOpens F'' d.V) (Work.SpecLin.ptPlace (x m)) (hmem m)

end Work.SymQuot.DivOf
