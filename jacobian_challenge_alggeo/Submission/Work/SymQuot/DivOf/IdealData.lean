/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The ideal of a point of `Symⁿ C` and its base change (area SY, `divOf`)

For a point `p : Spec F ⟶ Symⁿ C` together with a `ChartPt` `d` (an affine open `V ⊆ C` whose
chart contains `p`, `Work.SymQuot.DivOf.ChartPt`), the file `DivOf/ChartPt.lean` constructed the
set `d.localIdealSet ⊆ Γ(C,V)` of regular functions on `V` vanishing on the divisor of `p`, and
`DivOf/localIdealSet_isIdeal.lean` proved that it is the carrier of an ideal.  This file names
that ideal (`chartIdeal`) and its base change to `C_F`

`J := chartIdeal d · Γ(C_F, (C.bcOpens F V))`,

the ideal of `Γ(C_F, bcOpens F V)` from which the divisor `divOf p` is extracted
(`D(z) = placeOrder J z hz`, see `DivOf/AffineCurve.lean`).
-/
import Submission.Work.SymQuot.DivOf.ChartPt
import Submission.Work.SymQuot.DivOf.localIdealSet_isIdeal
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal
import Submission.Work.SymQuot.DivOf.isDedekindDomain_sections

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

variable {K : Type u} [Field K]

/-- **The ideal of a point of `Symⁿ C` in a chart**: the regular functions on `V` vanishing on
the divisor of the point (the ideal whose carrier is `ChartPt.localIdealSet`). -/
noncomputable def chartIdeal {C : Curve K} {n : ℕ} [NeZero n] [CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F] {p : Work.SpecLin.FPt (Sym C n) F}
    (d : ChartPt C n p) : Ideal Γ(C.left, d.V) :=
  Classical.choose (localIdealSet_isIdeal d)

/-- The defining property of `chartIdeal`. -/
theorem chartIdeal_coe {C : Curve K} {n : ℕ} [NeZero n] [CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F] {p : Work.SpecLin.FPt (Sym C n) F}
    (d : ChartPt C n p) :
    ((chartIdeal d : Ideal Γ(C.left, d.V)) : Set Γ(C.left, d.V)) = d.localIdealSet :=
  Classical.choose_spec (localIdealSet_isIdeal d)

/-- **The base change of the *reduced* ideal of a point of `Symⁿ C` to `C_F`**.

WARNING: this is NOT the ideal of the divisor of the point, except when the divisor is reduced.
Its carrier consists of the sections vanishing at every point of the support (the *reduced*
divisor), because `b ∈ localIdealSet ↔ ∀ m, b(x_m) = 0` and an intersection of maximal ideals
does not see multiplicities.  The correct, multiplicity-sensitive ideal is
`Work.SymQuot.DivOf.charIdeal` (see `DivOf/CharIdeal.lean` and the note at the end of
`NOTES.md`), which is what `divOf` uses. -/
noncomputable def baseChangedIdeal {C : Curve K} {n : ℕ} [NeZero n] [CurveAffineCover C]
    (F : Type u) [Field F] [Algebra K F] {p : Work.SpecLin.FPt (Sym C n) F}
    (d : ChartPt C n p) : Ideal Γ((C.baseChange F).left, C.bcOpens F d.V) :=
  Ideal.map (((Curve.baseChangeFst C F).app d.V).hom) (chartIdeal d)

end Work.SymQuot.DivOf
