/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The divisor of a point of `Symⁿ C` (area SY)

This file assembles the construction of `Work.SpecLin.SymGeom.divOf`:

* `chartPt_exists` (`SymQuot/DivOf/chartPt_exists.lean`): every point `p : Spec F ⟶ Symⁿ C` lies
  in a chart `Spec Γ(Cⁿ,Vⁿ)^{S_n}` for some affine open `V ⊆ C`;
* `chartIdeal` (`SymQuot/DivOf/IdealData.lean`): the ideal of `Γ(C,V)` of regular functions
  vanishing on the divisor of `p`, and its base change `baseChangedIdeal F d` to the affine open
  `bcOpens F V ⊆ C_F`;
* `divisorOfIdeal` (`SymQuot/DivOf/DivisorOfIdeal.lean`): the divisor `Σ_z v_z(J) [z]` cut out by
  an ideal of the affine ring of an affine open of a curve.

Here we put them together: `divOfChart` is the divisor of a point of `Symⁿ C` together with a
chart containing it, and `divOf` is the divisor of the point (using the chart supplied by
`chartPt_exists_nonempty`).
-/
import Submission.Work.SymQuot.DivOf.IdealData
import Submission.Work.SymQuot.DivOf.CharIdeal
import Submission.Work.SymQuot.DivOf.CharIdealGenDefs
import Submission.Work.SymQuot.DivOf.DivisorOfIdeal
import Submission.Work.SymQuot.DivOf.chartPt_exists
import Submission.Work.SymQuot.DivOf.exists_chartPt_nonempty

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

/-- **The divisor of a point of `Symⁿ C` in a chart**: for a chart `d` of `p`, the divisor of the
multiplicity-sensitive ideal `charIdeal F d ⊆ Γ(C_F, bcOpens F V)` (see
`Submission/Work/SymQuot/DivOf/CharIdeal.lean` and the note at the end of `NOTES.md` for why
the naive ideal `baseChangedIdeal F d`, whose carrier is `{b | χ_b = T^n}`, is *not* the ideal
of the divisor). -/
noncomputable def divOfChart {C : Curve K} {n : ℕ} [NeZero n] [CurveAffineCover C]
    (F : Type u) [Field F] [Algebra K F] {p : Work.SpecLin.FPt (Sym C n) F}
    (d : ChartPt C n p) [Nonempty d.V] : (C.baseChange F).Div :=
  @divisorOfIdeal F _ (C.baseChange F) (C.bcOpens F d.V) (Work.CurveBasics.Curve.bcOpens_nonempty C F d.V)
    (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F d.V d.isAffineOpen_V)
    (isDedekindDomain_sections (C := C.baseChange F)
      (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F d.V d.isAffineOpen_V))
    (charIdealGen F d)

/-- The defining equation of `divOfChart`. -/
theorem divOfChart_def {C : Curve K} {n : ℕ} [NeZero n] [CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F] {p : Work.SpecLin.FPt (Sym C n) F}
    (d : ChartPt C n p) [Nonempty d.V] :
    divOfChart F d =
      @divisorOfIdeal F _ (C.baseChange F) (C.bcOpens F d.V) (Work.CurveBasics.Curve.bcOpens_nonempty C F d.V)
        (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F d.V d.isAffineOpen_V)
        (isDedekindDomain_sections (C := C.baseChange F)
          (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F d.V d.isAffineOpen_V))
        (charIdealGen F d) := rfl

/-- **The divisor of a point of `Symⁿ C` is effective.** -/
theorem divOfChart_isEffective {C : Curve K} {n : ℕ} [NeZero n] [CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F] {p : Work.SpecLin.FPt (Sym C n) F}
    (d : ChartPt C n p) [Nonempty d.V] : (divOfChart F d).IsEffective := by
  have hW : IsAffineOpen (C.bcOpens F d.V) :=
    Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F d.V d.isAffineOpen_V
  haveI : IsDedekindDomain Γ((C.baseChange F).left, C.bcOpens F d.V) :=
    isDedekindDomain_sections (C := C.baseChange F) hW
  rw [divOfChart_def]
  exact divisorOfIdeal_isEffective (C.baseChange F) (C.bcOpens F d.V) hW (charIdealGen F d)

/-- **The divisor of a point of `Symⁿ C`**: `Work.SpecLin.SymGeom.divOf` (the point of the chart
chosen by `exists_chartPt_nonempty`). -/
noncomputable def divOf {C : Curve K} {n : ℕ} [NeZero n] [CurveAffineCover C]
    (F : Type u) [Field F] [Algebra K F] (p : Work.SpecLin.FPt (Sym C n) F) :
    (C.baseChange F).Div :=
  haveI : Nonempty (Classical.choose (exists_chartPt_nonempty (C := C) (n := n) p)).V :=
    Classical.choose_spec (exists_chartPt_nonempty (C := C) (n := n) p)
  divOfChart F (Classical.choose (exists_chartPt_nonempty (C := C) (n := n) p))

/-- **The divisor of a point of `Symⁿ C` is effective.** -/
theorem divOf_isEffective {C : Curve K} {n : ℕ} [NeZero n] [CurveAffineCover C]
    {F : Type u} [Field F] [Algebra K F] (p : Work.SpecLin.FPt (Sym C n) F) :
    (divOf F p).IsEffective := by
  haveI : Nonempty (Classical.choose (exists_chartPt_nonempty (C := C) (n := n) p)).V :=
    Classical.choose_spec (exists_chartPt_nonempty (C := C) (n := n) p)
  rw [divOf]
  exact divOfChart_isEffective (Classical.choose (exists_chartPt_nonempty (C := C) (n := n) p))

end Work.SymQuot.DivOf
