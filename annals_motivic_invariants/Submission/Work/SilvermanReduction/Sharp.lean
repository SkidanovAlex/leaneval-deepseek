/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Submission.Work.SilvermanReduction.Residual
import Submission.Work.SilvermanReduction.TateCurve
import Submission.Work.SilvermanReduction.hasGoodReduction_baseChange

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The class-(a) residual with the marker discharged

`LocalModelData` (in `Conditional.lean`) lists the four hypotheses of the class-(a) local model:
the discrete valuation ring `R` inside the top field `L = D.ext.L`, good reduction of `D.E` at `R`,
the two Galois conditions `PreservesValuation`/`TrivialOnResidue` for `σ = D.ext.gen`, and the
non-vanishing of the reduction of the marker `D.PL`.

The last of these is not an arithmetic hypothesis: when the marked point of the twist is `(0,0)`
— the Tate normal form of the number-field class — the marker `D.PL` is the base change of `(0,0)`
to `L`, and the reduction of an integral point is an affine point, never the origin
(`Marker.redPoint_PL_ne_zero_of_eq_some_zero`, whose input is `redPoint_some_zero_zero_ne_zero`).

This file states the class-(a) residual in the form in which the marker is already discharged, so
that what remains is *only* the place theory of the cyclotomic quintic field — see `NOTES.md` §4.

## Main results

* `hasReductionPlace_of_localModelData_of_PL_some_zero` — the place datum, with the marker
  hypothesis replaced by `D.PL = (0,0)`.
* `numberFieldResidual_of_PL_some_zero`, `hasPointlessTwist_of_PL_some_zero` — the class-(a)
  residual and the arithmetic half of Theorem 1.2 (a), in that form.
* `TatePlaceData`, `numberFieldReduction_of_tatePlaceData` — the same for the pinned curve
  `TateCurve.tateFiveTorsionCurve` (the Tate normal form with `c = 1`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

/-- **The class-(a) place datum, with the marker discharged.**  `D` is a quintic twist whose
marked point is `(0,0)` (`hPL`), `R` is a local model of a place of `D.ext.L` at which `D.E` has
good reduction, `σ = D.ext.gen` preserves the valuation and acts trivially on the residue field.
Then the reduction gives the place datum of the chain. -/
theorem hasReductionPlace_of_localModelData_of_PL_some_zero {𝕜 : Type} [Field 𝕜]
    [DecidableEq 𝕜] (D : Work.PointlessTwist.QuinticTwist 𝕜)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R D.ext.L] [IsFractionRing R D.ext.L]
    [DecidableEq (ResidueField R)]
    [hW : (D.E.baseChange D.ext.L).HasGoodReduction R]
    (hσ : PreservesValuation R (D.ext.gen : D.ext.L →+* D.ext.L))
    (hτ : TrivialOnResidue R (D.ext.gen : D.ext.L →+* D.ext.L))
    {h' : Nonsingular (D.E.baseChange D.ext.L) 0 0}
    (hPL : D.PL = WeierstrassCurve.Affine.Point.some 0 0 h') :
    Work.PointlessTwist.HasReductionPlace D :=
  hasReductionPlace_of_localModelData D
    ⟨R, hσ, hτ, redPoint_PL_ne_zero_of_eq_some_zero D hPL R⟩

/-- **The class-(a) residual of the chain, with the marker discharged.** -/
theorem numberFieldResidual_of_PL_some_zero {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] [NumberField 𝕜]
    (C₅ : Work.PointlessTwist.FiveTorsionCurve 𝕜)
    (L : Work.PointlessTwist.CyclicExtension 𝕜 5)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R (Work.PointlessTwist.twistOf C₅ L).ext.L]
    [IsFractionRing R (Work.PointlessTwist.twistOf C₅ L).ext.L]
    [DecidableEq (ResidueField R)]
    [hW : ((Work.PointlessTwist.twistOf C₅ L).E.baseChange
      (Work.PointlessTwist.twistOf C₅ L).ext.L).HasGoodReduction R]
    (hσ : PreservesValuation R ((Work.PointlessTwist.twistOf C₅ L).ext.gen :
      (Work.PointlessTwist.twistOf C₅ L).ext.L →+* (Work.PointlessTwist.twistOf C₅ L).ext.L))
    (hτ : TrivialOnResidue R ((Work.PointlessTwist.twistOf C₅ L).ext.gen :
      (Work.PointlessTwist.twistOf C₅ L).ext.L →+* (Work.PointlessTwist.twistOf C₅ L).ext.L))
    {h' : Nonsingular ((Work.PointlessTwist.twistOf C₅ L).E.baseChange
      (Work.PointlessTwist.twistOf C₅ L).ext.L) 0 0}
    (hPL : (Work.PointlessTwist.twistOf C₅ L).PL
      = WeierstrassCurve.Affine.Point.some 0 0 h') :
    Work.PointlessTwist.NumberFieldResidual 𝕜 :=
  ⟨C₅, L, hasReductionPlace_of_localModelData_of_PL_some_zero _ R hσ hτ hPL⟩

/-- **The arithmetic half of the paper's Theorem 1.2 (a), with the marker discharged.** -/
theorem hasPointlessTwist_of_PL_some_zero {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] [NumberField 𝕜]
    (C₅ : Work.PointlessTwist.FiveTorsionCurve 𝕜)
    (L : Work.PointlessTwist.CyclicExtension 𝕜 5)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R (Work.PointlessTwist.twistOf C₅ L).ext.L]
    [IsFractionRing R (Work.PointlessTwist.twistOf C₅ L).ext.L]
    [DecidableEq (ResidueField R)]
    [hW : ((Work.PointlessTwist.twistOf C₅ L).E.baseChange
      (Work.PointlessTwist.twistOf C₅ L).ext.L).HasGoodReduction R]
    (hσ : PreservesValuation R ((Work.PointlessTwist.twistOf C₅ L).ext.gen :
      (Work.PointlessTwist.twistOf C₅ L).ext.L →+* (Work.PointlessTwist.twistOf C₅ L).ext.L))
    (hτ : TrivialOnResidue R ((Work.PointlessTwist.twistOf C₅ L).ext.gen :
      (Work.PointlessTwist.twistOf C₅ L).ext.L →+* (Work.PointlessTwist.twistOf C₅ L).ext.L))
    {h' : Nonsingular ((Work.PointlessTwist.twistOf C₅ L).E.baseChange
      (Work.PointlessTwist.twistOf C₅ L).ext.L) 0 0}
    (hPL : (Work.PointlessTwist.twistOf C₅ L).PL
      = WeierstrassCurve.Affine.Point.some 0 0 h') :
    Work.PointlessTwist.HasPointlessTwist 𝕜 :=
  Work.PointlessTwist.hasPointlessTwist_of_numberFieldResidual
    (numberFieldResidual_of_PL_some_zero C₅ L R hσ hτ hPL)

/-- **The class-(a) residual at `ℚ`, with the curve pinned to the Tate normal form with `c = 1`**
(`TateCurve.tateFiveTorsionCurve`) and the marker discharged.  What remains is the field theory of
the place: the cyclic quintic field `L` and its local model. -/
theorem numberFieldResidual_of_tatePlaceData (L : Work.PointlessTwist.CyclicExtension ℚ 5)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R (Work.PointlessTwist.twistOf tateFiveTorsionCurve L).ext.L]
    [IsFractionRing R (Work.PointlessTwist.twistOf tateFiveTorsionCurve L).ext.L]
    [DecidableEq (ResidueField R)]
    [hW : ((Work.PointlessTwist.twistOf tateFiveTorsionCurve L).E.baseChange
      (Work.PointlessTwist.twistOf tateFiveTorsionCurve L).ext.L).HasGoodReduction R]
    (hσ : PreservesValuation R ((Work.PointlessTwist.twistOf tateFiveTorsionCurve L).ext.gen :
      (Work.PointlessTwist.twistOf tateFiveTorsionCurve L).ext.L →+*
        (Work.PointlessTwist.twistOf tateFiveTorsionCurve L).ext.L))
    (hτ : TrivialOnResidue R ((Work.PointlessTwist.twistOf tateFiveTorsionCurve L).ext.gen :
      (Work.PointlessTwist.twistOf tateFiveTorsionCurve L).ext.L →+*
        (Work.PointlessTwist.twistOf tateFiveTorsionCurve L).ext.L))
    {h' : Nonsingular ((Work.PointlessTwist.twistOf tateFiveTorsionCurve L).E.baseChange
      (Work.PointlessTwist.twistOf tateFiveTorsionCurve L).ext.L) 0 0}
    (hPL : (Work.PointlessTwist.twistOf tateFiveTorsionCurve L).PL
      = WeierstrassCurve.Affine.Point.some 0 0 h') :
    Work.PointlessTwist.NumberFieldResidual ℚ :=
  numberFieldResidual_of_PL_some_zero tateFiveTorsionCurve L R hσ hτ hPL

end

end Work.SilvermanReduction
