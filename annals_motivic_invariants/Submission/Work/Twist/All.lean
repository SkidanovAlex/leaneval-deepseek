/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Twist
-/
import Submission.Work.Twist.Defs
import Submission.Work.Twist.Assembly
import Submission.Work.Twist.ExtIsoTransport
import Submission.Work.Twist.ProjModel
import Submission.Work.Twist.away_chart_mvPolynomial
import Submission.Work.Twist.away_chart_mvPolynomial_X
import Submission.Work.Twist.chartAwayMapInv_comp_chartAwayMap
import Submission.Work.Twist.chartAwayMap_comp_chartAwayMapInv
import Submission.Work.Twist.chartAwayMap_fromZeroRingHom
import Submission.Work.Twist.chartDhom_eq_zero
import Submission.Work.Twist.curveModel_projectiveSpace_one
import Submission.Work.Twist.exists_chart_away_X_zero_compat
import Submission.Work.Twist.exists_shift_eq_nsmul_iff_five_dvd
import Submission.Work.Twist.exists_shift_pow_iff
import Submission.Work.Twist.galMapPow_eq_add_nsmul
import Submission.Work.Twist.hasLocalObstruction_of_pointless
import Submission.Work.Twist.hasPointlessTwistByObstruction_iff
import Submission.Work.Twist.hasPointlessTwist_iff_exists_pointless
import Submission.Work.Twist.isIntegral_projectiveSpace
import Submission.Work.Twist.localObstruction_of_galTrivial
import Submission.Work.Twist.nsmul_cls_eq_zero_iff
import Submission.Work.Twist.pointless_iff_of_extIso
import Submission.Work.Twist.pointless_of_galMap_quot_five
import Submission.Work.Twist.pointless_pow_iff
import Submission.Work.Twist.quot_mk_eq_zero_iff
import Submission.Work.Twist.realizationOf_iff_of_extIso
import Submission.Work.Twist.ringHom_smooth_fromZeroRingHom_X_iff
import Submission.Work.Twist.shift_eq_nsmul_eq_zero
import Submission.Work.Twist.smooth_projectiveSpaceToSpec
import Submission.Work.Twist.stdGradingChart
import Submission.Work.Twist.topologicalKrullDim_le_iSup_of_isOpenCover
import Submission.Work.Twist.topologicalKrullDim_projectiveSpace
import Submission.Work.Twist.torsorDivisorOfDegreePow_iff
import Submission.Work.Twist.torsorHasPointPow_iff
import Submission.Work.Twist.twistBridges_one_iff
import Submission.Work.Twist.twistCurveModelOfPow
import Submission.Work.Twist.twistCurveModel_bridges

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Twist` — single entry point

The area `Submission/Work/Twist` attacks the two **named residuals** of
`Submission/Work/PointlessIndexFive` for Lin–Shinder, *Motivic invariants of birational maps*,
Annals of Math. **199** (1), 2024, Theorem 1.2 (1) (a)–(d):

* `TwistRealization 𝕜` — **geometric**: every quintic twist is realized by a curve model
  (`TwistCurveModel`);
* `HasPointlessTwist 𝕜` — **arithmetic**: some quintic twist has non-vanishing class in
  `H¹(ℤ/5, E(L)) = ker N/(σ - 1)E(L)`.

## Import this

`import Submission.Work.Twist.All`

## The residual on the paper's own data (`Defs.lean`)

| name | meaning |
|---|---|
| `PointlessOf C₅ L` | the twist of the `FiveTorsionCurve` `C₅` by the cyclic quintic extension `L` is pointless |
| `RealizationOf C₅ L` | that twist is realized by a `TwistCurveModel` |
| `PointlessTwistData 𝕜` | **the residual of this area**: `∃ C₅ L, PointlessOf C₅ L ∧ RealizationOf C₅ L` |
| `PointlessTwistDataAny 𝕜` | the same with the `DecidableEq 𝕜` artefact quantified |
| `ExtIso L L'` | an isomorphism of cyclic quintic extensions matching the chosen generators |
| `LocalObstruction D` | the datum in which the paper decides `cls ≠ 0`: an additive `φ` out of `E(L)` killing `(σ - 1)E(L)` and not killing `P` (reduction at a place) |
| `QuinticTwist.galMapPow k`, `PointlessPow`, `TorsorHasPointPow`, `TorsorDivisorOfDegreePow`, `TwistBridges D C k` | the same notions written with the generator `σ ^ k` |

## Main results

* **The residual is exactly the parent chapter's residual**: `pointlessTwistData_iff`
  (`= HasPointlessIndexFiveCurveOfTwist`), `pointlessTwistDataAny_iff_residualSharp`
  (`= TwistResidualSharp`);
* **The composition**: `hasPointlessIndexFiveCurve_of_pointlessData`,
  `hasPointlessIndexFiveCurve_of_pointlessTwistData`, `conclusions_of_pointlessTwistData`
  (`HasPointlessIndexFiveCurve 𝕜 ∧ HasLLinkCurve 𝕜 ∧ ClarkLacyFive 𝕜`), and the four field classes
  `hasLLinkCurve_pointlessTwistDataAny_{numberField,functionField_numberField,functionField_finite,functionField_algClosed}`;
* **Well-posedness in the generator**: the orbit identity `galMapPow_eq_add_nsmul`, the criterion
  `exists_shift_pow_iff`, and the transports `pointless_pow_iff`, `torsorHasPointPow_iff`,
  `torsorDivisorOfDegreePow_iff`, `twistBridges_one_iff`, `twistCurveModel_bridges`,
  `twistCurveModelOfPow`;
* **Well-posedness in the extension**: `pointless_iff_of_extIso`, `realizationOf_iff_of_extIso`;
* **The element-level dictionary**: `quot_mk_eq_zero_iff`, `nsmul_cls_eq_zero_iff`,
  `exists_shift_eq_nsmul_iff_five_dvd` (index `5`), `shift_eq_nsmul_eq_zero`;
* **The arithmetic criteria**: `localObstruction_pointless`, `hasPointlessTwist_of_obstruction`,
  `hasPointlessTwistByObstruction_iff`, `hasLocalObstruction_of_pointless`,
  `localObstruction_of_galTrivial`, `pointless_of_galMap_quot_five`,
  `hasPointlessTwist_iff_exists_pointless`;
* **Assembly of a twist model**: `twistCurveModelOf`;
* **The projective model layer** (which Area 1 consumes): the chart-ring computation
  `away_chart_mvPolynomial` / `away_chart_mvPolynomial_X` (`A⁰_{X_i} ≅ 𝕜[y₁,…,yₙ]`, the algebra
  input that was missing from Mathlib, via `chartDhom`/`chartPsi`),
  `topologicalKrullDim_projectiveSpace` (`dim ℙⁿ = n`), `smooth_projectiveSpaceToSpec` (`ℙⁿ` smooth
  over `𝕜`), `isIntegral_projectiveSpace` (with the reusable
  `irreducibleSpace_proj_of_isDomain`, `isReduced_proj_of_isReduced`), and in `ProjModel`:
  `projectiveModelGap_iff` (the *only* remaining conjunct of `ProjectiveModelGap 𝕜 n` is
  `GeometricallyIntegral`), `variety_projectiveSpace_uncond` (`Variety 𝕜 (ℙⁿ)` unconditionally) and
  `curveModel_projectiveSpace_one_of_geometricallyIntegral`.

See `NOTES.md` for the status of the two residuals, the explicit model of the twist
(the Pfaffian elliptic quintic `Gr(2,5) ∩ ℙ⁴`), the per-class arithmetic, and the roadmap.
-/
