/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessIndexFive
-/
import Submission.Work.PointlessIndexFive.Main
import Submission.Work.PointlessIndexFive.GoodAut
import Submission.Work.PointlessIndexFive.hasGoodAut_char_two
import Submission.Work.PointlessIndexFive.hasGoodAut_char_three
import Submission.Work.PointlessIndexFive.order_aut_transport_variableChange
import Submission.Work.PointlessIndexFive.short_form_j_ne_hypotheses
import Submission.Work.PointlessIndexFive.nonempty_fiveTorsionCurve
import Submission.Work.PointlessIndexFive.nonempty_fiveTorsionCurve_of_two_three_invertible
import Submission.Work.PointlessIndexFive.Assembly
import Submission.Work.PointlessIndexFive.Model
import Submission.Work.PointlessIndexFive.PL_ne_zero
import Submission.Work.PointlessIndexFive.pointless_iff_not_exists_shift
import Submission.Work.PointlessIndexFive.pointless_iff_toTorsor
import Submission.Work.PointlessIndexFive.ofAdd_cls_pow_eq_one_iff
import Submission.Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff
import Submission.Work.PointlessIndexFive.five_dvd_of_pointless
import Submission.Work.PointlessIndexFive.period_eq_five_of_pointless
import Submission.Work.PointlessIndexFive.pointless_of_shift_mem_ker
import Submission.Work.PointlessIndexFive.pointless_of_galMap_eq
import Submission.Work.PointlessIndexFive.hasPointlessTwist_clarkLacyFive
import Submission.Work.PointlessIndexFive.divisorOfDegree_iff_five_dvd_of_pointless
import Submission.Work.PointlessIndexFive.hasPointlessIndexFiveCurve_of_twistModel
import Submission.Work.PointlessIndexFive.not_hasRatPoint_twistCurveModel
import Submission.Work.PointlessIndexFive.hasRatDivisorOfDegree_iff_twistCurveModel
import Submission.Work.PointlessIndexFive.hasRatDivisorOfDegree_five_twistCurveModel
import Submission.Work.PointlessIndexFive.notIsoJacSq_of_pointless
import Submission.Work.PointlessIndexFive.twistResidual_iff
import Submission.Work.PointlessIndexFive.five_nsmul_mem_shift_range
import Submission.Work.PointlessIndexFive.five_smul_eq_zero_H1
import Submission.Work.PointlessIndexFive.shift_mem_cocycles
import Submission.Work.PointlessIndexFive.finiteType_zeroComponent
import Submission.Work.PointlessIndexFive.exists_zeroComponentRingEquiv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.PointlessIndexFive` — single entry point

The area `Submission/Work/PointlessIndexFive` attacks the residual
`Work.TorsorExistence.HasPointlessIndexFiveCurve 𝕜` — the geometric mountain of the
`TorsorExistence` chapter for Lin–Shinder, *Motivic invariants of birational maps*, Annals of
Math. **199** (1), 2024, Theorem 1.2 (1) (a)–(d).  It splits the residual into a *geometric* half
and an *arithmetic* half, proves everything that follows from them (in particular the paper's
Lemma `lem:torsors`, `Work.Arithmetic.HasLLinkCurve 𝕜`, for the four field classes), and records the
two halves as precisely stated, referenced residuals.

## Import this

`import Submission.Work.PointlessIndexFive.All`

## The residuals (`Defs.lean`)

| name | meaning |
|---|---|
| `CurveModel 𝕜` | the geometric half alone: a scheme over `𝕜` with `Variety`, `IsProper`, `Smooth`, `GeometricallyIntegral` and `topologicalKrullDim = 1` |
| `TwistCurveModel 𝕜 D` | the scheme `(E_L)/G` of a quintic twist `D`, with the Galois-descent bridges `hasPoint_iff`, `divisorOfDegree_iff` |
| `TwistRealization 𝕜` | **geometric residual**: every quintic twist is realized by a curve model |
| `HasPointlessTwist 𝕜` | **arithmetic residual**: some quintic twist has non-vanishing class (Clark–Lacy Thm 1.10 / Lang–Tate Thm 7) |
| `ClarkLacyPointless 𝕜`, `LangTatePointless 𝕜` | the same Prop, named after the source theorem used for the class |
| `HasPointlessIndexFiveCurveOfTwist 𝕜` | witness form: `∃ D, D.Pointless ∧ Nonempty (TwistCurveModel D)` |
| `TwistResidual 𝕜` | both halves with the `DecidableEq` instance quantified (stronger than needed) |
| `TwistResidualSharp 𝕜` | **the sharpest residual, `DecidableEq`-free**: one pointless quintic twist which *is* realized by a curve model |
| `HasPointlessTwistAny 𝕜` | the arithmetic half, `DecidableEq`-free |

## Main results

* `hasPointlessIndexFiveCurve_of_twistModel` (`hasPointlessIndexFiveCurve_of_twistModel.lean`) —
  a curve model of a pointless quintic twist *is* a `PointlessIndexFiveCurve`;
* `hasPointlessIndexFiveCurve_of_twistRealization` (`Main.lean`) — **the main reduction**
  `TwistRealization 𝕜 → HasPointlessTwist 𝕜 → HasPointlessIndexFiveCurve 𝕜`;
* `hasLLinkCurve_of_twistRealization`, `hasLLinkCurve_of_twistResidual` — the paper's
  Lemma `lem:torsors` (`Work.Arithmetic.HasLLinkCurve 𝕜`) from the two halves;
* the four field classes (`Main.lean`):
  `hasPointlessIndexFiveCurve_numberField`, `hasPointlessIndexFiveCurve_functionField_numberField`,
  `hasPointlessIndexFiveCurve_functionField_finite`,
  `hasPointlessIndexFiveCurve_functionField_algClosed`, and the four `hasLLinkCurve_*`;
* `hasPointlessTwist_clarkLacyFive` — the arithmetic residual implies the Arithmetic area's named
  input `Work.Arithmetic.ClarkLacyFive 𝕜`;
* `hasPointlessIndexFiveCurve_iff_curveModel` — the parent residual split *without* `QuinticTwist`:
  a `PointlessIndexFiveCurve 𝕜` is a `CurveModel 𝕜` with no rational point, a degree-`5` divisor and
  all divisor degrees divisible by `5`;
* the `DecidableEq`-free `hasPointlessIndexFiveCurve_of_residualSharp`, `hasLLinkCurve_of_residualSharp`,
  `clarkLacyFive_of_residualSharp`, `conclusions_of_residualSharp` (from `TwistResidualSharp`), the
  corresponding `*_of_residual` from `TwistResidual`, and
  `hasLLinkCurve_residual_{numberField,functionField_numberField,functionField_finite,functionField_algClosed}`.

## Assembling the twist from steps (A) and (B) (`Assembly.lean`)

`Work.TorsorExistence.FiveTorsionCurve` (step (B): `E/𝕜` with `j ≠ 1728` and a rational point of
exact order `5`) together with `Work.TorsorExistence.CyclicExtension 𝕜 5` (step (A)) *is* a
`QuinticTwist 𝕜`: `quinticTwistOf C₅ L`.  Hence the whole remaining content of the arithmetic
residual is the non-vanishing of the class: `hasPointlessTwist_of_pointless_data`,
`hasPointlessTwist_of_numberField`, `clarkLacyPointless_of_exists_pointless`,
`hasPointlessTwistAny_of_exists_pointless`.

## The arithmetic half: criteria and bookkeeping

* `pointless_iff_not_exists_shift` — `Pointless ↔ P ∉ (σ - 1)E(L)`;
* `pointless_of_shift_mem_ker` — **the local-obstruction criterion**: any additive `φ` out of
  `E(L)` with `(σ - 1)E(L) ⊆ ker φ` and `φ P ≠ 0` forces `Pointless`;
* `pointless_of_galMap_eq` — the degenerate case `σ|E(L) = id`;
* `divisorOfDegree_iff_five_dvd_of_pointless` — the index-`5` condition in twist form;
* `notIsoJacSq_of_pointless` — Shinder–Zhang Lemma 2.7 for the twist: `C ≇ Jac²C`;
* `five_smul_eq_zero_H1`, `shift_mem_cocycles` — `H¹(ℤ/5,E(L))` has exponent `5`, and the
  coboundaries lie in the cocycles;
* `five_nsmul_mem_shift_range` — the same orbit-divisor computation for an arbitrary additive
  group `A` with an endomorphism `σ` and `N = 1 + σ + σ² + σ³ + σ⁴`: if `N y = 0` then
  `5y = (σ - 1)z` for an explicit `z`;
* `toTorsor_divisorOfDegree_iff`, `ofAdd_cls_pow_eq_one_iff`, `five_dvd_of_pointless`,
  `period_eq_five_of_pointless`, `pointless_iff_toTorsor`, `PL_ne_zero`;
* `not_hasRatPoint_twistCurveModel`, `hasRatDivisorOfDegree_iff_twistCurveModel`,
  `hasRatDivisorOfDegree_five_twistCurveModel` — the `TwistCurveModel` API used downstream.

## The projective model layer (`Model.lean`)

`projectiveSpace 𝕜 n` (`= Proj 𝕜[X₀,…,Xₙ]`) with `projectiveSpaceToSpec`, `IsProper`,
`LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` (all from Mathlib), `isIntegral_projectiveSpace`
and `variety_projectiveSpace`; and the named gap `ProjectiveModelGap 𝕜 n` (`Smooth`,
`GeometricallyIntegral`, `topologicalKrullDim = n`), together with `finiteType_zeroComponent` and
`exists_zeroComponentRingEquiv` which make `Proj` usable at all.

## End-to-end wiring (`Wire.lean`, not imported by `All`)

`Submission/Work/PointlessIndexFive/Wire.lean` composes `hasLLinkCurve_of_residual` with the
`LLink` area's `Work.LLink.not_gen_of_quadroCubic_*`, giving Theorem 1.2 (1) (a)–(d) from the two
named residuals `TwistResidualSharp 𝕜` and `Work.LLink.CrauderKatzExists 𝕜`:
`not_gen_of_residual_numberField`, `not_gen_of_residual_functionField_numberField`,
`not_gen_of_residual_functionField_finiteField`, `not_gen_of_residual_functionField_algClosed`.

`Wire.lean` also states the same four results directly from **the paper's own data** — a
`FiveTorsionCurve`, a `CyclicExtension 𝕜 5`, `Pointless` for the twist `quinticTwistOf C₅ L`, and a
`TwistCurveModel` for it: `hasLLinkCurve_of_pointless_data` and
`not_gen_of_pointless_data_{numberField,functionField_numberField,functionField_finiteField,functionField_algClosed}`.

See `NOTES.md` for the status of each residual and the roadmap.
-/
