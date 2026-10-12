import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixKin.FSRegime` — the coupled kinetic regime (the `b`-clash repair)

Subproject `Submission/Work/BoseFixKin/` (the D2 / `b`-clash repair of the bose box chain,
design `BOSE_BCLASH_LEAD.md`).  This file fixes the vocabulary of the chapter; every other
module of the chapter imports it.

## Why a new regime

`Work.BoseKinLoc.KinRegime c₀` bounds **all four** of `d, s, ε_T, b` by the *same* `c₀`, so any
`KineticLocalisation c₀` with `c₀ ≥ bValue = 1/16` forces FS `lem:LocKinEn` to hold at the
corner `s = ε_T = 1/16`.  Two obstructions live exactly there and nowhere else:

* the `χ`-constant `C` enters the budget as `C (2s)³ ‖p‖²`, so at `s = 1/16` it would need the
  unprovable numeral bound `C ≤ 128`; and
* the crude, *already proved* momentum bound `Work.BoseKinLoc.MomBound` only holds for
  `b ≤ b₀` with an **existential** `b₀ ≪ 1/16` (its `C_sym` is `≥ 4096`).

The repair is to **decouple `b` from `c₀`**: keep `bValue = 1/16` fixed, keep `s, ε_T` small,
and add the single *coupling* condition `ε_T · s ≤ c₀ · d`.  On this regime every `χ`-dependent
constant multiplies a small parameter, and `MomBound`'s existential `b₀` only produces a
factor `K = 1/(16 b₀)` that small `ε_T` absorbs.  The coupling is free at FS's parameters:
`ε_T s / d = X^{23/4 + 1 - 6} = X^{3/4} → 0`.

## Contents

| name | role |
|---|---|
| `KinRegimeFS` | the coupled regime (FS's parameters satisfy it, `Params.kinRegimeFS_of_params`) |
| `KineticLocalisationFS` | FS `lem:LocKinEn` on that regime |
| `cFS` | the *explicit* regime constant of the coupled budget `K`, `C` |

All constants here are absolute.  Nothing in this subproject edits the delivered
`Submission/Work/BoseKinLoc/` or `Submission/Work/BoseFixGlue/` chapters: they are imported.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixKin

/-- **FS's *coupled* kinetic regime.**  `b` is only bounded by the fixed `1/16` (FS's
`con:b`, which is not an adjustable constant), while `s` and `ε_T` are bounded by the
regime constant `c₀` and are coupled to `d` through `ε_T · s ≤ c₀ · d`.  At FS's parameters
(`d = X⁶`, `s = X`, `ε_T = X^{23/4}`) the coupling reads `X^{3/4} ≤ c₀`, so it holds for all
small enough diluteness. -/
def KinRegimeFS (c₀ ℓ d s εT b : ℝ) : Prop :=
  0 < ℓ ∧ 0 < d ∧ d ≤ 1 ∧ 0 < s ∧ s ≤ c₀ ∧ 0 < εT ∧ εT ≤ c₀ ∧ εT * s ≤ c₀ * d ∧
    0 < b ∧ b ≤ 1 / 16

/-- **FS `lem:LocKinEn` on the coupled regime**: `∫_u 𝒯_u du ≤ −Δ` for every smooth compactly
supported one-body state, at every parameter block satisfying `KinRegimeFS c₀`. -/
def KineticLocalisationFS (c₀ : ℝ) : Prop :=
  ∀ ℓ d s εT b : ℝ, KinRegimeFS c₀ ℓ d s εT b → ∀ ψ : ℝ³ → ℝ,
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun u : ℝ³ => Work.BoseKinLoc.fsT ℓ d s εT b u ψ) →
        ∫ u : ℝ³, Work.BoseKinLoc.fsT ℓ d s εT b u ψ ≤ Work.BSKinetic.dSpace ψ

/-- **The explicit regime constant of the coupled budget, given the momentum factor `K` and
the `T'`-constant `C`.**  `min (1/4) (1/(64 (K + C + 1)))`: small enough that
`(1+K)/2 · ε_T ≤ 1/128`, `8 C s³ ≤ 7/8` and `(1+K) s²/2 ≤ 7/48` all hold, which are the
three arithmetic facts the three-region budget uses. -/
def cFS (K C : ℝ) : ℝ := min (1 / 4) (1 / (64 * (K + C + 1)))

end Work.BoseFixKin
