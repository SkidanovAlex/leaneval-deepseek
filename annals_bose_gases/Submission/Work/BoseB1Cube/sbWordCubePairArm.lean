import ChallengeDeps
import Submission.Work.BoseB1Cube.cubeRowsLower
import Submission.Work.BoseFixB1S.b1sCountSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.sbWordCubePairArm` — the **pair channel** as a lower bound for the word

Session 18 of the holder of `Submission/Work/BoseB1Cube/cubeSmallNArb12ExHolds.lean`.

## What this gives

The matched sliding word splits *definitionally* as `sbWordCube = sbKinCube + sbPot` and
`sbPot = pairSum − μ·fibSum` (`Work.BoseFixB1.sbPot_split`), and its kinetic part `sbKinCube` is
**nonnegative for every state** (`Work.BoseFixB1C.sbKinCube_nonneg`: the gap row is a nonnegative
coefficient times a sum of squares, the spectral slot is `tBwordKinInd` of a nonnegative symbol).
⚠ The two declarations `Work.BoseFixB1C.sbKinCube_nonneg` / `sbWordCube_eq_add` exist in *both*
`BoseFixB1C/sbKinCubeFacts.lean` and `BoseFixB1C/trimOffInteriorCube.lean`; only the latter may be
imported here (this module's cone already contains it through `crudeSmallWinLower`).
Hence

    **`pairSum − μ·fibSum ≤ sbWordCube`**    for every (admissible `μ`, `u`, `n`, continuous `Φ`).

This is the **pair arm** of the residual `Work.BoseB1Cube.HoleRowOne`: whenever the state's own pair
channel `pairSum` already covers the demand plus the fibre cost, the row holds *immediately*, with no
use of the flat arm, the gap column or the spectral slot.

## Why it matters for the residual

`HoleRowOne`'s row is `(1/18)·μ·(n/|B|)·∬w₁·∫Φ² ≤ sbWordCube`.  With `D := (1/18)·μ·(n/|B|)·∬w₁·∫Φ²`
this file makes the residual splittable at the *state level*:

* `D + μ·fibSum ≤ pairSum`  ⟹  the row holds (this file);
* otherwise the residual is the **pair-dead** case `pairSum < D + μ·fibSum`.

Since the flat-arm threshold `FlatArm37` only gives `pairSum ≳ 0.27·(M_v/W)·flat`, the pair-dead
residual is *strictly* the smaller one: `D + μ·fibSum` is of the order of `10^{-11}·flat` at FS's
parameters (see `FINDING_cubeSmallNArb12ExHolds_session18.md` §3), i.e. **ten orders of magnitude
smaller** than the flat arm's threshold.  That slack is what makes the geometric estimate
(lossy by a fixed large constant) viable.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The pair arm.**  The matched word dominates its potential slot, and the potential slot is
`pairSum − μ·fibSum` (`Work.BoseFixB1.sbPot_split`), so the state's own pair channel is a lower bound
for the row's right-hand side — with the word's kinetic part as a free bonus. -/
theorem sbWordCube_ge_pairSum_sub_fib {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R εr μ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (hadmr : Work.BoseBoxFix.Adm v εr μ)
    (hRd : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    {n : ℕ} {Φ : X n → ℝ} (hΦc : Continuous Φ) (u : E3) :
    Work.BoseFixB1.pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Φ
      - μ * Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Φ
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := by
  have hsplit := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
    hadmr hΦc u hRd hRχ
  have hdef := Work.BoseFixB1C.sbWordCube_eq_add (v := v) (h := h) (μ := μ) u Φ
  have hnn := Work.BoseFixB1C.sbKinCube_nonneg (v := v) (ε₀ := εr) hadmr u Φ
  linarith only [hsplit, hdef, hnn]

/-- **The pure-state form of the pair arm**: with `D` the item-(1) demand and `fib` the fibre cost,
`D + μ·fib ≤ pairSum` alone implies the row `D ≤ sbWordCube`.  This is the case split the residual
`HoleRowOne` should be run with. -/
theorem sbWordCube_ge_demand_of_pairSum {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R εr μ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (hadmr : Work.BoseBoxFix.Adm v εr μ)
    (hRd : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    {n : ℕ} {Φ : X n → ℝ} (hΦc : Continuous Φ) (u : E3) {D : ℝ}
    (hD : D
      ≤ Work.BoseFixB1.pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Φ
        - μ * Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Φ) :
    D ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ :=
  le_trans hD (sbWordCube_ge_pairSum_sub_fib hv_supp hR hv hvrad hv1 hadmr hRd hRχ hΦc u)

end Work.BoseB1Cube
