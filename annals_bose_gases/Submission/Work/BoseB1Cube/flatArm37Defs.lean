import ChallengeDeps
import Submission.Work.BoseB1Cube.coreSmallA
import Submission.Work.BoseB1Cube.cubeRowsLower
import Submission.Work.BoseB1Cube.payPortLedger2
import Submission.Work.BoseB1Cube.sbWordCube_eq_zero_of_bI_eq_zero
import Submission.Work.BoseB1Cube.wSmallPairGlobalVanish
import Submission.Work.BoseB1Cube.windowShiftDichotomy
import Submission.Work.BoseFixB1S.b1sCountSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseB1Cube/flatArm37Defs` — the **sharper flat-arm condition** `FlatArm37`

`Work.BoseFixB1B.flatArmCond` is the PROVED dichotomy `boxPairCount ≤ 4·(V²/∬w)·pairSum`, whose
flat half yields only `pairSum ≥ ¼·X` with `X = (M_v/V²)·boxPairCount`.  On the *small window* at
`Cn = 4` that is short of the target rows by exactly the factor `19/18` (`¼X = 4μ²M_v` against a
requirement `(19/18)·μ²W`, i.e. `M_v ≥ (19/18)W`, which fails for spread-out weak potentials where
`M_v/W = ∫v/(8πa) → 1`).

`FlatArm37` is the same condition with the constant `4` replaced by `37/10`; it yields
`pairSum ≥ (10/37)·X`, and `(10/37)X = 4.32μ²M_v ≥ (19/18)μ²W` for `M_v ≥ 0.977W` — in particular
for every `v` with `M_v ≥ W` (which is PROVED: `boxM2_sub_boxM1_nonneg_slidingB1`).  So the rows
close on `FlatArm37` at the *existing* `Cn = 4` architecture.  See
`FINDING_cubeSmallNArb12ExHolds_session13.md` §3.

## ⚠ IMPORT-CONE REQUIREMENT for any proof of `cubeSmallWinFlatArm37*`

The holder `Submission/Work/BoseB1Cube/cubeSmallNArb12ExHolds.lean` must be able to *import* the
lemma and use it to fill its `sorry`, and that file already contains
`Submission/Work/BoseB1Cube/rowsOfSmallWindow.lean` in its cone.  Therefore the proof of
`cubeSmallWinFlatArm37` (session 13, PROVED but **cyclic**) — which imports
`Submission/Work/BoseB1Cube/flatArm37RowOneGood.lean` → `cubeFlatArm_holds.lean` →
`cubeCrudeBand_holds.lean` → … → `rowsOfSmallWindow.lean` → the holder — **cannot be consumed
inside the holder**.  Any *usable* version must be proved with a **holder-free import cone**: the
minimal cone is `Mathlib`, `BoseB1Cube/cubeWinRowsNearFlat`, `BoseB1Cube/crudeSmallWinLower`,
`BoseB1Cube/flatArm37Defs`, `BoseFixB1B/BandCountCapDefs`, `BoseB1B/…` primitives; do **not** import
`cubeFlatArm_holds`, `cubeCrudeBand_holds`, `nomRowSqWindowRow`, `rowsOfSmallWindow`,
`sbWordCube_ge_crudeSmallWin`, or anything that (transitively) imports the holder.  (Same pattern as
session 10's `cubeRowsCoreLower.lean` / `cubeWinRowsAssemblyLower.lean`.)
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
set_option maxHeartbeats 4000000

/-- **The sharper flat-arm condition** — `Work.BoseFixB1B.flatArmCond` with the constant `4`
replaced by `37/10`:
`boxPairCount ≤ (37/10)·(V²/∬w)·pairSum`, equivalently `pairSum ≥ (10/37)·(M_v/V²)·boxPairCount`.
It is stronger than `flatArmCond`, so `flatArmCond ⟹ FlatArm37` and the *complement* of
`FlatArm37` is contained in the hole arm of the corpus's dichotomy. -/
def FlatArm37 (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ)
    (Φ : X n → ℝ) (u : E3) : Prop :=
  Work.BoseFixB1S.boxPairCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBB v μ u) Φ
    ≤ (37 / 10) * ((Work.BoseFixB1B.PBBV v μ u) ^ 2
          / Work.BoseFixB1S.boxM2 (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBB v μ u)
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1B.PBM v μ)
                (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u v))
      * Work.BoseFixB1.pairSum v (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
          (Work.BoseFixB1B.PBd v μ) u Φ

/-- **The flat-arm rows**, packaged as a `Prop` (the shape of
`Work.BoseB1Cube.cubeSmallWinFlatArm37`): on the small window, the two target rows at `Cn = 4` for
the states satisfying `FlatArm37`, on the near-flat region `n₊ < c₀·∫Φ²` with a threshold `c₀ > 0`
that the statement is free to choose (it must be small relative to the fibre constant `Cm` of
`fibSum_le_manifest`). -/
def FlatArm37Rows (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ C c₀ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < c₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : E3, u ∈ goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        μ * Work.BoseFixB1B.PBW h μ u ≤ _root_.BoseGases.a v →
        (∀ {n' : ℕ}, 4 * μ * Work.BoseFixB1B.PBBV v μ u ≤ (n' : ℝ) →
            (n' : ℝ) < 5 * μ * Work.BoseFixB1B.PBBV v μ u →
            ∀ (Φ : X n' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Φ → Work.BoseFixB1B.InBox v μ u Φ →
              FlatArm37 v h μ n' Φ u →
              Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                  (Work.BoseFixB1.bV v μ u) Φ
                < c₀ * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2) →
              (1 / 18) * μ * ((n' : ℝ) / Work.BoseFixB1B.PBBV v μ u)
                  * Work.BoseFixB1B.PBW h μ u
                  * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2)
                ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ)
        ∧ (∀ {n'' : ℕ}, (n'' : ℝ) ≤ 8 * μ * Work.BoseFixB1B.PBBV v μ u →
            ∀ (Φ : X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Φ → Work.BoseFixB1B.InBox v μ u Φ →
              FlatArm37 v h μ n'' Φ u →
              Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                  (Work.BoseFixB1.bV v μ u) Φ
                < c₀ * (∫ x in Submission.BoseGases.abox n'' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2) →
              ((1 / 4) * (((n'' : ℝ) / Work.BoseFixB1B.PBBV v μ u) - μ) ^ 2
                    * Work.BoseFixB1B.PBW h μ u
                  - (1 / 2) * μ ^ 2 * Work.BoseFixB1B.PBW h μ u
                  - C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ
                        * Work.BoseFixB1B.PBW h μ u + μ * (_root_.BoseGases.a v)))
                  * (∫ x in Submission.BoseGases.abox n'' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2)
                ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ)

end Work.BoseB1Cube
