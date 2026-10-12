import ChallengeDeps
import Submission.Work.BoseB1Cube.nomRowLinWindowRow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.smallWinDefs` — the `Prop` of the small-window case of the node

Holder-independent definition module (definitions only, no `sorry`), so that both the holder
`Submission/Work/BoseB1Cube/normNodeOfPort.lean` (which proves `NormNode` from it plus the
large-window case) and the delegated lemma `Submission/Work/BoseB1Cube/SmallWinNode.lean` (which
proves it) can import it without an import cycle.

`Work.BoseB1Cube.SmallWinProp v h R` is `Work.BoseB1Cube.NormNode v h R` with the single extra
hypothesis `μ · bW v h μ u ≤ a v` — branch 1 of the PROVED
`Work.BoseB1Cube.windowShiftDichotomy`.  It is *strictly weaker* than the node.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

/-- **The small-window case of `Work.BoseB1Cube.NormNode`** — the node's row, with the extra
hypothesis `μ · bW v h μ u ≤ a v` (branch 1 of the PROVED `windowShiftDichotomy`). -/
def SmallWinProp (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        μ * Work.BoseFixB1.bW v h μ u ≤ _root_.BoseGases.a v →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

/-- **The large-window (port-ledger) case of `Work.BoseB1Cube.NormNode`** — the node's row with the
extra hypothesis `¬ (μ · bW v h μ u ≤ a v)`, i.e. branch 2 of the PROVED `windowShiftDichotomy`.
On this branch the shift hypothesis holds, hence the box datum `(1−2Γ)Gχ ≤ bM2 − bW`
(`Work.BoseB1Cube.boxM2_sub_w1MassB_ge_of_windowDichotomy`), and the PROVED port rung
`Work.BoseB1Cube.sbWordCube_ge_payPortR3` + `ledger_crux` close the ledger; the other three box-data
rows are supplied by `Work.BoseB1Cube.boxDataShift`.  Strictly weaker than the node. -/
def LargeWinProp (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ Cn : ℝ, 4 ≤ Cn → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Ψ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ¬ (μ * Work.BoseFixB1.bW v h μ u ≤ _root_.BoseGases.a v) →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ))),
          Ψ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1.bA v μ u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), (Ψ x) ^ 2) = 1 →
        Cn * μ * Work.BoseFixB1.bV v μ u ≤ (n : ℝ) →
        (n : ℝ) ≤ 2 * Cn * μ * Work.BoseFixB1.bV v μ u →
        (1 / 18) * μ * ((n : ℝ) / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bW v h μ u
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ

end Work.BoseB1Cube

end
