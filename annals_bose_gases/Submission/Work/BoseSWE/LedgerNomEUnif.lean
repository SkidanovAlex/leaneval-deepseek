import ChallengeDeps
import Submission.Work.BoseSWE.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseSWE.LedgerNomEUnif` — the a-priori ledger **with the slack**, as a hypothesis

`Work.BoseSWE.LedgerNomEUnif v h R` is the *statement* of the a-priori ledger in the `E`-vocabulary
(the `E`-twin of `Work.BoseB1Cube.ledgerNom`), opened up as a `Prop` in its four row parameters
`c₁, C, E, CE` so that consumers (`countWindowOfPerBoxFNomSlotsE`) can take it as a hypothesis and
run *before* the ledger itself is proved.  The instance is produced by
`Work.BoseSWE.ledgerNomE` (child of this area) via `Work.BoseSWE.ledgerNomEUnif_holds` (in
`F4d_Node.lean`).

Shape (identical to `ledgerNomE`): from the two-slot per-box row with the slack,
`Work.BoseSWE.PerBoxFNomE v h R c₁ C CE μp μ n Φ u` for `μp ∈ {μ, 4μ}`, and FS's localisation
`Work.BoseB1Cube.SlidingGoodCube v h`, one gets thresholds `ε₀, C_A ≥ 0, E' ≥ 0` such that for
every low state

    c₁·nomRPsi ≤ C_A·(μ²(a v)ℓ³κ)·‖Φ‖² + E'·(μ(a v)κ)·n·‖Φ‖² ,   (b/(2ℓ²))·⟨n₊⟩ ≤ (same) .
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The a-priori ledger with the slack, as a `Prop` in its row parameters. -/
def LedgerNomEUnif (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∀ (c₁ C E CE : ℝ), 0 < c₁ → 0 ≤ C → 0 < E → 0 ≤ CE →
    (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : E3),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          ∀ μp : ℝ, (μp = μ ∨ μp = 4 * μ) →
            PerBoxFNomE v h R c₁ C CE μp μ n Φ u) →
    Work.BoseB1Cube.SlidingGoodCube v h →
    ∃ ε₀ C_A E' : ℝ, 0 < ε₀ ∧ 0 ≤ C_A ∧ 0 ≤ E' ∧
      ∀ (J μ : ℝ), Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ)
          (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            c₁ * Work.BoseB1Cube.nomRPsi h μ (Φ : X n → ℝ)
                ≤ C_A * (μ ^ 2 * (_root_.BoseGases.a v)
                      * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                      * Work.BoseB1Cube.kappa v μ)
                    * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
                  + E' * (μ * (_root_.BoseGases.a v) * Work.BoseB1Cube.kappa v μ) * (n : ℝ)
                      * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
            ∧ ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
                    / (2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
                  * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Φ : X n → ℝ)
                ≤ C_A * (μ ^ 2 * (_root_.BoseGases.a v)
                      * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                      * Work.BoseB1Cube.kappa v μ)
                    * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
                  + E' * (μ * (_root_.BoseGases.a v) * Work.BoseB1Cube.kappa v μ) * (n : ℝ)
                      * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)

end Work.BoseSWE
