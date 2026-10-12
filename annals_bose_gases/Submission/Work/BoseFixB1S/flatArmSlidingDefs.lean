import ChallengeDeps
import Submission.Work.BoseFixB1.perBoxF_localised
import Submission.Work.BoseFixR.PerBoxCrudeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The **chemical debit** of the sliding word at FS's parameters: `μ · fibSum`
(`Work.BoseFixB1.fibSum` is the fibre loss `Σᵢ∫Φ²∫_y w_{1,B(u)}(xᵢ,y)dy`). -/
noncomputable def chemicalDebit {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  μ * Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Φ

/-- The **deficit** of the sliding word: the chemical debit minus the two credits
(`sbKin` and the pair term).  By `sbWord = sbKin + pairSum − μ·fibSum`, the target's conclusion is
`deficitSliding ≤ C·(μ²(a v)χ + μ(a v))·‖Φ‖²`. -/
noncomputable def deficitSliding {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  chemicalDebit (v := v) h μ Φ u
    - Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u Φ
    - Work.BoseFixB1.pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Φ

/-- **The `(i)`-hypothesis of the target** (the state is denser in `B(u)` than
`K(μ·χ-mass + 1)·‖Φ‖²`). -/
def OccHyp {v : E3 → ℝ} (K μ : ℝ) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : Prop :=
  Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Φ
    ≥ K * (μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
      * Work.BoseBoxFix.normB v μ n Φ

/-- **The flat arm of `condensedArmSliding`** — the genuine residual: on the states whose credits
`sbKin + pairSum` are *below* the chemical line `μ·fibSum`, the allowance
`C(μ²(a v)·χ-mass + μ·(a v))‖Φ‖²` pays the deficit (and the target's hypothesis `(i)` is assumed;
the condensation hypothesis `(ii)` of the target is *not* needed for this statement, and is
therefore not repeated here — a prover may use it freely by strengthening the statement).

This is FS §5's flat branch: it excludes every state with a nonpositive demand, every state whose
kinetic word alone covers the demand, and every *pair-rich* state (where `pairSum` alone covers it
— on the flat state at density `μ` this is FS's Born-gap slack `½M₂ ≥ (½+c)M₁`). -/
def FlatArmSliding {v : E3 → ℝ} (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ K C : ℝ, 0 < ε₀ ∧ 0 < K ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        OccHyp (v := v) K μ (Φ : Submission.BoseGases.X n → ℝ) u →
        0 < deficitSliding (v := v) h μ (Φ : Submission.BoseGases.X n → ℝ) u →
        deficitSliding (v := v) h μ (Φ : Submission.BoseGases.X n → ℝ) u
          ≤ C * (μ ^ 2 * _root_.BoseGases.a v
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * _root_.BoseGases.a v)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)

end Work.BoseFixB1S
