import ChallengeDeps
import Submission.Work.BoseFixB1S.BoxQWords
import Submission.Work.BoseFixR.PerBoxCrudeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.flatArmBandDefs` — the flat arm of the band-condensed bound

`Work.BoseFixB1B.FlatArmBand v h` is the target `Work.BoseFixB1B.bandCondensedArm` with the
flatness hypothesis `boxQCount ≤ boxFlatCount` strengthened to `2·boxQCount ≤ boxFlatCount`.
It is thus the *exact complement* of the PROVED `Work.BoseFixB1B.bandExcitedArm` (which gives
`0 ≤ sbWord h μ u Φ` from `boxFlatCount ≤ 2·boxQCount`), and it is the only remaining content of
the target: `Work.BoseFixB1B.bandCondensedArm_of_flatArm` assembles the two arms.

The definition lives in this small `sorry`-free module so that both the assembler
(`Submission/Work/BoseFixB1B/bandCondensedArm.lean`) and the prover of the arm itself
(`Submission/Work/BoseFixB1B/bandFlatArm.lean`) can import it without importing each other.

Nothing here is a proof: this file only names the statement.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

/-- **The flat arm of the band-condensed bound**: on the `μ ↦ 4μ` band, for states that are
*denser* in `B(u)` than the threshold `K(μ·chiMass + 1)·‖Φ‖²` and whose condensate dominates the
excited count by a factor 2 (`2·boxQCount ≤ boxFlatCount`),

`−(C(μ²(a v)·chiMass + μ(a v)))·‖Φ‖² ≤ sbWord h μ u Φ`.

This is the complement of the PROVED `bandExcitedArm`. -/
def FlatArmBand (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ K C : ℝ, 0 < ε₀ ∧ 0 < K ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d (4 * μ) →
        Work.BoseFixR.crudeThreshold v K μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ) →
        2 * Work.BoseFixB1S.boxQCount
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1S.boxFlatCount
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ) →
        -(C * (μ ^ 2 * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            + μ * _root_.BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)

end Work.BoseFixB1B
