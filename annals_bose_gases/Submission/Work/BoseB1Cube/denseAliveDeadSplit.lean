import ChallengeDeps
import Submission.Work.BoseB1Cube.cubeDensePos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.denseAliveDeadSplit` — the pair-alive / pair-dead split of the dense
# band arm

Session-10 deliverable (`FINDING_cubeDensePos_session10.md` §2–§4).  The residual of the chapter
is `Work.BoseB1Cube.CubeBandArmDensePos`, i.e. the row `PerBoxFCube` on the dense band.  The
pair column of that row is paid either by the **pair sum** `flatPairSum` (the *pair-alive* class,
where `flatPairSum` is at least `w1MassB·boxPairCount/(2·boxMass²)`, i.e. at least `A/R₂` with
`A = boxM2·boxPairCount/(2·boxMass²)` the payout's anchor and `R₂ = boxM2/w1MassB ≥ 1+c₀`) or it
is not, in which case the payout `(√A − √(D/2))² ≤ Ps` is weak and the only available payer is the
razor/kinetic slot (*pair-dead*).

This module only states the split and proves the (elementary) reassembly

    CubeBandArmDenseAliveRow → CubeBandArmDenseDeadRow → CubeBandArmDensePos ,

with the constants merged by `min`/`max` through `Work.BoseB1Cube.perBoxFCube_mono` (exactly as
`cubeBandArmDenseAt_of_flatZero_and_pos` merges the flat-zero and positive arms).  The analytic
content lives in the two hypothesis `Prop`s; the dichotomy is by the decidable-comparison
`w1MassB·boxPairCount/(2·boxMass²) ≤ flatPairSum` on the state.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The pair-alive half of the dense band arm** — the row on the dense band with the extra
hypothesis that the pair sum dominates `w₁·cS₂/(2V²)` (`cS₂ = boxPairCount`, `V = boxMass`), i.e.
`flatPairSum ≥ A/R₂` with `A` the payout anchor of `Work.BoseFixB1S.pairSumGeSqSubSqrt`.

This is *strictly weaker* than `CubeBandArmDensePos`, and it is the class on which the pair column
is provable from the on-disk instruments with a **fixed** constant (`C = 250` suffices; see
`FINDING_cubeDensePos_session10.md` §2/§2bis).  Its complement is the razor's own class
`{(1−δ)·R₂ < 1}` (`δ` the payout loss). -/
def CubeBandArmDenseAliveRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R θ : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        0 < Work.BoseFixB1.Up.nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        θ * μ < Work.BoseFixB1.flatTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            * Work.BoseFixB1S.boxPairCount
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ)
            / (2 * (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) ^ 2)
          ≤ Work.BoseFixB1.flatPairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- **The pair-dead half of the dense band arm** — the row on the dense band where the pair sum is
*below* `w₁·cS₂/(2V²)`.  This is the razor's own class: there the payout
`(√A − √(D/2))² ≤ Ps` gives at most `A/R₂`, and the pair-condensate payer is switched off, so the
only payer is the kinetic/spectral slot (`Work.BoseB1Cube.bandKinDeadB`, the capacity `(G)`). -/
def CubeBandArmDenseDeadRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R θ : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        0 < Work.BoseFixB1.Up.nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        θ * μ < Work.BoseFixB1.flatTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ) →
        ¬ (Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            * Work.BoseFixB1S.boxPairCount
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ)
            / (2 * (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) ^ 2)
          ≤ Work.BoseFixB1.flatPairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ)) →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- **The dense band arm is the union of its pair-alive and pair-dead halves.**  The split is on the
scalar comparison `w₁·cS₂/(2V²) ≤ flatPairSum` on the state; the constants merge by `min`/`max`
through `Work.BoseB1Cube.perBoxFCube_mono` (whose two nonnegativity bricks are
`perBoxCubeFWeight_nonneg` and `perBoxCubeErr_nonneg`), exactly as in
`cubeBandArmDenseAt_of_flatZero_and_pos`. -/
theorem cubeBandArmDensePos_of_alive_dead {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R θ : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (halive : CubeBandArmDenseAliveRow v h R θ) (hdead : CubeBandArmDenseDeadRow v h R θ) :
    CubeBandArmDensePos v h R θ := by
  obtain ⟨εa, c₁a, Ca, hεa, hc₁a, hCa, ha⟩ := halive
  obtain ⟨εd, c₁d, Cd, hεd, hc₁d, hCd, hd⟩ := hdead
  refine ⟨min εa εd, min c₁a c₁d, max Ca Cd, lt_min hεa hεd, lt_min hc₁a hc₁d,
    le_max_of_le_left hCa, ?_⟩
  intro μ hAdm n Φ u hgood hthin hνpos hband hdense
  have hAdma : Work.BoseBoxFix.Adm v εa μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmd : Work.BoseBoxFix.Adm v εd μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hA : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u *
        (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
          Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x /
              Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)) :=
    perBoxCubeFWeight_nonneg h hv hvrad hR hv_supp hAdm Φ u
  have hZ : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
        * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
            + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      + μ * (_root_.BoseGases.a v) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    perBoxCubeErr_nonneg hAdm (Work.BoseFixB1.adm_a_pos hAdm).le Φ u
  by_cases hcmp : Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      * Work.BoseFixB1S.boxPairCount
          (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Φ : Submission.BoseGases.X n → ℝ)
        / (2 * (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) ^ 2)
      ≤ Work.BoseFixB1.flatPairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
  · exact perBoxFCube_mono Φ u (min_le_left _ _) (le_max_left _ _) hA hZ
      (ha μ hAdma n Φ u hgood hthin hνpos hband hdense hcmp)
  · exact perBoxFCube_mono Φ u (min_le_right _ _) (le_max_right _ _) hA hZ
      (hd μ hAdmd n Φ u hgood hthin hνpos hband hdense hcmp)

end Work.BoseB1Cube
