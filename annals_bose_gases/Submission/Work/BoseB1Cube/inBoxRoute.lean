import ChallengeDeps
import Submission.Work.BoseB1Cube.cubeSmallNArb
import Submission.Work.BoseB1Cube.denseAliveDeadSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.inBoxRoute` — the in-box FS route (lead's design `curric-46`, node A)

The lead's design (`sources/boseDCF/bose_deadrow_cubicfree.md` §A, wire statements in
`sources/boseDCF/bose_deadrow_cubicfree_REVIEW_wire.lean`, namespace `Work.C46Design`) redirects the
dense half of the chapter away from the alive/dead split:

* the pair-dead class `Work.BoseB1Cube.CubeBandArmDenseDeadRow` is TRUE but has **no state-level
  payer** — FS pays it by `Q₃ ↦ Q₄` Cauchy–Schwarz plus the refined `lm:appbubogolubov` in the
  `MΔ`-payer form, which the corpus has only for **in-box** states.  In particular the sharp
  capacity aggregation `voidCap(⋃B(c_j,ρ)) ≥ (1−o(1))4πρk` is **FALSE** for clustered centres
  (capacity is subadditive), so the razor/capacity line is closed;
* hence the route is `InBoxCubeRow` (the in-box row, all `n`) ⟹ `CubePerBox`, with no split.

This module carries the shared vocabulary of that route in the chapter's own namespace
(`Work.BoseB1Cube`): the definition `InBoxCubeRow` and the two *proved* restriction lemmas relating
the dead row to the positive arms.  The analytic nodes `cubePerBox_of_inBoxCubeRow` (A2),
`inBoxCubeRow_of_chain` (A4) and `InBoxVarRow` (A3) are delegated separately; `InBoxVarRow` is
stated in the `AprioriCount` vocabulary (see `Submission/Work/AprioriCount/cubeDenseAliveRow.lean`).

**Do not** attack `CubeBandArmDenseDeadRow` as a class (lead, node A): its restriction lemmas are
proved below, and the capacity route is refuted.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **(A0, PROVED)** the dead row is a restriction of the positive dense arm. -/
theorem deadRow_of_densePos {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R θ : ℝ}
    (hpos : CubeBandArmDensePos v h R θ) : CubeBandArmDenseDeadRow v h R θ := by
  obtain ⟨ε₀, c₁, C, hε, hc, hC, hrow⟩ := hpos
  exact ⟨ε₀, c₁, C, hε, hc, hC, fun μ hA n Φ u hg ht hν hb hd _ => hrow μ hA n Φ u hg ht hν hb hd⟩

/-- **(A0′, PROVED)** the dead row is a restriction of `CubePerBox`. -/
theorem deadRow_of_cubePerBox {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R θ : ℝ}
    (hpb : CubePerBox v h R) : CubeBandArmDenseDeadRow v h R θ := by
  obtain ⟨ε₀, c₁, C, hε, hc, hC, hrow⟩ := hpb
  exact ⟨ε₀, c₁, C, hε, hc, hC, fun μ hA n Φ u hg _ _ _ _ _ => hrow μ hA n Φ u hg⟩

/-- **(A1) The in-box FS row**: `PerBoxFCube` for normalised states localised in the sliding box
`B(u)` (every slot a.e. in `dlBox`), on the good set, for EVERY `n` and every density (no band, no
dense/dilute, no alive/dead split).  This is FS `thm:smallbox` on the `n`-particle sector of
`B(u)`. -/
def InBoxCubeRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict
            (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
          (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
            ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
        (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1 →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

-- **The in-box row is strictly stronger than the positive dense arm** — but only in the presence
-- of the normalisation `∫Φ² = 1`, which the dense arm does not carry.  Recorded as a comment rather
-- than a lemma: `InBoxCubeRow ⟹ (the dense-band hypotheses) ⟹ CubeBandArmDensePos` holds for
-- normalised states, since the band `n₊ ≤ cubeBandT·n·N` is then implied by `n₊ ≤ n` and the
-- density window is unused by the in-box row.

end Work.BoseB1Cube
