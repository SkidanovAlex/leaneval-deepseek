import ChallengeDeps
import Submission.Work.BoseB1Cube.Arms
import Submission.Work.BoseB1Cube.flatZeroLedger
import Submission.Work.BoseFixB1.CornerMismatch
import Submission.Work.BoseFixB1B.tBwordKinInd_eq_zero_of_boxQInd_ae_eq_zero
import Submission.Work.BoseFixB1S.flatBranchB1_boxConstant
import Submission.Work.BoseFixB1S.localCountSqPeelB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.cubeDensePos` — the dense band arm with its `n₊ = 0` slice removed

`Work.BoseB1Cube.CubeBandArmDenseAt v h R θ` (the residual of
`Submission/Work/BoseB1Cube/cubePerBox_holds.lean`, stated in `Arms.lean`) carries **no** lower
bound on the sliding-box excited count `n₊(B(u))`: its `n₊ = 0` slice is included.

That slice is **PROVED** in this area: `Work.BoseB1Cube.cubePerBox_flatZeroArm`
(`Submission/Work/BoseB1Cube/cubePerBox_flatZeroArm.lean`) proves the row on every non-thin good box
with `cnPlusBoxInd = 0` — and, since the duplicate declaration
`Work.BoseFixB1S.pairMass_eq_setIntegral` of `BoseFixB1S/boxConstCalibB1.lean` has been renamed to
`pairMass_eq_setIntegral_calib`, that module is now **importable in the chapter's cone** (verified:
`Submission/Work/BoseB1Cube/_probeConeUnlock.lean`; the only remaining import conflict of the area
is `Work.BoseFixB1S.chiSmallB_continuous ∈ {BoseFixB1S/chiSmallB_eq_zero_of_volume_dlBox_eq_zero,
BoseFixB1.Up/PairRowOper}`, which does not involve the flat-zero arm).

So the residual can be *strictly weakened*: it suffices to prove the row on the **positive** band
`0 < n₊(B(u)) ≤ 10^{-100}·n‖Φ‖²`.  This module states that weakened residual
(`Work.BoseB1Cube.CubeBandArmDensePos`) and proves

    CubeFlatZeroArm v h R  →  CubeBandArmDensePos v h R θ  →  CubeBandArmDenseAt v h R θ ,

the constants merging by `min`/`max` through `Work.BoseB1Cube.perBoxFCube_mono` (whose two
nonnegativity bricks are `perBoxCubeFWeight_nonneg` and `perBoxCubeErr_nonneg`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **The dense band arm with the exactly flat states removed** — `CubeBandArmDenseAt` with the
extra hypothesis `0 < n₊(B(u))`.  Strictly weaker than `CubeBandArmDenseAt`
(`cubeBandArmDenseAt_of_flatZero_and_pos`). -/
def CubeBandArmDensePos (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R θ : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ¬ IsThinBox v h μ u →
        0 < Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ) →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * normB v μ n (Φ : X n → ℝ) →
        θ * μ < flatTau (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
            (Φ : X n → ℝ) →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- **The residual is the positive-band one**: the exactly flat states (`n₊(B(u)) = 0`) are the
PROVED arm `Work.BoseB1Cube.CubeFlatZeroArm` (available in this cone as
`Work.BoseB1Cube.cubePerBox_flatZeroArm`), so only `0 < n₊(B(u))` remains. -/
theorem cubeBandArmDenseAt_of_flatZero_and_pos {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R θ : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hzero : CubeFlatZeroArm v h R) (hpos : CubeBandArmDensePos v h R θ) :
    CubeBandArmDenseAt v h R θ := by
  obtain ⟨εz, c₁z, Cz, hεz, hc₁z, hCz, hz⟩ := hzero
  obtain ⟨εp, c₁p, Cp, hεp, hc₁p, hCp, hp⟩ := hpos
  refine ⟨min εz εp, min c₁z c₁p, max Cz Cp, lt_min hεz hεp, lt_min hc₁z hc₁p,
    le_max_of_le_left hCz, ?_⟩
  intro μ hAdm n Φ u hgood hthin hband hdense
  have hAdmz : Adm v εz μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmp : Adm v εp μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hA : 0 ≤ Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u *
      (∫ x in abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x /
            Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u)) :=
    perBoxCubeFWeight_nonneg h hv hvrad hR hv_supp hAdm Φ u
  have hZ : 0 ≤ μ ^ 2 * (a v)
        * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
            + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u
        * normB v μ n (Φ : X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : X n → ℝ) :=
    perBoxCubeErr_nonneg hAdm (Work.BoseFixB1.adm_a_pos hAdm).le Φ u
  by_cases hν : Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ) = 0
  · exact perBoxFCube_mono Φ u (min_le_left _ _) (le_max_left _ _) hA hZ
      (hz μ hAdmz n Φ u hgood hthin hν)
  · have hνpos : 0 < Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ) :=
      lt_of_le_of_ne (Work.BoseFixB1.Up.nPlusB_nonneg v μ u n (Φ : X n → ℝ)) (Ne.symm hν)
    exact perBoxFCube_mono Φ u (min_le_right _ _) (le_max_right _ _) hA hZ
      (hp μ hAdmp n Φ u hgood hthin hνpos hband hdense)

end Work.BoseB1Cube
