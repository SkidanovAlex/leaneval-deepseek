import ChallengeDeps
import Submission.Work.BoseB1Cube.CubeRows
import Submission.Work.BoseB1Cube.PerBoxLHS
import Submission.Work.BoseFixB1B.matchedChainedBound
import Submission.Work.BoseFixB1S.perBoxGapBranchB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.Arms` — the three pointwise arms of the cube per-box row

The per-box row `Work.BoseFixB1S.PerBoxFCube` is *pointwise* in `u` and has **no**
lowness/localisation hypothesis, so its trichotomy is elementary: for a state on a good box either

* the box is **thin** (`Work.BoseFixB1.IsThinBox`) — the PROVED
  `Work.BoseB1Cube.cubePerBox_thinArm`;
* or the box is **gap-dominated** (`γ_g·n‖Φ‖² ≤ n₊(B(u))` with the small `γ_g ≤ 10^{-100}` of FS's
  own dichotomy, `Work.BoseFixB1.Up.perBoxF_thick_of_flatBranch`) — the cube twin
  `Work.BoseB1Cube.CubeGapArmGamma` of the PROVED `Work.BoseFixB1.Up.perBoxF_of_gapPayment`;
* or the box is in the **flat band** `n₊(B(u)) ≤ 10^{-100}·n‖Φ‖²` — the analytic frontier,
  isolated in `Submission/Work/BoseB1Cube/CubeRows.lean` as `CubeFlatWordKin`.

The three cases exhaust the states (`γ_g ≤ 10^{-100}` is what makes the band hypothesis follow from
the negation of the gap hypothesis), and the constants merge by `min`/`max` through the
monotonicity `Work.BoseB1Cube.perBoxFCube_mono`.  This module contains only the **vocabulary and
the assembly**; the arms themselves are proved elsewhere
(`Work.BoseB1Cube.cubePerBox_thinArm`, `Work.BoseB1Cube.cubePerBox_gapArmInCone`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

/-! ## 5. The three arms of the pointwise trichotomy, and their assembly

The per-box row `PerBoxFCube` is *pointwise* in `u` and has **no** lowness/localisation
hypothesis, so its trichotomy is elementary: for a state on a good box either

* the box is **thin** (`Work.BoseFixB1.IsThinBox`: the cut-off support is thinner than
  `supp g₀`, so the localised one-body kernel vanishes) — the PROVED
  `Work.BoseB1Cube.cubePerBox_thinArm`;
* or the box is **gap-dominated** (`γ_g·n‖Φ‖² ≤ n₊(B(u))` with a *small* `γ_g`) — the cube twin of
  the PROVED `Work.BoseFixB1.Up.perBoxF_of_gapPayment`
  (`Work.BoseB1Cube.cubePerBox_gapArmGamma`), whose `γ_g ≤ 10^{-100}` is the constant the corpus's
  own dichotomy (`perBoxF_thick_of_flatBranch`) uses;
* or the box is in the **flat band** `n₊(B(u)) ≤ 10^{-100}·n‖Φ‖²` — the analytic frontier of the
  chapter, isolated in `Submission/Work/BoseB1Cube/CubeRows.lean` as `CubeFlatWordKin`.

The three cases exhaust the states (`γ_g ≤ 10^{-100}` is what makes the last hypothesis follow
from the negation of the second), and the constants merge by `min`/`max` through the monotonicity
`Work.BoseB1Cube.perBoxFCube_mono`. -/

/-- The **gap arm** of the pointwise trichotomy: the cube gap branch at the small threshold
`γ ≤ 10^{-100}` — the cube twin of the PROVED `Work.BoseFixB1.Up.perBoxF_of_gapPayment`. -/
def CubeGapArmGamma (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C γ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < γ ∧ γ ≤ (1 / 10 : ℝ) ^ (100 : ℕ) ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        γ * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
          ≤ Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v)) (dlBox (sideAt μ (a v))
              (paramsAt μ (a v)).d u) (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
              (Φ : X n → ℝ) →
        Work.BoseFixB1S.PerBoxFCube v h R (1 / 4) C μ n Φ u

/-- The **thin arm**: the degenerate ("thin") boxes — the conclusion of the PROVED
`Work.BoseB1Cube.cubePerBox_thinArm`. -/
def CubeThinArm (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        Work.BoseFixB1.IsThinBox v h μ u →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- The **band arm**: the flat band `n₊(B(u)) ≤ 10^{-100}·n‖Φ‖²` on the non-thin boxes, at a
free pair `(c₁, C)`.  This is the shape in which the matched-window flat residual
`Work.BoseB1Cube.CubeFlatWordKin` (`CubeRows.lean`) lands after the Δ-augmented ledger
`Work.BoseB1Cube.perBoxFCube_of_ledgerDelta`. -/
def CubeBandArm (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * normB v μ n (Φ : X n → ℝ) →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- The **flat-zero arm**: the exactly flat (`n₊(B(u)) = 0`) states on non-thin boxes — the
conclusion of the PROVED `Work.BoseB1Cube.cubePerBox_flatZeroArm` (`cubePerBox_flatZeroArm.lean`;
its in-cone ledger `Work.BoseB1Cube.CubeFlat.perBoxF_of_flatZeroCube` lives in
`flatZeroLedger.lean`).  Note: this arm needs **no** band hypothesis and **no** position
restriction, and it is *provable* — which shows that the target's own row holds at the exactly flat
states even where the (stronger) *word* row of `CubeRows.lean` fails (the `χ`-shell obstruction
recorded in `FINDING_cubePerBox_session2.md` §8). -/
def CubeFlatZeroArm (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v)) (dlBox (sideAt μ (a v))
            (paramsAt μ (a v)).d u) (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            (Φ : X n → ℝ) = 0 →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- The **positive band arm**: the flat band `0 < n₊(B(u)) ≤ 10^{-100}·n‖Φ‖²` on the non-thin
boxes, at a free pair `(c₁, C)`.  This is the *weakest* residual of the chapter that still suffices
for `CubePerBox` once the exactly flat states are routed to the PROVED `CubeFlatZeroArm`; it is the
shape of `Work.BoseB1Cube.CubeBandArm` with the exactly flat states removed. -/
def CubeBandArmPos (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        0 < Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ) →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * normB v μ n (Φ : X n → ℝ) →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- **The assembly of the trichotomy.**  The three arms above imply `CubePerBox`: the split is on
`IsThinBox`, then on `γ_g n‖Φ‖² ≤ n₊(B(u))`, the remaining case being the band because
`γ_g ≤ 10^{-100}`; the constants merge by `min`/`max` via `perBoxFCube_mono`. -/
theorem cubePerBox_of_arms {v : E3 → ℝ} {h : ScatSol v} {R : ℝ} (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hg : CubeGapArmGamma v h R) (htt : CubeThinArm v h R) (hb : CubeBandArm v h R) :
    CubePerBox v h R := by
  obtain ⟨εg, Cg, γg, hεg, hCg, hγg, hγg100, hgap⟩ := hg
  obtain ⟨εt, c₁t, Ct, hεt, hc₁t, hCt, hthin⟩ := htt
  obtain ⟨εb, c₁b, Cb, hεb, hc₁b, hCb, hband⟩ := hb
  refine ⟨min εg (min εt εb), min (1 / 4) (min c₁t c₁b), max Cg (max Ct Cb),
    lt_min hεg (lt_min hεt hεb), lt_min (by norm_num) (lt_min hc₁t hc₁b),
    le_max_of_le_left hCg, ?_⟩
  intro μ hAdm n Φ u hgood
  have hAdm_g : Adm v εg μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdm_t : Adm v εt μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdm_b : Adm v εb μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  have hav : 0 < a v := Work.BoseFixB1.adm_a_pos hAdm
  -- the two nonnegativity bricks of `perBoxFCube_mono`
  have hA : 0 ≤ Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u *
      (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x /
            Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u)) :=
    perBoxCubeFWeight_nonneg h hv hvrad hR hv_supp hAdm Φ u
  have hZ : 0 ≤ μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : X n → ℝ) :=
    perBoxCubeErr_nonneg hAdm hav.le Φ u
  by_cases hth : Work.BoseFixB1.IsThinBox v h μ u
  · exact perBoxFCube_mono Φ u (le_trans (min_le_right _ _) (min_le_left _ _))
      (le_trans (le_max_left _ _) (le_max_right _ _)) hA hZ (hthin μ hAdm_t n Φ u hgood hth)
  · by_cases hgapcase : γg * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
        ≤ Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v)) (dlBox (sideAt μ (a v))
            (paramsAt μ (a v)).d u) (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            (Φ : X n → ℝ)
    · -- gap arm
      exact perBoxFCube_mono Φ u (min_le_left _ _) (le_max_left _ _) hA hZ
        (hgap μ hAdm_g n Φ u hgapcase)
    · -- band arm
      refine perBoxFCube_mono Φ u (le_trans (min_le_right _ _) (min_le_right _ _))
        (le_trans (le_max_right _ _) (le_max_right _ _)) hA hZ
        (hband μ hAdm_b n Φ u hgood hth ?_)
      -- the band hypothesis, from the negation of the gap hypothesis and `γg ≤ 10^{-100}`
      have hN0 : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hlt : Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
          < γg * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := not_le.mp hgapcase
      have hmul : γg * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
          ≤ cubeBandT * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
        rw [cubeBandT]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγg100 hn0) hN0
      linarith

/-- **The four-arm assembly**: with the PROVED flat-zero arm routed to the exactly flat states, the
band arm only has to carry the *positive* band `0 < n₊(B(u)) ≤ 10^{-100}n‖Φ‖²`.  The split is
`IsThinBox` → `n₊ = 0` → `γ_g n‖Φ‖² ≤ n₊` → band; `0 < n₊` in the last case follows from
`n₊ ≠ 0` and `n₊ ≥ 0` (`Work.BoseFixB1.Up.nPlusB_nonneg`). -/
theorem cubePerBox_of_arms4 {v : E3 → ℝ} {h : ScatSol v} {R : ℝ} (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hg : CubeGapArmGamma v h R) (htt : CubeThinArm v h R) (hfz : CubeFlatZeroArm v h R)
    (hb : CubeBandArmPos v h R) : CubePerBox v h R := by
  obtain ⟨εg, Cg, γg, hεg, hCg, hγg, hγg100, hgap⟩ := hg
  obtain ⟨εt, c₁t, Ct, hεt, hc₁t, hCt, hthin⟩ := htt
  obtain ⟨εf, c₁f, Cf, hεf, hc₁f, hCf, hfz'⟩ := hfz
  obtain ⟨εb, c₁b, Cb, hεb, hc₁b, hCb, hband⟩ := hb
  refine ⟨min εg (min εt (min εf εb)),
    min (1 / 4) (min c₁t (min c₁f c₁b)), max Cg (max Ct (max Cf Cb)),
    lt_min hεg (lt_min hεt (lt_min hεf hεb)),
    lt_min (by norm_num) (lt_min hc₁t (lt_min hc₁f hc₁b)),
    le_max_of_le_left hCg, ?_⟩
  intro μ hAdm n Φ u hgood
  have hAdm_g : Adm v εg μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdm_t : Adm v εt μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdm_f : Adm v εf μ :=
    Work.BoseFixB1.Adm.mono hAdm
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hAdm_b : Adm v εb μ :=
    Work.BoseFixB1.Adm.mono hAdm
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hav : 0 < a v := Work.BoseFixB1.adm_a_pos hAdm
  have hA : 0 ≤ Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u *
      (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x /
            Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u)) :=
    perBoxCubeFWeight_nonneg h hv hvrad hR hv_supp hAdm Φ u
  have hZ : 0 ≤ μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : X n → ℝ) :=
    perBoxCubeErr_nonneg hAdm hav.le Φ u
  by_cases hth : Work.BoseFixB1.IsThinBox v h μ u
  · exact perBoxFCube_mono Φ u (le_trans (min_le_right _ _) (min_le_left _ _))
      (le_trans (le_max_left _ _) (le_max_right _ _)) hA hZ
      (hthin μ hAdm_t n Φ u hgood hth)
  · by_cases hzero : Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ) = 0
    · -- exactly flat: the PROVED flat-zero arm
      exact perBoxFCube_mono Φ u
        (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_left _ _))
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hA hZ
        (hfz' μ hAdm_f n Φ u hgood hth hzero)
    · have hpos : 0 < Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ) :=
        lt_of_le_of_ne (Work.BoseFixB1.Up.nPlusB_nonneg v μ u n (Φ : X n → ℝ))
          (Ne.symm hzero)
      by_cases hgapcase : γg * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
          ≤ Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v)) (dlBox (sideAt μ (a v))
              (paramsAt μ (a v)).d u) (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
              (Φ : X n → ℝ)
      · -- gap arm
        exact perBoxFCube_mono Φ u (min_le_left _ _) (le_max_left _ _) hA hZ
          (hgap μ hAdm_g n Φ u hgapcase)
      · -- positive band arm
        refine perBoxFCube_mono Φ u
          (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_right _ _))
          (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hA hZ
          (hband μ hAdm_b n Φ u hgood hth hpos ?_)
        have hN0 : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hlt : Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            < γg * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := not_le.mp hgapcase
        have hmul : γg * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * normB v μ n (Φ : X n → ℝ) := by
          rw [cubeBandT]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγg100 hn0) hN0
        linarith

/-! ## 6. The density split of the positive band: `CubeBandArmDiluteAt` / `CubeBandArmDenseAt`

The positive-band residual `CubeBandArmPos` above is *further* split by the state's windowed mean
density `τ = flatTau = flatScountB/(chiMass·‖Φ‖²)`:

* **dilute** (`τ ≤ θμ`, `θ` prescribed): the row is **PROVED** — the cube twin
  `Work.BoseB1Cube.cubeBandArmDilute_holds` of the assembly
  `flatFterm_le_mu_sq_add` + `Work.BoseB1Cube.cubeDiluteFibreRow`;  it uses *no* capacity, *no*
  count window, *no* lowness, *no* band hypothesis and *no* lower bound on `n₊`, and it holds for
  **any** `θ < 1`;
* **dense** (`θμ < τ`): the strictly narrower residual.

Both arms are parametrised by the *same* prescribed `θ`, because the dilute half's threshold is
fixed by the fibre row it consumes.  `cubeBandArm_of_splitAt` reassembles the two halves into the
band arm `CubeBandArm` (and hence, with the PROVED `cubePerBox_of_arms`, into `CubePerBox`);
`cubeBandArmPos_of_splitAt` is the sharper form when the exactly flat states are already
discharged by `cubePerBox_flatZeroArm`.

⚠ **`n₊ = 0` in the dense arm.**  Because `cubeDiluteFibreRow` requires `0 < n₊` (a *redundant*
hypothesis: the row is now stated without the band and without `0 < n₊`, but the `n₊ = 0` slice is
not reachable through it), the *dilute* arm carries `0 < n₊` nowhere in the split — the split is
purely on `τ`.  The `n₊ = 0` states are PROVED (`Work.BoseB1Cube.CubeFlatZeroArm`,
`cubePerBox_flatZeroArm`), but that module's import cone declares
`Work.BoseFixB1S.boxConstCalibB1` while this chapter's dilute side needs
`Work.BoseFixB1S.boxPairValue`; both declare `Work.BoseFixB1S.pairMass_eq_setIntegral`, so the two
cones cannot be imported together (see `FINDING_cubeDiluteArm.md` §3 for the exact repair). -/

/-- **The dilute half of the density split**, at a prescribed threshold `θ`: the row on every
non-thin sliding box whose windowed mean density is at most `θμ`.  **PROVED** —
`Work.BoseB1Cube.cubeBandArmDilute_holds`. -/
def CubeBandArmDiluteAt (v : E3 → ℝ) (h : ScatSol v) (R θ : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        Work.BoseFixB1.flatTau (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
              (Φ : X n → ℝ) ≤ θ * μ →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- **The dense half of the density split**, at the same prescribed threshold `θ`: the row on the
band `n₊ ≤ 10^{-100} n‖Φ‖²` at windowed mean density above `θμ`.  This is the *hard core* of the
chapter's residual. -/
def CubeBandArmDenseAt (v : E3 → ℝ) (h : ScatSol v) (R θ : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
        u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        Work.BoseFixB1.Up.nPlusB v μ u n (Φ : X n → ℝ)
            ≤ cubeBandT * (n : ℝ) * normB v μ n (Φ : X n → ℝ) →
        θ * μ < Work.BoseFixB1.flatTau (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u (Φ : X n → ℝ) →
        Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u

/-- The two halves at one and the same threshold imply the **band arm** `CubeBandArm` (the row on
`goodSet ∧ ¬IsThinBox ∧ n₊ ≤ 10^{-100}n‖Φ‖²`, with no lower bound on `n₊`), by a case split on
`τ ⋛ θμ`; the constants merge by `min`/`max` through `perBoxFCube_mono`. -/
theorem cubeBandArm_of_splitAt {v : E3 → ℝ} {h : ScatSol v} {R θ : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hdil : CubeBandArmDiluteAt v h R θ) (hden : CubeBandArmDenseAt v h R θ) :
    CubeBandArm v h R := by
  obtain ⟨εd, c₁d, Cd, hεd, hc₁d, hCd, hdil'⟩ := hdil
  obtain ⟨εn, c₁n, Cn, hεn, hc₁n, hCn, hden'⟩ := hden
  refine ⟨min εd εn, min c₁d c₁n, max Cd Cn, lt_min hεd hεn, lt_min hc₁d hc₁n,
    le_max_of_le_left hCd, ?_⟩
  intro μ hAdm n Φ u hgood hth hband
  have hAdmd : Adm v εd μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmn : Adm v εn μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
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
  by_cases hcase : Work.BoseFixB1.flatTau (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u (Φ : X n → ℝ) ≤ θ * μ
  · exact perBoxFCube_mono Φ u (min_le_left _ _) (le_max_left _ _) hA hZ
      (hdil' μ hAdmd n Φ u hgood hth hcase)
  · exact perBoxFCube_mono Φ u (min_le_right _ _) (le_max_right _ _) hA hZ
      (hden' μ hAdmn n Φ u hgood hth hband (lt_of_not_ge hcase))

/-- The two halves at one and the same threshold imply the positive-band arm (a case split; the
constants merge by `min`/`max` through `perBoxFCube_mono`). -/
theorem cubeBandArmPos_of_splitAt {v : E3 → ℝ} {h : ScatSol v} {R θ : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hdil : CubeBandArmDiluteAt v h R θ) (hden : CubeBandArmDenseAt v h R θ) :
    CubeBandArmPos v h R := by
  have hband := cubeBandArm_of_splitAt hv hvrad hR hv_supp hdil hden
  obtain ⟨ε₀, c₁, C, hε₀, hc₁, hC, hbody⟩ := hband
  exact ⟨ε₀, c₁, C, hε₀, hc₁, hC,
    fun μ hAdm n Φ u hgood hth _hpos hbnd => hbody μ hAdm n Φ u hgood hth hbnd⟩

/-- The four-arm assembly: gap / thin / dilute / dense at one and the same threshold `θ`. -/
theorem cubePerBox_of_arms6 {v : E3 → ℝ} {h : ScatSol v} {R θ : ℝ} (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hg : CubeGapArmGamma v h R) (htt : CubeThinArm v h R)
    (hdil : CubeBandArmDiluteAt v h R θ) (hden : CubeBandArmDenseAt v h R θ) :
    CubePerBox v h R :=
  cubePerBox_of_arms hv hvrad hR hv_supp hg htt
    (cubeBandArm_of_splitAt hv hvrad hR hv_supp hdil hden)

end Work.BoseB1Cube
