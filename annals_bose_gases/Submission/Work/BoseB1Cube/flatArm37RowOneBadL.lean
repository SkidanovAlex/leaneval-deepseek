import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.chiScaleZeroSmallBox
import Submission.Work.BoseB1Cube.flatArm37Defs
import Submission.Work.BoseB1Cube.pairSumZeroOfChiScaleZero
import Submission.Work.BoseB1Cube.slidingBoxGates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.flatArm37RowOneBadL` — row 1 of the flat arm on the *bad* region
# `μ·|B(u)| < 12`, with a **holder-free** import cone

## What the lemma says

Under the four explicit diluteness gates `ε₀ ≤ 1`, `ε₀ ≤ (a v)³`, `ε₀ ≤ 10⁶^{-323/166}`
and `ε₀ ≤ 10⁶^{-323/148}`, an admissible `μ`, a sliding box `u ∈ goodSet`, a continuous
in-box state `Φ` on `X n'` with `n' ≥ 4μ|B(u)|`, the **bad** box-size hypothesis
`μ·|B(u)| < 12`, the sharp flat-arm condition `FlatArm37` (`Pc ≤ (37/10)(V²/M₂)·pairSum`)
and the near-flat condition `n₊ < c₀∫Φ²` (`c₀ ≤ 1/2`) are **contradictory**.

## Why (the geometric argument)

The two big-diluteness gates force a *huge* big box: `ε₀ ≤ 10⁶^{-323/166}` with the
diluteness `t = μ(a v)³ ≤ ε₀` gives `μℓ³ = t^{-166/323} ≥ 216000 = 60³`, and
`ε₀ ≤ 10⁶^{-323/148}` gives `μ(ℓd)³ = t^{-148/323} ≥ 13824 = 24³`, i.e. `5·12·μ^{-1/3} ≤ ℓ`
and `2·12·μ^{-1/3} ≤ ℓd`.  Together with `μ|B(u)| < 12` this puts `u` at a corner of the
big box: every side of `B(u)` is at most `12·μ^{-1/3}` while the box is not the full
`(ℓd)`-cube, so every `x ∈ B(u)` has `‖x‖ ≥ ℓ/2` and hence `χ_{B(u)}(x) = chiScale ℓ x = 0`
(`Work.BoseB1Cube.chiScaleZeroSmallBox`).  Therefore `pairSum = 0`
(`Work.BoseB1Cube.pairSumZeroOfChiScaleZero`), and `FlatArm37` forces `Pc ≤ 0`; the pair
count is a sum of squares, so `Pc = 0`, and `boxFlatSqJensen` (`S² − S·∫Φ² ≤ ∫Φ²·Pc`) gives
`S ≤ ∫Φ²`.  The count split `S + n₊ = n'∫Φ²` (`Work.BoseFixB1S.b1sCountSplit`) then yields
`n'∫Φ² < (1 + c₀)∫Φ²`, i.e. `n' < 1 + c₀ ≤ 3/2`, contradicting `n' ≥ 4μ|B(u)| ≥ 4`
(the standing gate `1 ≤ μ|B(u)|`, `Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood`).

## Provenance and the import cone

This is a **verbatim transcription** of the body of

    Work.BoseB1Cube.flatArm37RowOne_bad     (`Submission/Work/BoseB1Cube/cubeSmallWinFlatArm37.lean`)

whose statement is this one with the four gates bundled into the abbreviation
`geoEps (a v)`; the only change is that the gates are taken as hypotheses directly, so that
the (cyclic) helper `geoEps` is not needed.

It must **not** import `cubeSmallWinFlatArm37.lean`: its consumer
`Work.BoseB1Cube.cubeSmallWinFlatArm37Lower` (`Submission/Work/BoseB1Cube/cubeSmallWinFlatArm37Lower.lean`)
imports *this* file, and `cubeSmallWinFlatArm37.lean`'s cone contains
`flatArm37RowOneGood → cubeFlatArm_holds → … → cubeSmallNArb12ExHolds`, the holder of the
parent node — an import cycle.  Hence the file imports only the pieces the *bad* case needs
(the good case needs the pairing payout instead), and the four helpers of
`cubeSmallWinFlatArm37.lean` that the argument uses (`mu_ell_cube_ge_big`,
`mu_ellD_cube_ge_big`, `mul_rpow_neg_third_le_of_cube`, `rpow_323_166`, `rpow_323_148`) are
re-supplied here as `private` lemmas.
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

/-! ## 1. The diluteness arithmetic (`private` copies of the corridor lemmas) -/

private lemma rpow_323_166 : (((1000000 : ℝ)) ^ (-(323 / 166 : ℝ))) ^ (-(166 / 323 : ℝ))
    = 1000000 := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1000000)]
  norm_num

private lemma rpow_323_148 : (((1000000 : ℝ)) ^ (-(323 / 148 : ℝ))) ^ (-(148 / 323 : ℝ))
    = 1000000 := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1000000)]
  norm_num

/-- `μ ℓ³ ≥ 216000` at the small diluteness `μa³ ≤ ε₀ ≤ 10⁶^{-323/166}`. -/
private lemma mu_ell_cube_ge_big {a μ ε₀ : ℝ} (ha : 0 < a) (hμ : 0 < μ) (hdil : μ * a ^ 3 ≤ ε₀)
    (hε : ε₀ ≤ (1000000 : ℝ) ^ (-(323 / 166 : ℝ))) :
    216000 ≤ μ * Work.BoseBox.sideAt μ a ^ 3 := by
  have hεpos : 0 < ε₀ := lt_of_lt_of_le (mul_pos hμ (pow_pos ha 3)) hdil
  have h1 : (1000000 : ℝ) ≤ ε₀ ^ (-(166 / 323 : ℝ)) := by
    have h2 := Real.rpow_le_rpow_of_nonpos hεpos hε (by norm_num : (-(166 / 323 : ℝ)) ≤ 0)
    rwa [rpow_323_166] at h2
  have h3 : μ * Work.BoseBox.sideAt μ a ^ 3 = (μ * a ^ 3) ^ (-(166 / 323 : ℝ)) := by
    rw [Work.BoseFixB1.mu_ell_cube_eq ha hμ]
    simp only [Work.BoseBox.fsXp]
    norm_num
  rw [h3]
  calc (216000 : ℝ) ≤ 1000000 := by norm_num
    _ ≤ ε₀ ^ (-(166 / 323 : ℝ)) := h1
    _ ≤ (μ * a ^ 3) ^ (-(166 / 323 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hμ (pow_pos ha 3)) hdil (by norm_num)

/-- `μ (ℓd)³ ≥ 13824` at the small diluteness `μa³ ≤ ε₀ ≤ 10⁶^{-323/148}`. -/
private lemma mu_ellD_cube_ge_big {a μ ε₀ : ℝ} (ha : 0 < a) (hμ : 0 < μ) (hdil : μ * a ^ 3 ≤ ε₀)
    (hε : ε₀ ≤ (1000000 : ℝ) ^ (-(323 / 148 : ℝ))) :
    13824 ≤ μ * ((Work.BoseBox.paramsAt μ a).d * Work.BoseBox.sideAt μ a) ^ 3 := by
  have hεpos : 0 < ε₀ := lt_of_lt_of_le (mul_pos hμ (pow_pos ha 3)) hdil
  have h1 : (1000000 : ℝ) ≤ ε₀ ^ (-(148 / 323 : ℝ)) := by
    have h2 := Real.rpow_le_rpow_of_nonpos hεpos hε (by norm_num : (-(148 / 323 : ℝ)) ≤ 0)
    rwa [rpow_323_148] at h2
  have h2 : μ * ((Work.BoseBox.paramsAt μ a).d * Work.BoseBox.sideAt μ a) ^ 3
      = (μ * a ^ 3) ^ (-(148 / 323 : ℝ)) := by
    rw [Work.BoseFixB1.mu_d_mul_sideAt_cube_eq ha hμ]
    simp only [Work.BoseBox.fsXp]
    norm_num
  rw [h2]
  calc (13824 : ℝ) ≤ 1000000 := by norm_num
    _ ≤ ε₀ ^ (-(148 / 323 : ℝ)) := h1
    _ ≤ (μ * a ^ 3) ^ (-(148 / 323 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hμ (pow_pos ha 3)) hdil (by norm_num)

/-- **From a cube bound to the `μ^{-1/3}`-form.**  If `c³ ≤ μ ℓ³` (`0 ≤ c`, `0 < μ`, `0 < ℓ`)
then `c μ^{-1/3} ≤ ℓ`. -/
private lemma mul_rpow_neg_third_le_of_cube {c μ ℓ : ℝ} (hμ : 0 < μ) (hℓ : 0 < ℓ) (hc : 0 ≤ c)
    (h : c ^ 3 ≤ μ * ℓ ^ 3) : c * μ ^ (-(1 / 3) : ℝ) ≤ ℓ := by
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have h3 : (c ^ 3) ^ ((1 : ℝ) / 3) ≤ (μ * ℓ ^ 3) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) h (by norm_num)
  have hc3 : (c ^ 3) ^ ((1 : ℝ) / 3) = c := by
    rw [← Real.rpow_natCast c 3, ← Real.rpow_mul hc]
    norm_num
  have hμℓ3 : (μ * ℓ ^ 3) ^ ((1 : ℝ) / 3) = μ ^ ((1 : ℝ) / 3) * ℓ := by
    rw [Real.mul_rpow hμ.le (by positivity)]
    congr 1
    rw [← Real.rpow_natCast ℓ 3, ← Real.rpow_mul hℓ.le]
    norm_num
  have hc_le : c ≤ μ ^ ((1 : ℝ) / 3) * ℓ := by rw [← hμℓ3, ← hc3]; exact h3
  have h1 : μ ^ ((1 : ℝ) / 3) * μ ^ (-(1 / 3) : ℝ) = 1 := by
    rw [← Real.rpow_add hμ, show (1 : ℝ) / 3 + (-(1 / 3)) = 0 by norm_num, Real.rpow_zero]
  calc c * μ ^ (-(1 / 3) : ℝ)
      ≤ (μ ^ ((1 : ℝ) / 3) * ℓ) * μ ^ (-(1 / 3) : ℝ) :=
        mul_le_mul_of_nonneg_right hc_le (Real.rpow_nonneg hμ.le _)
    _ = ℓ := by rw [show (μ ^ ((1 : ℝ) / 3) * ℓ) * μ ^ (-(1 / 3) : ℝ)
          = (μ ^ ((1 : ℝ) / 3) * μ ^ (-(1 / 3) : ℝ)) * ℓ by ring, h1, one_mul]

/-! ## 2. The bad case of the dichotomy: `μ·|B(u)| < 12`

If the box volume is this small, the sliding box is a sliver at a corner of the big box, so
`chiScale ℓ` (and hence the whole kernel `wSmallPair`) vanishes on it.  With `InBox` this makes
`pairSum = 0`, and `FlatArm37` then forces `Pc ≤ 0`; `boxFlatSqJensen` gives `S ≤ ∫Φ²`, and the
count split `S + n₊ = n'∫Φ²` contradicts `n₊ < c₀∫Φ²` because `n' ≥ 4μ|B(u)| ≥ 4`. -/

theorem flatArm37RowOneBadL {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hav : 0 < _root_.BoseGases.a v)
    {ε₀ c₀ : ℝ} (hε₀ : 0 < ε₀) (hε1 : ε₀ ≤ 1) (hεa : ε₀ ≤ (_root_.BoseGases.a v) ^ 3)
    (hεA : ε₀ ≤ (1000000 : ℝ) ^ (-(323 / 166 : ℝ)))
    (hεB : ε₀ ≤ (1000000 : ℝ) ^ (-(323 / 148 : ℝ)))
    (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1 / 2)
    {μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ)
    (hsmall : μ * Work.BoseFixB1B.PBBV v μ u < 12)
    {n' : ℕ} (h4 : 4 * μ * Work.BoseFixB1B.PBBV v μ u ≤ (n' : ℝ))
    {Φ : Submission.BoseGases.X n' → ℝ} (hcont : Continuous Φ)
    (hIn : Work.BoseFixB1B.InBox v μ u Φ)
    (hFlat : Work.BoseB1Cube.FlatArm37 v h μ n' Φ u)
    (hQ : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
        (Work.BoseFixB1.bV v μ u) Φ
      < c₀ * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2)) :
    False := by
  classical
  have hμ : 0 < μ := hAdm.1
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ := hAdm.2.1
  have hℓ : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1B.PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hd1 : Work.BoseFixB1B.PBd v μ ≤ 1 := Work.BoseB1Cube.adm_d_le_one hAdm hε1
  have hℓd : 0 < Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ := mul_pos hℓ hd
  have hdil1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hdil hε1
  -- the two cubic gates
  have hcube1 : (60 : ℝ) ^ 3 ≤ μ * (Work.BoseFixB1B.PBℓ v μ) ^ 3 := by
    have hthis := mu_ell_cube_ge_big (a := _root_.BoseGases.a v) (μ := μ) (ε₀ := ε₀) hav hμ hdil hεA
    have hEq : Work.BoseBox.sideAt μ (_root_.BoseGases.a v) = Work.BoseFixB1B.PBℓ v μ := rfl
    rw [hEq] at hthis
    norm_num at hthis ⊢
    exact hthis
  have hcube2 : (24 : ℝ) ^ 3
      ≤ μ * (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ) ^ 3 := by
    have hthis := mu_ellD_cube_ge_big (a := _root_.BoseGases.a v) (μ := μ) (ε₀ := ε₀) hav hμ hdil hεB
    simp only [Work.BoseFixB1B.PBℓ, Work.BoseFixB1B.PBd] at hthis ⊢
    rw [mul_comm (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))] at hthis
    norm_num at hthis ⊢
    exact hthis
  have hbig : 5 * 12 * μ ^ (-(1 / 3) : ℝ) ≤ Work.BoseFixB1B.PBℓ v μ := by
    have h := mul_rpow_neg_third_le_of_cube (c := (60 : ℝ)) hμ hℓ (by norm_num) hcube1
    have h5 : (5 : ℝ) * 12 = 60 := by norm_num
    rw [h5]
    exact h
  have hshort : 2 * 12 * μ ^ (-(1 / 3) : ℝ)
      ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ := by
    have h := mul_rpow_neg_third_le_of_cube (c := (24 : ℝ)) hμ hℓd (by norm_num) hcube2
    have h5 : (2 : ℝ) * 12 = 24 := by norm_num
    rw [h5]
    exact h
  have hreg : μ ^ (-(1 / 3) : ℝ) ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ := by
    have h1 : μ ^ (-1 / 3 : ℝ) ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ :=
      Work.BoseFixB1S.inv_third_le_of_one_le_mul_cube hμ hℓd.le (by linarith [hcube2])
    simpa only [Work.BoseFixB1S.rpow_neg_third_eq μ] using h1
  -- `chiScale ℓ` vanishes on the box
  have hzero : ∀ x ∈ Submission.BoseGases.dlBox (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBd v μ) u, Submission.BoseGases.chiScale (Work.BoseFixB1B.PBℓ v μ) x = 0 :=
    chiScaleZeroSmallBox (K := 12) hℓ hd hd1 hμ (by norm_num) hreg hshort hbig hu
      (le_of_lt hsmall)
  -- the pairing vanishes
  have hpair : Work.BoseFixB1.pairSum v (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBd v μ) u Φ = 0 :=
    pairSumZeroOfChiScaleZero (h := h) (M := Work.BoseFixB1B.PBM v μ) (u := u) hzero hIn
  -- the pair count is nonnegative and `FlatArm37` forces it to vanish
  have hPc0 : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1B.PBBV v μ u)
      (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Φ := by
    rw [Work.BoseFixB1S.boxPairCount]
    exact Finset.sum_nonneg (fun p _ => integral_nonneg (fun x => sq_nonneg _))
  have hFlat' : Work.BoseFixB1S.boxPairCount (Work.BoseFixB1B.PBBV v μ u)
      (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Φ ≤ 0 := by
    have hh := hFlat
    rw [Work.BoseB1Cube.FlatArm37] at hh
    rw [hpair, mul_zero] at hh
    exact hh
  have hPc : Work.BoseFixB1S.boxPairCount (Work.BoseFixB1B.PBBV v μ u)
      (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Φ = 0 :=
    le_antisymm hFlat' hPc0
  -- the counts
  have hVpos : 0 < Work.BoseFixB1B.PBBV v μ u := Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hcount : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1B.PBBV v μ u)
        (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Φ
      + Work.BoseFixB1S.boxQCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBB v μ u) Φ
      = (n' : ℝ) * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2) :=
    Work.BoseFixB1S.b1sCountSplit hℓ hVpos
      (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
      (Work.SmallBoxSliding.boxMass_eq_measureReal _ _ _)
      (Work.SmallBoxSliding.dlBox_subset_acube _ _ _) hcont hIn
  have hJensen : (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1B.PBBV v μ u)
        (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Φ) ^ 2
      - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
          (Work.BoseFixB1B.PBB v μ u) Φ
        * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2)
      ≤ (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2)
        * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBB v μ u) Φ :=
    Work.BoseFixB1S.boxFlatSqJensen hℓ hVpos
      (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
      (Work.SmallBoxSliding.boxMass_eq_measureReal _ _ _)
      (Work.SmallBoxSliding.dlBox_subset_acube _ _ _) hcont
  have hS0 : 0 ≤ Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1B.PBBV v μ u)
      (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Φ := by
    rw [Work.BoseFixB1S.boxFlatCount]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hQ0 : 0 ≤ Work.BoseFixB1S.boxQCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBB v μ u) Φ := by
    rw [Work.BoseFixB1S.boxQCount]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hJ0 : 0 ≤ ∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  -- the flat count is at most the norm
  have hSleJ : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBB v μ u) Φ
      ≤ ∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2 := by
    have h := hJensen
    rw [hPc, mul_zero] at h
    rcases eq_or_lt_of_le hS0 with hS | hS
    · rw [← hS] at h ⊢
      exact hJ0
    · have h2 : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1B.PBBV v μ u)
          (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u) Φ
          * Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBB v μ u) Φ
          ≤ Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
              (Work.BoseFixB1B.PBB v μ u) Φ
            * ∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2 := by
        nlinarith [h]
      exact le_of_mul_le_mul_left h2 hS
  -- the excited count is the target's `cnPlusBoxInd`
  have hQ' : Work.BoseFixB1S.boxQCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
      (Work.BoseFixB1B.PBB v μ u) Φ
      < c₀ * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2) := hQ
  rcases le_or_gt (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2) 0 with
    hJle | hJpos
  · have hJeq : (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2) = 0 :=
      le_antisymm hJle hJ0
    have : Work.BoseFixB1S.boxQCount (Work.BoseFixB1B.PBBV v μ u) (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBB v μ u) Φ < 0 := by rw [hJeq, mul_zero] at hQ'; exact hQ'
    linarith [hQ0, this]
  · have hlt : (n' : ℝ) * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ),
        (Φ x) ^ 2)
        < (1 + c₀) * (∫ x in Submission.BoseGases.abox n' (Work.BoseFixB1B.PBℓ v μ), (Φ x) ^ 2) := by
      rw [← hcount]
      nlinarith [hSleJ, hQ']
    have hn' : (n' : ℝ) < 1 + c₀ := lt_of_mul_lt_mul_right hlt hJpos.le
    have hge4 : (4 : ℝ) ≤ (n' : ℝ) := by
      have h1 : 1 ≤ μ * Work.BoseFixB1B.PBBV v μ u :=
        Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood (a := _root_.BoseGases.a v) hav hμ hdil1 hu
      linarith [h4, h1]
    linarith [hn', hc₀1, hge4]

end Work.BoseB1Cube
