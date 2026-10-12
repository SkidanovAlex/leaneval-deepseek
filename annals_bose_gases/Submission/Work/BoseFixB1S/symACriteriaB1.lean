import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseFixB1.KH.SymAMoments
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

noncomputable section

open scoped Real Topology

set_option maxHeartbeats 1600000

/-! ## The scalar criteria, first at a generic diluteness `t`

At FS's parameters `fsParams t` we have `s = t^{1/323}`, `d = s⁶ = t^{6/323}`,
`ε_T = t^{(23/4)/323}`.  If `t ≤ ε₀ = δ^{323}` with `δ = symASmallScale` then
`s ≤ δ`, and `δ` was chosen so that each of the four criteria follows from
`s ≤ δ` with no further input.  This is the self-contained re-derivation of
`Work.BoseFixB1S.oneBodyB1.mixCriteriaArith` required here (that module carries
a `sorry` elsewhere in its import cone and is disallowed). -/

/-- **The scalar criteria at FS's parameter block**, for a diluteness `t` below the explicit
threshold `symAEps0 = δ^{323}`. -/
lemma symACriteriaArith {t : ℝ} (ht0 : 0 < t) (ht : t ≤ Work.BoseFixB1.KH.symAEps0) :
    0 < (Work.BoseBox.fsParams t).s ∧ (Work.BoseBox.fsParams t).d ≤ 1 / 2 ∧
    (Work.BoseBox.fsParams t).eT ≤ 1 / 2 ∧
    Work.BoseFixB1.KH.symAMom1 ≤ ((Work.BoseBox.fsParams t).s)⁻¹ ∧
    8 * Work.BoseFixB1.KH.symAMom2 ≤ (1 - (Work.BoseBox.fsParams t).d) ^ 2 *
      (((Work.BoseBox.fsParams t).s)⁻¹) ^ 2 := by
  set δ := Work.BoseFixB1.KH.symASmallScale with hδ
  have hδpos : 0 < δ := Work.BoseFixB1.KH.symASmallScale_pos
  have hδhalf : δ ≤ 1 / 2 := Work.BoseFixB1.KH.symASmallScale_le_half
  have hδ1 : δ ≤ 1 := by linarith
  have hM1n : 0 ≤ Work.BoseFixB1.KH.symAMom1 := Work.BoseFixB1.KH.symAMom1_nonneg
  have hM2n : 0 ≤ Work.BoseFixB1.KH.symAMom2 := Work.BoseFixB1.KH.symAMom2_nonneg
  have heps : Work.BoseFixB1.KH.symAEps0 = δ ^ (323 : ℝ) := by
    rw [Work.BoseFixB1.KH.symAEps0, ← hδ]
  have ht' : t ≤ δ ^ (323 : ℝ) := by rwa [heps] at ht
  have hspos : 0 < (Work.BoseBox.fsParams t).s := by
    show 0 < Work.BoseBox.fsXp t 1
    exact Work.BoseBox.fsXp_pos ht0
  have hsle : (Work.BoseBox.fsParams t).s ≤ δ := by
    show Work.BoseBox.fsXp t 1 ≤ δ
    rw [Work.BoseBox.fsXp]
    calc t ^ ((1 : ℝ) / 323) ≤ (δ ^ (323 : ℝ)) ^ ((1 : ℝ) / 323) :=
          Real.rpow_le_rpow ht0.le ht' (by norm_num)
      _ = δ ^ ((323 : ℝ) * ((1 : ℝ) / 323)) := (Real.rpow_mul hδpos.le 323 ((1 : ℝ) / 323)).symm
      _ = δ := by rw [show (323 : ℝ) * ((1 : ℝ) / 323) = 1 by norm_num, Real.rpow_one]
  have hs1 : (Work.BoseBox.fsParams t).s ≤ 1 := by linarith
  have hdle : (Work.BoseBox.fsParams t).d ≤ 1 / 2 := by
    show Work.BoseBox.fsXp t 6 ≤ 1 / 2
    rw [Work.BoseBox.fsXp]
    calc t ^ ((6 : ℝ) / 323) ≤ (δ ^ (323 : ℝ)) ^ ((6 : ℝ) / 323) :=
          Real.rpow_le_rpow ht0.le ht' (by norm_num)
      _ = δ ^ ((323 : ℝ) * ((6 : ℝ) / 323)) := (Real.rpow_mul hδpos.le 323 ((6 : ℝ) / 323)).symm
      _ = δ ^ (6 : ℝ) := by rw [show (323 : ℝ) * ((6 : ℝ) / 323) = 6 by norm_num]
      _ ≤ δ := Real.rpow_le_self_of_le_one hδpos.le hδ1 (by norm_num)
      _ ≤ 1 / 2 := hδhalf
  have heTle : (Work.BoseBox.fsParams t).eT ≤ 1 / 2 := by
    show Work.BoseBox.fsXp t (23 / 4) ≤ 1 / 2
    rw [Work.BoseBox.fsXp]
    calc t ^ (((23 : ℝ) / 4) / 323) ≤ (δ ^ (323 : ℝ)) ^ (((23 : ℝ) / 4) / 323) :=
          Real.rpow_le_rpow ht0.le ht' (by norm_num)
      _ = δ ^ ((323 : ℝ) * (((23 : ℝ) / 4) / 323)) :=
          (Real.rpow_mul hδpos.le 323 (((23 : ℝ) / 4) / 323)).symm
      _ = δ ^ ((23 : ℝ) / 4) := by
          rw [show (323 : ℝ) * (((23 : ℝ) / 4) / 323) = (23 : ℝ) / 4 by norm_num]
      _ ≤ δ := Real.rpow_le_self_of_le_one hδpos.le hδ1 (by norm_num)
      _ ≤ 1 / 2 := hδhalf
  refine ⟨hspos, hdle, heTle, ?_, ?_⟩
  · -- `M₁ ≤ 1/s`
    have h1 : δ * (Work.BoseFixB1.KH.symAMom1 + 1) ≤ 1 := by
      have hpos : 0 < Work.BoseFixB1.KH.symAMom1 + 1 := by linarith
      calc δ * (Work.BoseFixB1.KH.symAMom1 + 1)
          ≤ (Work.BoseFixB1.KH.symAMom1 + 1)⁻¹ * (Work.BoseFixB1.KH.symAMom1 + 1) :=
            mul_le_mul_of_nonneg_right Work.BoseFixB1.KH.symASmallScale_le_mom1 hpos.le
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    have h2 : Work.BoseFixB1.KH.symAMom1 * (Work.BoseBox.fsParams t).s ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hsle
        (by linarith : (0 : ℝ) ≤ Work.BoseFixB1.KH.symAMom1 + 1)
      nlinarith [h1, this, hspos, hM1n]
    rw [← one_div, le_div_iff₀ hspos]
    linarith
  · -- `8M₂ ≤ (1−d)²/s²`
    have h1 : δ * (32 * Work.BoseFixB1.KH.symAMom2 + 1) ≤ 1 := by
      have hpos : 0 < 32 * Work.BoseFixB1.KH.symAMom2 + 1 := by linarith
      calc δ * (32 * Work.BoseFixB1.KH.symAMom2 + 1)
          ≤ (32 * Work.BoseFixB1.KH.symAMom2 + 1)⁻¹ * (32 * Work.BoseFixB1.KH.symAMom2 + 1) :=
            mul_le_mul_of_nonneg_right Work.BoseFixB1.KH.symASmallScale_le_mom2 hpos.le
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    have h2 : Work.BoseFixB1.KH.symAMom2 * (Work.BoseBox.fsParams t).s ≤ 1 / 32 := by
      have hpos : (0 : ℝ) ≤ 32 * Work.BoseFixB1.KH.symAMom2 + 1 := by linarith
      have := mul_le_mul_of_nonneg_right hsle hpos
      nlinarith [h1, this, hspos, hM2n]
    have hss : (Work.BoseBox.fsParams t).s ^ 2 ≤ (Work.BoseBox.fsParams t).s := by
      nlinarith [hspos, hs1]
    have h3 : 8 * Work.BoseFixB1.KH.symAMom2 * (Work.BoseBox.fsParams t).s ^ 2 ≤ 1 / 4 := by
      have h4 : Work.BoseFixB1.KH.symAMom2 * (Work.BoseBox.fsParams t).s ^ 2
          ≤ Work.BoseFixB1.KH.symAMom2 * (Work.BoseBox.fsParams t).s :=
        mul_le_mul_of_nonneg_left hss hM2n
      have h5 : (8 : ℝ) * (Work.BoseFixB1.KH.symAMom2 * (Work.BoseBox.fsParams t).s ^ 2)
          ≤ 8 * (Work.BoseFixB1.KH.symAMom2 * (Work.BoseBox.fsParams t).s) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
      linarith [h2, h5]
    have h5 : (1 / 4 : ℝ) ≤ (1 - (Work.BoseBox.fsParams t).d) ^ 2 := by
      nlinarith [hdle]
    have h6 : 0 < (Work.BoseBox.fsParams t).s ^ 2 := by positivity
    have h7 : 8 * Work.BoseFixB1.KH.symAMom2 * (Work.BoseBox.fsParams t).s ^ 2
        * ((Work.BoseBox.fsParams t).s ^ 2)⁻¹
        ≤ (1 - (Work.BoseBox.fsParams t).d) ^ 2 * ((Work.BoseBox.fsParams t).s ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_trans h3 h5) (by positivity)
    have h8 : 8 * Work.BoseFixB1.KH.symAMom2 * (Work.BoseBox.fsParams t).s ^ 2
        * ((Work.BoseBox.fsParams t).s ^ 2)⁻¹ = 8 * Work.BoseFixB1.KH.symAMom2 := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h6), mul_one]
    rw [← h8]
    convert h7 using 2
    rw [inv_pow]

/-- The four scalar criteria of the two-cut symbol comparison at FS's parameter block
`paramsAt μ a = fsParams (μa³)`, for diluteness `μa³` below the explicit threshold
`symAEps0 = δ^323` (`δ = min (1/2) (min (M₁+1)⁻¹ (32M₂+1)⁻¹)`, `M₁, M₂` the two bump moments of
`Work.BoseFixB1.KH.SymAMoments`): `s > 0`, `d = s⁶ ≤ 1/2`, `eT = s^{23/4} ≤ 1/2`, `M₁ ≤ 1/s`
and `8M₂ ≤ (1−d)²(1/s)²`.  (`symAMom1`, `symAMom2` are definitionally the two integrals
`(2π)⁻³∫ profHat²‖t‖`, `(2π)⁻³∫ profHat²‖t‖²`.)

DISALLOWED IMPORTS (both modules contain `sorry`): `Submission.Work.BoseFixB1.KH.fsParams_small_criteria`
and `Submission.Work.BoseFixB1S.oneBodyB1.mixInputB1`.  The arithmetic must be re-derived
self-containedly from `symASmallScale`/`symAEps0`/`Work.BoseBox.fsXp` via `Real.rpow_mul`,
`Real.rpow_le_rpow`, `Real.rpow_le_self_of_le_one`, ... (an existing sorry-free derivation you may
consult and adapt is `Work.BoseFixB1S.oneBodyB1.mixCriteriaArith` in
`Submission/Work/BoseFixB1S/oneBodyB1/mixInputB1.lean`, whose statement is your generic-`t` version). -/
lemma symACriteriaB1 {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (hd : μ * a ^ 3 ≤ Work.BoseFixB1.KH.symAEps0) :
    0 < (Work.BoseBox.paramsAt μ a).s ∧ (Work.BoseBox.paramsAt μ a).d ≤ 1 / 2 ∧
    (Work.BoseBox.paramsAt μ a).eT ≤ 1 / 2 ∧
    Work.BoseFixB1.KH.symAMom1 ≤ ((Work.BoseBox.paramsAt μ a).s)⁻¹ ∧
    8 * Work.BoseFixB1.KH.symAMom2 ≤ (1 - (Work.BoseBox.paramsAt μ a).d) ^ 2 *
      (((Work.BoseBox.paramsAt μ a).s)⁻¹) ^ 2 := by
  have h := symACriteriaArith (t := μ * a ^ 3) (mul_pos hμ (pow_pos ha 3)) hd
  show 0 < (Work.BoseBox.fsParams (μ * a ^ 3)).s ∧
    (Work.BoseBox.fsParams (μ * a ^ 3)).d ≤ 1 / 2 ∧
    (Work.BoseBox.fsParams (μ * a ^ 3)).eT ≤ 1 / 2 ∧
    Work.BoseFixB1.KH.symAMom1 ≤ ((Work.BoseBox.fsParams (μ * a ^ 3)).s)⁻¹ ∧
    8 * Work.BoseFixB1.KH.symAMom2 ≤ (1 - (Work.BoseBox.fsParams (μ * a ^ 3)).d) ^ 2 *
      (((Work.BoseBox.fsParams (μ * a ^ 3)).s)⁻¹) ^ 2
  exact h

end

end Work.BoseFixB1S
