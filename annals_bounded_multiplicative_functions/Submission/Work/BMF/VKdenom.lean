import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Vinogradov–Korobov denominator

`VKd y = (log y)^{2/3} (log log y)^{1/3}` for `y > e`.

In the Vinogradov–Korobov zero-free region the relevant quantity at ordinate `t` is
`VKd (|t| + 3)`, and the short-interval statement of the paper uses the same shape with
argument `u + T + 3`.  This file fixes the notation and records the elementary
positivity/monotonicity/comparison facts used by the zero-free-region development.
-/

namespace Work.BMF

open Real

/-- The Vinogradov–Korobov denominator shape `(log y)^{2/3}(log log y)^{1/3}`. -/
noncomputable def VKd (y : ℝ) : ℝ :=
  (Real.log y) ^ (2 / 3 : ℝ) * (Real.log (Real.log y)) ^ (1 / 3 : ℝ)

lemma VKd_def (y : ℝ) :
    VKd y = (Real.log y) ^ (2 / 3 : ℝ) * (Real.log (Real.log y)) ^ (1 / 3 : ℝ) := rfl

/-- For `y ≥ 3` (so `log y ≥ 1`) the denominator is strictly positive. -/
lemma VKd_pos {y : ℝ} (hy : 3 ≤ y) : 0 < VKd y := by
  rw [VKd_def]
  have hy0 : 0 < y := by linarith
  have h1 : 1 < Real.log y := by
    rw [Real.lt_log_iff_exp_lt hy0]
    linarith [Real.exp_one_lt_three]
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (Real.log_pos h1) _)

lemma VKd_nonneg {y : ℝ} (hy : 3 ≤ y) : 0 ≤ VKd y := (VKd_pos hy).le

lemma one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
  exact Real.exp_one_lt_three.le

/-- `1 ≤ log y` for `y ≥ 3`. -/
lemma one_le_log {y : ℝ} (hy : 3 ≤ y) : (1 : ℝ) ≤ Real.log y :=
  le_trans one_le_log_three (Real.log_le_log (by norm_num) hy)

/-- **`VKd` is nondecreasing on `[3, ∞)`.** -/
lemma VKd_mono {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) : VKd x ≤ VKd y := by
  rw [VKd_def, VKd_def]
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ Real.log x := one_le_log hx
  have hxy' : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hy1 : 1 ≤ Real.log y := le_trans hx1 hxy'
  have hy0 : 0 < Real.log y := lt_of_lt_of_le zero_lt_one hy1
  have hlogx0 : 0 ≤ Real.log x := le_trans zero_le_one hx1
  have h1 : (Real.log x) ^ (2 / 3 : ℝ) ≤ (Real.log y) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hlogx0 hxy' (by norm_num)
  have h2 : (Real.log (Real.log x)) ^ (1 / 3 : ℝ) ≤
      (Real.log (Real.log y)) ^ (1 / 3 : ℝ) := by
    refine Real.rpow_le_rpow (Real.log_nonneg hx1) ?_ (by norm_num)
    exact Real.log_le_log (by linarith) hxy'
  exact mul_le_mul h1 h2 (Real.rpow_nonneg (Real.log_nonneg hx1) _)
    (Real.rpow_nonneg (le_of_lt hy0) _)

/-- `VKd y ≤ log y` for `y ≥ 3`. -/
lemma VKd_le_log {y : ℝ} (hy : 3 ≤ y) : VKd y ≤ Real.log y := by
  rw [VKd_def]
  set L : ℝ := Real.log y with hL
  have hL1 : 1 ≤ L := by rw [hL]; exact one_le_log hy
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hlogL : Real.log L ≤ L := Real.log_le_self hL0.le
  have hstep : (Real.log L) ^ (1 / 3 : ℝ) ≤ L ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (Real.log_nonneg hL1) hlogL (by norm_num)
  calc L ^ (2 / 3 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ)
      ≤ L ^ (2 / 3 : ℝ) * L ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hL0.le _)
    _ = L := by
        rw [← Real.rpow_add hL0]
        norm_num

/-- `exp 2 ≤ 12`. -/
lemma exp_two_le_twelve : Real.exp 2 ≤ 12 := by
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [h]
  nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]

lemma two_le_log_twelve : (2 : ℝ) ≤ Real.log 12 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 12)]
  exact exp_two_le_twelve

lemma two_thirds_mul_four_thirds_le_three :
    (2 : ℝ) ^ (4 / 3 : ℝ) ≤ 3 := by
  have hcube : ((2 : ℝ) ^ (4 / 3 : ℝ)) ^ 3 ≤ (3 : ℝ) ^ 3 := by
    have h1 : ((2 : ℝ) ^ (4 / 3 : ℝ)) ^ (3 : ℝ) = ((2 : ℝ) ^ (4 / 3 : ℝ)) ^ 3 :=
      Real.rpow_natCast _ 3
    rw [← h1, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by norm_num) hcube

/-- **Doubling bound for the Vinogradov–Korobov denominator.** `VKd (2Y) ≤ 3 VKd Y`
for `Y ≥ 12`. -/
lemma VKd_two_mul_le_three {Y : ℝ} (hY : 12 ≤ Y) : VKd (2 * Y) ≤ 3 * VKd Y := by
  have hY0 : 0 < Y := by linarith
  rw [VKd_def, VKd_def]
  set W : ℝ := Real.log Y with hW
  have hW2 : 2 ≤ W := by
    rw [hW]
    exact le_trans two_le_log_twelve (Real.log_le_log (by norm_num) hY)
  have hW0 : 0 < W := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le_W : Real.log 2 ≤ W := by
    have h : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    linarith
  have hlog2Y : Real.log (2 * Y) = Real.log 2 + W := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hY0), hW]
  set V : ℝ := Real.log 2 + W with hV
  have hVpos : 0 < V := by rw [hV]; linarith
  have hV1 : 1 ≤ V := by rw [hV]; linarith
  have hVle : V ≤ 2 * W := by rw [hV]; linarith
  -- first factor
  have h1 : (Real.log (2 * Y)) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) * W ^ (2 / 3 : ℝ) := by
    rw [hlog2Y, hV, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hW0.le]
    exact Real.rpow_le_rpow (by positivity) hVle (by norm_num)
  -- second factor
  have hloglog : Real.log (Real.log (2 * Y)) = Real.log V := by rw [hlog2Y, hV]
  have hstep2 : Real.log V ≤ 4 * Real.log W := by
    have h2W : Real.log V ≤ Real.log (2 * W) := Real.log_le_log hVpos hVle
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hW0)] at h2W
    have hlogW_ge : Real.log 2 ≤ Real.log W := Real.log_le_log (by norm_num) hW2
    linarith
  have h2 : (Real.log (Real.log (2 * Y))) ^ (1 / 3 : ℝ) ≤
      (4 : ℝ) ^ (1 / 3 : ℝ) * (Real.log W) ^ (1 / 3 : ℝ) := by
    rw [hloglog, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
      (Real.log_nonneg (by linarith : (1 : ℝ) ≤ W))]
    exact Real.rpow_le_rpow (Real.log_nonneg hV1) hstep2 (by norm_num)
  -- product
  have hA : 0 ≤ (2 : ℝ) ^ (2 / 3 : ℝ) * W ^ (2 / 3 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hW0.le _)
  have hB : 0 ≤ (Real.log (Real.log (2 * Y))) ^ (1 / 3 : ℝ) := by
    rw [hloglog]
    exact Real.rpow_nonneg (Real.log_nonneg hV1) _
  have hprod := mul_le_mul h1 h2 hB hA
  refine hprod.trans ?_
  have hcoef : (2 : ℝ) ^ (2 / 3 : ℝ) * (4 : ℝ) ^ (1 / 3 : ℝ) = (2 : ℝ) ^ (4 / 3 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← Real.rpow_natCast 2 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hVKnonneg : 0 ≤ W ^ (2 / 3 : ℝ) * (Real.log W) ^ (1 / 3 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hW0.le _)
      (Real.rpow_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ W)) _)
  calc ((2 : ℝ) ^ (2 / 3 : ℝ) * W ^ (2 / 3 : ℝ)) *
        ((4 : ℝ) ^ (1 / 3 : ℝ) * (Real.log W) ^ (1 / 3 : ℝ))
      = ((2 : ℝ) ^ (2 / 3 : ℝ) * (4 : ℝ) ^ (1 / 3 : ℝ)) *
          (W ^ (2 / 3 : ℝ) * (Real.log W) ^ (1 / 3 : ℝ)) := by ring
    _ = (2 : ℝ) ^ (4 / 3 : ℝ) * (W ^ (2 / 3 : ℝ) * (Real.log W) ^ (1 / 3 : ℝ)) := by
        rw [hcoef]
    _ ≤ 3 * (W ^ (2 / 3 : ℝ) * (Real.log W) ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right two_thirds_mul_four_thirds_le_three hVKnonneg

end Work.BMF
