import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Filter

/-- `log` grows more slowly than any positive power: for any `c a : ℝ` and `0 < b`,
eventually `c * (log L)^a ≤ L^b`. -/
private lemma eventually_const_mul_log_rpow_le_rpow (c a b : ℝ) (hb : 0 < b) :
    ∀ᶠ L : ℝ in Filter.atTop, c * (Real.log L) ^ a ≤ L ^ b := by
  rcases lt_or_ge c 0 with hc | hc
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with L hL
    have h1 : 0 ≤ (Real.log L) ^ a := Real.rpow_nonneg (Real.log_nonneg hL) a
    have h2 : 0 ≤ L ^ b := Real.rpow_nonneg (by linarith) b
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hc.le h1) h2
  · have h := (isLittleO_log_rpow_rpow_atTop a hb).const_mul_left c
    filter_upwards [h.eventuallyLE, Filter.eventually_ge_atTop (1 : ℝ)] with L hL hL1
    rw [Real.norm_of_nonneg (mul_nonneg hc (Real.rpow_nonneg (Real.log_nonneg hL1) a)),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) b)] at hL
    exact hL

/-- Specialisation of `eventually_const_mul_log_rpow_le_rpow` to the first power of `log`. -/
private lemma eventually_const_mul_log_le_rpow (c b : ℝ) (hb : 0 < b) :
    ∀ᶠ L : ℝ in Filter.atTop, c * Real.log L ≤ L ^ b := by
  have h := eventually_const_mul_log_rpow_le_rpow c 1 b hb
  filter_upwards [h] with L hL
  rwa [Real.rpow_one] at hL

/-- `log 4 + 2 log L ≤ (1/2) L^{5/4}` eventually. -/
private lemma eventually_log4_add_two_log_le :
    ∀ᶠ L : ℝ in Filter.atTop, Real.log 4 + 2 * Real.log L ≤ (1 / 2) * L ^ (5 / 4 : ℝ) := by
  have h1 : ∀ᶠ L : ℝ in Filter.atTop, 8 * Real.log L ≤ L ^ (5 / 4 : ℝ) :=
    eventually_const_mul_log_le_rpow 8 (5 / 4) (by norm_num)
  have h2 : ∀ᶠ L : ℝ in Filter.atTop, 4 * Real.log 4 ≤ L ^ (5 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 4)).eventually_ge_atTop (4 * Real.log 4)
  filter_upwards [h1, h2] with L h1 h2
  linarith

/-- For `b < c`, eventually `L^b` is at most half of `L^c`. -/
private lemma eventually_rpow_le_half_rpow {b c : ℝ} (hbc : b < c) :
    ∀ᶠ L : ℝ in Filter.atTop, L ^ b ≤ (1 / 2) * L ^ c := by
  have hd : 0 < c - b := sub_pos.mpr hbc
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
      (tendsto_rpow_atTop hd).eventually_ge_atTop (2 : ℝ)] with L hL hL2
  have hpos : 0 < L ^ b := Real.rpow_pos_of_pos hL b
  have hsplit : L ^ c = L ^ b * L ^ (c - b) := by
    rw [← Real.rpow_add hL]; ring_nf
  rw [hsplit]
  nlinarith [hpos, hL2]

theorem ztNumeric_eventually :
    (∀ᶠ L in Filter.atTop, Real.log 4 + 2 * Real.log L + L ^ (1 / 10 : ℝ) ≤ L ^ (5 / 4 : ℝ)) ∧
    (∀ᶠ L in Filter.atTop,
      2 * L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) + 17 ≤ Real.exp (L ^ (5 / 4 : ℝ))) ∧
    (∀ᶠ L in Filter.atTop, Real.log 2 ≤ (3 / 4) * Real.log L) ∧
    (∀ᶠ L in Filter.atTop, Real.log 3 ≤ L ^ (5 / 4 : ℝ)) ∧
    (∀ᶠ L in Filter.atTop, 2 * (Real.log L) ^ (1 / 3 : ℝ) ≤ L ^ (1 / 15 : ℝ)) := by
  have hB : ∀ᶠ L : ℝ in Filter.atTop, L ^ (1 / 10 : ℝ) ≤ (1 / 2) * L ^ (5 / 4 : ℝ) :=
    eventually_rpow_le_half_rpow (by norm_num : (1 : ℝ) / 10 < 5 / 4)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [eventually_log4_add_two_log_le, hB] with L hA hB
    linarith
  · -- `exp (L^{5/4})` dominates the polynomial-exponential factor `2 L^2 exp (L^{1/10}) + 17`.
    have hbig : ∀ᶠ L : ℝ in Filter.atTop, (34 : ℝ) ≤ Real.exp (L ^ (5 / 4 : ℝ)) :=
      (Real.tendsto_exp_atTop.comp
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 4))).eventually_ge_atTop 34
    filter_upwards [eventually_log4_add_two_log_le, hB, hbig,
      Filter.eventually_gt_atTop (0 : ℝ)] with L hA hHalf hbig hL
    have hlog : Real.log (4 * L ^ 2) = Real.log 4 + 2 * Real.log L := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : L ^ 2 ≠ 0), Real.log_pow]
      norm_num
    have h4pos : (0 : ℝ) < 4 * L ^ 2 := by positivity
    have hlogA : Real.log (4 * L ^ 2) ≤ (1 / 2) * L ^ (5 / 4 : ℝ) := by rw [hlog]; exact hA
    have hle1 : 4 * L ^ 2 ≤ Real.exp ((1 / 2) * L ^ (5 / 4 : ℝ)) :=
      (Real.log_le_iff_le_exp h4pos).mp hlogA
    have hDge : (1 / 2) * L ^ (5 / 4 : ℝ) ≤ L ^ (5 / 4 : ℝ) - L ^ (1 / 10 : ℝ) := by linarith
    have hle2 : 4 * L ^ 2 ≤ Real.exp (L ^ (5 / 4 : ℝ) - L ^ (1 / 10 : ℝ)) :=
      le_trans hle1 (Real.exp_le_exp.mpr hDge)
    have hexp : Real.exp (L ^ (5 / 4 : ℝ))
        = Real.exp (L ^ (1 / 10 : ℝ)) * Real.exp (L ^ (5 / 4 : ℝ) - L ^ (1 / 10 : ℝ)) := by
      rw [← Real.exp_add,
        show L ^ (1 / 10 : ℝ) + (L ^ (5 / 4 : ℝ) - L ^ (1 / 10 : ℝ)) = L ^ (5 / 4 : ℝ) by ring]
    have hstep : 2 * L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ))
        ≤ (1 / 2) * Real.exp (L ^ (5 / 4 : ℝ)) := by
      rw [hexp]
      nlinarith [hle2, Real.exp_pos (L ^ (1 / 10 : ℝ))]
    have h17 : 17 ≤ (1 / 2) * Real.exp (L ^ (5 / 4 : ℝ)) := by linarith
    linarith
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop ((4 / 3) * Real.log 2)] with L hL
    linarith
  · exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 4)).eventually_ge_atTop (Real.log 3)
  · exact eventually_const_mul_log_rpow_le_rpow 2 (1 / 3) (1 / 15) (by norm_num)

end Work.BMF.liouville
