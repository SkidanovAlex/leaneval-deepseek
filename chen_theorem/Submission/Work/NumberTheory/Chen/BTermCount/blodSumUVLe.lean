import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodUnweightedDefs

namespace Work.NumberTheory.Chen.BTermCount

/-!
# The unweighted `U·V` block sum is `O(x log x)`

The large-conductor large-sieve block sum `blodLSBlockSum` contains the factor
`Σ_{j < blockCount M Y} blodU M j * blodV x M j`, where
`blodU M j = 2 · blockStart M j` and `blodV x M j = (x+2)/blockStart M j + 1`.
This module proves the elementary bound

`Σ_{j < blockCount M Y} blodU M j * blodV x M j ≤ 12 · x · log x`

under the standing hypotheses `1 ≤ M ≤ Y` and `Y ≤ 2 x^{1/3}` (`x ≥ 32`).
The two ingredients are

* a per-block bound `U_j V_j = 2 Q_j (((x+2)/Q_j) + 1) ≤ 2(x+2) + 2 Q_j ≤ 4x`
  (the floor division kills the `x/Q_j`, and `Q_j ≤ Y + M ≤ 2Y ≤ 4x^{1/3} ≤ x/2`);
* a block-count bound `blockCount M Y = Nat.log 2 (Y/M+1) + 1 ≤ 3 log x`
  (from `Y + 1 ≤ x` and `Nat.log 2 x ≤ 2 log x`).

`12 = 4 · 3` is the product of the two constants.
-/

/-- For `x ≥ 32`, `8 · x^{1/3} ≤ x` (from `x^{1/3} ≥ 3`, i.e. `x ≥ 27`). -/
lemma blodSumUV_eight_mul_cbrt_le (x : ℕ) (hx : 32 ≤ x) :
    8 * (x : ℝ) ^ ((1:ℝ)/3) ≤ (x : ℝ) := by
  set c : ℝ := (x : ℝ) ^ ((1:ℝ)/3) with hc
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hc3 : c ^ 3 = (x : ℝ) := by
    rw [hc]
    have h : ((1:ℝ)/3) = ((3:ℕ):ℝ)⁻¹ := by norm_num
    rw [h]
    exact Real.rpow_inv_natCast_pow (le_of_lt hxpos) (by norm_num)
  have hc3le : (3 : ℝ) ≤ c := by
    have h27 : (27 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 27 ≤ x)
    have h1 : (27 : ℝ) ^ ((1:ℝ)/3) ≤ (x : ℝ) ^ ((1:ℝ)/3) :=
      Real.rpow_le_rpow (by norm_num) h27 (by norm_num)
    have h2 : (27 : ℝ) ^ ((1:ℝ)/3) = 3 := by
      rw [show (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    rw [h2] at h1
    rw [hc]; exact h1
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc3le
  have hc2 : 8 ≤ c ^ 2 := by nlinarith
  have h : 8 * c ≤ c ^ 3 := by
    calc 8 * c ≤ c ^ 2 * c := mul_le_mul_of_nonneg_right hc2 (le_of_lt hcpos)
      _ = c ^ 3 := by ring
  linarith [hc3]

/-- `Y + 1 ≤ x` under the hypotheses of `blodSumUVLe`. -/
lemma blodSumUV_Y_add_one_le (x Y : ℕ) (hx : 32 ≤ x)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) : Y + 1 ≤ x := by
  have hxR : (32 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h8 := blodSumUV_eight_mul_cbrt_le x hx
  have h4 : 4 * (x : ℝ) ^ ((1:ℝ)/3) ≤ (x : ℝ) := by linarith
  have hhalf : 2 * (x : ℝ) ^ ((1:ℝ)/3) ≤ (x : ℝ) / 2 := by linarith
  have hx2 : (2 : ℝ) ≤ (x : ℝ) := by linarith
  have hYlt : (Y : ℝ) < (x : ℝ) := by linarith
  have : Y < x := by exact_mod_cast hYlt
  omega

/-- The number of dyadic blocks is at most `3 log x`. -/
lemma blodSumUV_blockCount_le (x M Y : ℕ) (hx : 32 ≤ x) (hYx : Y + 1 ≤ x) :
    ((blockCount M Y : ℕ) : ℝ) ≤ 3 * Real.log (x : ℝ) := by
  have hx1 : 1 ≤ x := by omega
  have hYM : Y / M + 1 ≤ x := by
    have h1 : Y / M ≤ Y := Nat.div_le_self Y M
    omega
  have hlog : ((Nat.log 2 (Y / M + 1) : ℕ) : ℝ) ≤ ((Nat.log 2 x : ℕ) : ℝ) := by
    exact_mod_cast Nat.log_mono_right hYM
  have hlogb : ((Nat.log 2 x : ℕ) : ℝ) ≤ Real.logb 2 (x : ℝ) := Real.natLog_le_logb x 2
  have hlogbdef : Real.logb 2 (x : ℝ) = Real.log (x : ℝ) / Real.log 2 := rfl
  have hlogx_nonneg : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx1)
  have hstep : ((Nat.log 2 x : ℕ) : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    rw [hlogbdef] at hlogb
    calc ((Nat.log 2 x : ℕ) : ℝ) ≤ Real.log (x : ℝ) / Real.log 2 := hlogb
      _ ≤ Real.log (x : ℝ) / (1/2) := by
          refine div_le_div_of_nonneg_left hlogx_nonneg (by norm_num) ?_
          linarith [Real.log_two_gt_d9]
      _ = 2 * Real.log (x : ℝ) := by ring
  have hone : 1 ≤ Real.log (x : ℝ) := by
    have h32 : Real.log (32 : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hx)
    have h1 : (1 : ℝ) ≤ Real.log 32 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 32)]
      linarith [Real.exp_one_lt_three]
    linarith
  rw [blockCount]
  push_cast
  linarith

/-- Each block contributes at most `4x`. -/
lemma blodSumUV_term_le (x M Y j : ℕ) (hx : 32 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) (hj : j < blockCount M Y) :
    (blodU M j : ℝ) * (blodV x M j : ℝ) ≤ 4 * (x : ℝ) := by
  have hQle : blockStart M j ≤ Y + M := by
    rw [blockStart, blockCount] at *
    have hj' : j ≤ Nat.log 2 (Y / M + 1) := by omega
    have h2 : 2 ^ j ≤ Y / M + 1 := by
      calc 2 ^ j ≤ 2 ^ Nat.log 2 (Y / M + 1) := Nat.pow_le_pow_right (by norm_num) hj'
        _ ≤ Y / M + 1 := Nat.pow_log_le_self 2 (by simp)
    calc M * 2 ^ j ≤ M * (Y / M + 1) := Nat.mul_le_mul_left M h2
      _ = M * (Y / M) + M * 1 := by ring
      _ ≤ Y + M := by
          have := Nat.mul_div_le Y M
          omega
  set Q := blockStart M j with hQ
  have hU : (blodU M j : ℝ) = 2 * (Q : ℝ) := by rw [blodU, hQ]; push_cast; ring
  have hV : (blodV x M j : ℝ) = (((x + 2) / Q : ℕ) : ℝ) + 1 := by
    rw [blodV, hQ]; push_cast; ring
  have hmul : (Q : ℝ) * ((((x + 2) / Q : ℕ)) : ℝ) ≤ ((x : ℝ) + 2) := by
    have h := Nat.mul_div_le (x + 2) Q
    have h' : ((Q * ((x + 2) / Q) : ℕ) : ℝ) ≤ ((x + 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hQleR : (Q : ℝ) ≤ (Y : ℝ) + (M : ℝ) :=
    hQ ▸ (by exact_mod_cast hQle : (blockStart M j : ℝ) ≤ (Y : ℝ) + (M : ℝ))
  have hMYR : (M : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hMY
  calc (blodU M j : ℝ) * (blodV x M j : ℝ)
      = 2 * ((Q : ℝ) * ((((x + 2) / Q : ℕ)) : ℝ)) + 2 * (Q : ℝ) := by rw [hU, hV]; ring
    _ ≤ 2 * ((x : ℝ) + 2) + 2 * (Q : ℝ) := by linarith
    _ ≤ 2 * (x : ℝ) + 4 + 4 * (Y : ℝ) := by linarith
    _ ≤ 2 * (x : ℝ) + 4 + 8 * (x : ℝ) ^ ((1:ℝ)/3) := by linarith
    _ ≤ 2 * (x : ℝ) + 4 + (x : ℝ) := by linarith [blodSumUV_eight_mul_cbrt_le x hx]
    _ ≤ 4 * (x : ℝ) := by
        have h4x : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 4 ≤ x)
        linarith

theorem blodSumUVLe (x M Y : ℕ) (hx : 32 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) :
    (∑ j ∈ Finset.range (blockCount M Y), (blodU M j : ℝ) * (blodV x M j : ℝ))
      ≤ 12 * (x : ℝ) * Real.log (x : ℝ) := by
  have hY1x : Y + 1 ≤ x := blodSumUV_Y_add_one_le x Y hx hY
  have hcount : ((blockCount M Y : ℕ) : ℝ) ≤ 3 * Real.log (x : ℝ) :=
    blodSumUV_blockCount_le x M Y hx hY1x
  have hterm : ∀ j ∈ Finset.range (blockCount M Y),
      (blodU M j : ℝ) * (blodV x M j : ℝ) ≤ 4 * (x : ℝ) :=
    fun j hj => blodSumUV_term_le x M Y j hx hM hMY hY (Finset.mem_range.mp hj)
  have h4x : (0 : ℝ) ≤ 4 * (x : ℝ) := by positivity
  calc (∑ j ∈ Finset.range (blockCount M Y), (blodU M j : ℝ) * (blodV x M j : ℝ))
      ≤ ∑ _j ∈ Finset.range (blockCount M Y), (4 * (x : ℝ)) := Finset.sum_le_sum hterm
    _ = ((blockCount M Y : ℕ) : ℝ) * (4 * (x : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * Real.log (x : ℝ)) * (4 * (x : ℝ)) :=
        mul_le_mul_of_nonneg_right hcount h4x
    _ = 12 * (x : ℝ) * Real.log (x : ℝ) := by ring

end Work.NumberTheory.Chen.BTermCount
