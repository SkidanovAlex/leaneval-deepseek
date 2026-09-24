import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodUnweightedDefs

/-!
# The `√(U_j V_j)` block sum of the unweighted bilinear level of distribution

This module bounds the sum over the dyadic `a`-blocks of `√(U_j · V_j)`, where
`U_j = 2 * blockStart M j` is twice the block start (the `a`-range) and
`V_j = (x+2) / blockStart M j + 1` is the `b`-range.

Since `U_j · V_j = 2 Q_j (((x+2)/Q_j) + 1) ≤ 2(x+2) + 2 Q_j` with `Q_j = M 2^j ≤ Y + M`,
each term is at most `3√x` under the standing hypotheses (`x ≥ 32`, `M ≤ Y ≤ 2x^{1/3}`),
and the number of blocks is `O(log x)`: `blockCount M Y ≤ 2 log x`.  Hence the block sum is
at most `6 √x log x`.

The two ingredients are proved here separately:

* `blodBlockStartLeAdd` — the dyadic block starts do not overshoot the window (`Q_j ≤ Y+M`);
* `blodUVBound`/`blodSqrtTermLe` — the per-block bound `√(U_j V_j) ≤ 3√x`;
* `blodBlockCountLe` — the block count bound `blockCount M Y ≤ 2 log x`.
-/

open Finset

namespace Work.NumberTheory.Chen.BTermCount

/-- The dyadic block starts never overshoot the window top by more than `M`:
`blockStart M j = M * 2^j ≤ Y + M` for every block index `j < blockCount M Y`. -/
private theorem blodBlockStartLeAdd (M Y j : ℕ) (_hM : 1 ≤ M) (hj : j < blockCount M Y) :
    blockStart M j ≤ Y + M := by
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

/-- The product of the `a`-range and the `b`-range of a dyadic block is at most `6(x+2)`. -/
private theorem blodUVBound (x M Y j : ℕ) (hx : 32 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) (hj : j < blockCount M Y) :
    ((blodU M j : ℝ) * (blodV x M j : ℝ)) ≤ 6 * ((x : ℝ) + 2) := by
  have hx1 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hQle : blockStart M j ≤ Y + M := blodBlockStartLeAdd M Y j hM hj
  have hQpos : (0:ℝ) < (blockStart M j : ℝ) := by
    have : 0 < blockStart M j := by unfold blockStart; positivity
    exact_mod_cast this
  have hU2 : ((blodU M j : ℕ) : ℝ) = 2 * (blockStart M j : ℝ) := by
    rw [blodU]; push_cast; ring
  have hVle1 : ((blodV x M j : ℕ) : ℝ) ≤ ((x : ℝ) + 2) / (blockStart M j : ℝ) + 1 := by
    rw [blodV]
    have h := Nat.cast_div_le (α := ℝ) (m := x + 2) (n := blockStart M j)
    push_cast at h ⊢
    linarith
  have hQmul : (blockStart M j : ℝ) * (((x : ℝ) + 2) / (blockStart M j : ℝ)) = (x : ℝ) + 2 := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (ne_of_gt hQpos)]
  have hQ2Y : (blockStart M j : ℝ) ≤ 2 * (Y : ℝ) := by
    have h1 : (blockStart M j : ℝ) ≤ (Y : ℝ) + (M : ℝ) := by exact_mod_cast hQle
    have h2 : (M : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hMY
    linarith
  have hYle2 : (Y : ℝ) ≤ (x : ℝ) + 2 := by
    have hx8 : (8:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 8 ≤ x)
    have hx2sq : (8:ℝ) ≤ (x:ℝ)^2 := by nlinarith [hx8]
    have ht0 : (0:ℝ) ≤ (x:ℝ)^((1:ℝ)/3) := Real.rpow_nonneg (le_of_lt hx1) _
    have hcube : ((x:ℝ)^((1:ℝ)/3))^3 = (x:ℝ) := by
      have := Real.rpow_inv_natCast_pow (x := (x:ℝ)) (n := 3) (le_of_lt hx1) (by norm_num)
      simpa [one_div] using this
    have hmain : ((x:ℝ)^((1:ℝ)/3))^3 ≤ ((x:ℝ)/2)^3 := by
      rw [hcube]; nlinarith [hx2sq]
    have hle : (x:ℝ)^((1:ℝ)/3) ≤ (x:ℝ)/2 :=
      (pow_le_pow_iff_left₀ ht0 (by positivity) (by norm_num : 3 ≠ 0)).mp hmain
    linarith
  rw [hU2]
  have h2 : (blockStart M j : ℝ) * (((x : ℝ)+2)/(blockStart M j : ℝ) + 1)
      = ((x : ℝ)+2) + (blockStart M j : ℝ) := by rw [mul_add, mul_one, hQmul]
  calc 2 * (blockStart M j : ℝ) * ((blodV x M j : ℕ) : ℝ)
      ≤ 2 * (blockStart M j : ℝ) * (((x : ℝ)+2)/(blockStart M j : ℝ) + 1) := by
        nlinarith [hVle1, hQpos]
    _ = 2 * (((x : ℝ)+2) + (blockStart M j : ℝ)) := by linarith [h2]
    _ ≤ 6 * ((x:ℝ) + 2) := by linarith

/-- Each term of the block sum is at most `3√x`. -/
private theorem blodSqrtTermLe (x M Y j : ℕ) (hx : 32 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) (hj : j < blockCount M Y) :
    Real.sqrt ((blodU M j : ℝ) * (blodV x M j : ℝ)) ≤ 3 * Real.sqrt (x : ℝ) := by
  have hx1 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  refine le_trans (Real.sqrt_le_sqrt (blodUVBound x M Y j hx hM hMY hY hj)) ?_
  have h3 : (6:ℝ) * ((x:ℝ) + 2) ≤ (3 * Real.sqrt (x:ℝ))^2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hx1)]
    have hx4 : (4:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 4 ≤ x)
    nlinarith
  calc Real.sqrt (6 * ((x:ℝ) + 2)) ≤ Real.sqrt ((3 * Real.sqrt (x:ℝ))^2) :=
        Real.sqrt_le_sqrt h3
    _ = 3 * Real.sqrt (x:ℝ) := Real.sqrt_sq (by positivity)

/-- The number of dyadic blocks is at most `2 log x`, under `M ≤ Y ≤ 2x^{1/3}`. -/
private theorem blodBlockCountLe (x M Y : ℕ) (hx : 32 ≤ x) (_hM : 1 ≤ M) (_hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) :
    ((blockCount M Y : ℕ) : ℝ) ≤ 2 * Real.log (x : ℝ) := by
  have hx1 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  set k := Nat.log 2 (Y / M + 1) with hkdef
  have hbc : blockCount M Y = k + 1 := by rw [blockCount, hkdef]
  have h2k : 2 ^ k ≤ Y / M + 1 := Nat.pow_log_le_self 2 (by simp)
  have h2kR : (2:ℝ)^k ≤ (Y:ℝ) + 1 := by
    have h1 : ((2:ℕ)^k : ℝ) ≤ ((Y/M + 1 : ℕ) : ℝ) := by exact_mod_cast h2k
    have h2 : ((Y/M : ℕ) : ℝ) ≤ (Y:ℝ) := by exact_mod_cast Nat.div_le_self Y M
    have h3 : ((2:ℕ)^k : ℝ) = (2:ℝ)^k := by push_cast; ring
    push_cast at h1
    linarith
  have hY1 : (Y:ℝ) + 1 ≤ 3 * (x:ℝ)^((1:ℝ)/3) := by
    have hx13 : (1:ℝ) ≤ (x:ℝ)^((1:ℝ)/3) := by
      have h1 : (1:ℝ)^((1:ℝ)/3) ≤ (x:ℝ)^((1:ℝ)/3) :=
        Real.rpow_le_rpow (by norm_num)
          (show (1:ℝ) ≤ (x:ℝ) by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
      simpa using h1
    linarith
  have hlog : (k:ℝ) * Real.log 2 ≤ Real.log 2 + 1/2 + (1/3) * Real.log (x:ℝ) := by
    have hpos : (0:ℝ) < (2:ℝ)^k := by positivity
    have hle1 : Real.log ((2:ℝ)^k) ≤ Real.log (3 * (x:ℝ)^((1:ℝ)/3)) :=
      Real.log_le_log hpos (le_trans h2kR hY1)
    rw [Real.log_pow] at hle1
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hx1 _)),
      Real.log_rpow hx1] at hle1
    have hlog3 : Real.log 3 ≤ Real.log 2 + 1/2 := by
      have h : Real.log 3 = Real.log 2 + Real.log (3/2) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
      rw [h]
      have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3/2)
      linarith
    linarith
  have hlog2lo : (0.69:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hlogx : (3.4:ℝ) ≤ Real.log (x:ℝ) := by
    have h1 : Real.log 32 ≤ Real.log (x:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hx)
    have h2 : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]; push_cast; ring
    rw [h2] at h1
    linarith
  have hgoal : (k:ℝ) + 1 ≤ 2 * Real.log (x:ℝ) := by
    nlinarith [hlog, hlog2lo, hlog2hi, hlogx]
  rw [hbc]; push_cast; linarith

/-- **The `√(U_j V_j)` block sum.** Bounded by `6 √x log x`. -/
theorem blodSumSqrtUVLe (x M Y : ℕ) (hx : 32 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) :
    (∑ j ∈ Finset.range (blockCount M Y),
        Real.sqrt ((blodU M j : ℝ) * (blodV x M j : ℝ)))
      ≤ 6 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) := by
  have hterm : ∀ j ∈ Finset.range (blockCount M Y),
      Real.sqrt ((blodU M j : ℝ) * (blodV x M j : ℝ)) ≤ 3 * Real.sqrt (x : ℝ) := by
    intro j hj
    exact blodSqrtTermLe x M Y j hx hM hMY hY (Finset.mem_range.mp hj)
  have hcount := blodBlockCountLe x M Y hx hM hMY hY
  calc (∑ j ∈ Finset.range (blockCount M Y),
          Real.sqrt ((blodU M j : ℝ) * (blodV x M j : ℝ)))
      ≤ ∑ _j ∈ Finset.range (blockCount M Y), 3 * Real.sqrt (x : ℝ) :=
        Finset.sum_le_sum hterm
    _ = ((blockCount M Y : ℕ) : ℝ) * (3 * Real.sqrt (x : ℝ)) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 * Real.log (x:ℝ)) * (3 * Real.sqrt (x:ℝ)) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 6 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) := by ring

end Work.NumberTheory.Chen.BTermCount
