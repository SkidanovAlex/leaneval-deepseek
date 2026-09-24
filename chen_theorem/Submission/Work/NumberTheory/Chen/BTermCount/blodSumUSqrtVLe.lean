import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodUnweightedDefs

namespace Work.NumberTheory.Chen.BTermCount

open Finset

/-!
# The `U √V` block sum

`blodU M j = 2 · blockStart M j` and `blodV x M j = (x+2)/blockStart M j + 1` are the
`a`-range and the `b`-range of the `j`-th dyadic block of the window `[M,Y)`.

This module evaluates the "square-root weighted" block sum

  `Σ_{j < blockCount M Y} blodU M j · √(blodV x M j)`

in the regime `M ≤ Y ≤ 2 x^{1/3}`, `x ≥ 32`.  The bound is `48 x^{2/3} log x`.

The proof is completely elementary.  For each block `j < blockCount M Y` the block start
`Q_j = M · 2^j` satisfies `Q_j ≤ Y + M ≤ 2Y` (dyadic blocks do not overshoot the window top
by more than the window bottom).  Since `x ≥ 32` forces `2Y ≤ x + 2`, this gives
`(x+2)/Q_j ≥ 1` and hence `blodV x M j ≤ 2 (x+2)/Q_j`; the term is therefore at most

  `2 Q_j √(2(x+2)/Q_j) = 2 √(2(x+2) Q_j) ≤ 2 √(4 Y (x+2)) ≤ 8 x^{2/3}`,

using `Y ≤ 2x^{1/3}` and `x + 2 ≤ 2x`.  There are at most `6 log x` blocks (a dyadic-counting
bound using `Y ≤ x`), so the sum is at most `6 log x · 8 x^{2/3} = 48 x^{2/3} log x`.
-/

/-- Dyadic blocks do not overshoot the window top by more than the window bottom:
`blockStart M j = M · 2^j ≤ Y + M` for `j < blockCount M Y` and `1 ≤ M`. -/
private lemma blod_blockStart_le_add (M Y j : ℕ) (_hM : 1 ≤ M) (hj : j < blockCount M Y) :
    blockStart M j ≤ Y + M := by
  have hj' : j ≤ Nat.log 2 (Y / M + 1) := by
    have h := hj
    unfold blockCount at h
    omega
  have h2 : 2 ^ j ≤ Y / M + 1 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hj') (Nat.pow_log_le_self 2 (by simp))
  calc blockStart M j = M * 2 ^ j := rfl
    _ ≤ M * (Y / M + 1) := Nat.mul_le_mul_left M h2
    _ = M * (Y / M) + M := by ring
    _ ≤ Y + M := Nat.add_le_add_right (Nat.mul_div_le Y M) M

/-- Each block of the `U √V` sum is at most `8 x^{2/3}`. -/
private lemma blod_term_le (x M Y j : ℕ) (hx : 32 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) (hj : j < blockCount M Y) :
    (blodU M j : ℝ) * Real.sqrt (blodV x M j : ℝ) ≤ 8 * (x:ℝ)^((2:ℝ)/3) := by
  set Q := blockStart M j with hQ
  have hQadd : Q ≤ Y + M := blod_blockStart_le_add M Y j hM hj
  have hQ2Y : Q ≤ 2 * Y := by omega
  -- `(x:ℝ)^{1/3} ≥ 3`, `((x:ℝ)^{1/3})^3 = x`, hence `2Y ≤ 4x^{1/3} ≤ x + 2`
  have ht3 : (3:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/3) := by
    have hxr : (27:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 27 ≤ x)
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 27) hxr
      (by norm_num : (0:ℝ) ≤ (1:ℝ)/3)
    norm_num at h
    exact h
  have htc : ((x:ℝ) ^ ((1:ℝ)/3))^3 = (x:ℝ) := by
    have := Real.rpow_inv_natCast_pow (x := (x:ℝ)) (by positivity) (by norm_num : (3:ℕ) ≠ 0)
    simpa using this
  have h4 : 4 * (x:ℝ)^((1:ℝ)/3) ≤ (x:ℝ) + 2 := by
    nlinarith [ht3, htc, sq_nonneg ((x:ℝ)^((1:ℝ)/3) - 3)]
  have h2Y : 2 * Y ≤ x + 2 := by
    have : (2 * Y : ℝ) ≤ ((x + 2 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hQle : Q ≤ x + 2 := le_trans hQ2Y h2Y
  have hQpos : 0 < Q := by
    rw [hQ, blockStart]
    exact Nat.mul_pos (by omega) (pow_pos (by norm_num) j)
  have hU : (blodU M j : ℝ) = 2 * (Q:ℝ) := by
    rw [blodU, ← hQ]; push_cast; ring
  have hV : (blodV x M j : ℝ) = (((x+2)/Q : ℕ) : ℝ) + 1 := by
    rw [blodV, ← hQ]; push_cast; ring
  -- `blodV x M j ≤ 2(x+2)/Q`
  have hVle : (blodV x M j : ℝ) ≤ 2 * (((x:ℝ)+2) / (Q:ℝ)) := by
    rw [hV]
    have h1 : (((x+2)/Q : ℕ) : ℝ) ≤ ((x+2:ℕ):ℝ) / (Q:ℝ) := Nat.cast_div_le
    have h2 : (((x+2:ℕ):ℝ)) = (x:ℝ)+2 := by push_cast; ring
    rw [h2] at h1
    have hQnn : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQpos
    have hQx : (Q:ℝ) ≤ (x:ℝ)+2 := by exact_mod_cast hQle
    have hone : (1:ℝ) ≤ ((x:ℝ)+2)/(Q:ℝ) := (one_le_div hQnn).mpr hQx
    linarith
  have hsqrt := Real.sqrt_le_sqrt hVle
  have hstep1 : (blodU M j : ℝ) * Real.sqrt (blodV x M j : ℝ) ≤
      (2*(Q:ℝ)) * Real.sqrt (2 * (((x:ℝ)+2) / (Q:ℝ))) := by
    rw [hU]
    exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
  -- `Q √(2(x+2)/Q) = √(2(x+2)Q)`
  have hQsqrt : (Q:ℝ) * Real.sqrt (2*((x:ℝ)+2)/(Q:ℝ)) = Real.sqrt (2*((x:ℝ)+2)*(Q:ℝ)) := by
    have hQnn : (0:ℝ) ≤ (Q:ℝ) := by positivity
    calc (Q:ℝ) * Real.sqrt (2*((x:ℝ)+2)/(Q:ℝ))
        = Real.sqrt ((Q:ℝ)^2) * Real.sqrt (2*((x:ℝ)+2)/(Q:ℝ)) := by
            rw [Real.sqrt_sq hQnn]
      _ = Real.sqrt ((Q:ℝ)^2 * (2*((x:ℝ)+2)/(Q:ℝ))) := by
            rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (Q:ℝ)^2)]
      _ = Real.sqrt (2*((x:ℝ)+2)*(Q:ℝ)) := by
            congr 1
            field_simp
  have harg : 2*((x:ℝ)+2)*(Q:ℝ) ≤ 16 * (x:ℝ)^((4:ℝ)/3) := by
    have hx2 : (x:ℝ) + 2 ≤ 2 * (x:ℝ) := by
      have : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
      linarith
    have hQ2Yr : (Q:ℝ) ≤ 2*(Y:ℝ) := by exact_mod_cast hQ2Y
    have hx43 : (x:ℝ)^((4:ℝ)/3) = (x:ℝ) * (x:ℝ)^((1:ℝ)/3) := by
      rw [show (4:ℝ)/3 = 1 + 1/3 by norm_num,
        Real.rpow_add (by positivity : (0:ℝ) < (x:ℝ)), Real.rpow_one]
    rw [hx43]
    have hxn : (0:ℝ) < (x:ℝ) := by positivity
    nlinarith [hQ2Yr, hY, hx2, hxn, Real.rpow_nonneg (le_of_lt hxn) ((1:ℝ)/3)]
  have hsqrt16 : Real.sqrt (16 * (x:ℝ)^((4:ℝ)/3)) = 4 * (x:ℝ)^((2:ℝ)/3) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16)]
    have h16 : Real.sqrt (16:ℝ) = 4 := by norm_num
    rw [h16]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (x:ℝ))]
    norm_num
  have hfin : 2 * Real.sqrt (2*((x:ℝ)+2)*(Q:ℝ)) ≤ 8 * (x:ℝ)^((2:ℝ)/3) := by
    have := Real.sqrt_le_sqrt harg
    rw [hsqrt16] at this
    linarith
  have hmid : (2*(Q:ℝ)) * Real.sqrt (2 * (((x:ℝ)+2) / (Q:ℝ)))
      = 2 * Real.sqrt (2*((x:ℝ)+2)*(Q:ℝ)) := by
    rw [show (2*(Q:ℝ)) * Real.sqrt (2 * (((x:ℝ)+2) / (Q:ℝ)))
        = 2 * ((Q:ℝ) * Real.sqrt (2*((x:ℝ)+2)/(Q:ℝ))) by ring_nf, hQsqrt]
  linarith

/-- `(Nat.log 2 n : ℝ) ≤ 2 log n` for `n ≥ 2`. -/
private lemma cast_natLog_le_two_log {n : ℕ} (hn : 2 ≤ n) :
    ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have h3 : ((2 : ℕ) : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast h1
  have h4 := Real.log_le_log (by positivity : (0:ℝ) < ((2:ℕ):ℝ) ^ Nat.log 2 n) h3
  rw [Real.log_pow] at h4
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpos : (0 : ℝ) < Real.log 2 := by linarith
  have hk : ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hpos]
    simpa using h4
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : (1 : ℝ) / 2 ≤ Real.log (n : ℝ) :=
    le_trans hlog2 (Real.log_le_log (by norm_num) hn2)
  calc ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := hk
    _ ≤ Real.log (n : ℝ) / (1/2) :=
        div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) (by norm_num) hlog2
    _ = 2 * Real.log (n : ℝ) := by ring

/-- There are at most `6 log x` blocks, for `1 ≤ M ≤ Y ≤ 2x^{1/3}` and `32 ≤ x`. -/
private lemma blod_blockCount_le (x M Y : ℕ) (hx : 32 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) :
    ((blockCount M Y : ℕ) : ℝ) ≤ 6 * Real.log (x:ℝ) := by
  have ht3 : (3:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/3) := by
    have hxr : (27:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 27 ≤ x)
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 27) hxr
      (by norm_num : (0:ℝ) ≤ (1:ℝ)/3)
    norm_num at h
    exact h
  have htc : ((x:ℝ) ^ ((1:ℝ)/3))^3 = (x:ℝ) := by
    have := Real.rpow_inv_natCast_pow (x := (x:ℝ)) (by positivity) (by norm_num : (3:ℕ) ≠ 0)
    simpa using this
  have hx13 : 2 * (x:ℝ)^((1:ℝ)/3) ≤ (x:ℝ) := by
    nlinarith [ht3, htc, sq_nonneg ((x:ℝ)^((1:ℝ)/3) - 3)]
  have hYx : (Y:ℝ) ≤ (x:ℝ) := le_trans hY hx13
  have hYx' : Y ≤ x := by exact_mod_cast hYx
  have hYM2 : 2 ≤ Y / M + 1 := by
    have h1 : 1 ≤ Y / M := Nat.one_le_div_iff (by omega : 0 < M) |>.mpr hMY
    omega
  have hlog' : ((Nat.log 2 (Y / M + 1) : ℕ) : ℝ) ≤ 2 * Real.log ((Y / M + 1 : ℕ) : ℝ) :=
    cast_natLog_le_two_log hYM2
  have hYMle : Y / M + 1 ≤ x + 1 := by
    have h1 : Y / M ≤ Y := Nat.div_le_self Y M
    omega
  have hxm : ((Y / M + 1 : ℕ) : ℝ) ≤ (x : ℝ) + 1 := by exact_mod_cast hYMle
  have hlogmono : Real.log ((Y / M + 1 : ℕ) : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    have hx8 : (8 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 8 ≤ x)
    have h2 : (x : ℝ) + 1 ≤ (x : ℝ) ^ 2 := by nlinarith
    calc Real.log ((Y / M + 1 : ℕ) : ℝ) ≤ Real.log ((x : ℝ) + 1) :=
          Real.log_le_log (by positivity) hxm
      _ ≤ Real.log ((x : ℝ) ^ 2) := Real.log_le_log (by linarith) h2
      _ = 2 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_num
  have hxhalf : (1:ℝ)/2 ≤ Real.log (x:ℝ) := by
    have h8 : (1:ℝ) ≤ Real.log 8 := by
      have h : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
      linarith [Real.log_two_gt_d9]
    have hx8 : (8:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 8 ≤ x)
    linarith [le_trans h8 (Real.log_le_log (by norm_num) hx8)]
  simp only [blockCount]
  push_cast
  linarith

/-- **The `U √V` block sum.**  For `M ≤ Y ≤ 2 x^{1/3}` and `x ≥ 32`,
`Σ_{j < blockCount M Y} blodU M j · √(blodV x M j) ≤ 48 x^{2/3} log x`. -/
theorem blodSumUSqrtVLe (x M Y : ℕ) (hx : 32 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3)) :
    (∑ j ∈ Finset.range (blockCount M Y),
        (blodU M j : ℝ) * Real.sqrt (blodV x M j : ℝ))
      ≤ 48 * (x : ℝ) ^ ((2:ℝ)/3) * Real.log (x : ℝ) := by
  have hbc : ((blockCount M Y : ℕ) : ℝ) ≤ 6 * Real.log (x:ℝ) :=
    blod_blockCount_le x M Y hx hM hMY hY
  have hnn : (0:ℝ) ≤ 8 * (x:ℝ)^((2:ℝ)/3) := by positivity
  calc ∑ j ∈ Finset.range (blockCount M Y),
        (blodU M j : ℝ) * Real.sqrt (blodV x M j : ℝ)
      ≤ ∑ _j ∈ Finset.range (blockCount M Y), 8 * (x:ℝ)^((2:ℝ)/3) :=
        Finset.sum_le_sum (fun j hj =>
          blod_term_le x M Y j hx hM hMY hY (Finset.mem_range.mp hj))
    _ = ((blockCount M Y : ℕ) : ℝ) * (8 * (x:ℝ)^((2:ℝ)/3)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (6 * Real.log (x:ℝ)) * (8 * (x:ℝ)^((2:ℝ)/3)) :=
        mul_le_mul_of_nonneg_right hbc hnn
    _ = 48 * (x:ℝ)^((2:ℝ)/3) * Real.log (x:ℝ) := by ring

end Work.NumberTheory.Chen.BTermCount
