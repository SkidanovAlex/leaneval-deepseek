import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A crude exp/log-log bound for `1000^k k^k`

We prove that for all `P, T, k` with `2 ≤ P`, `3 ≤ T`, and
`log T / log P ≤ k ≤ log T / log P + 1`, the quantity `1000^k · k^k` is bounded
by an explicit constant times `exp (2 · (log T / log P) · log (log T))`.

The argument is elementary: writing `L = log T / log P`, we have `k ≤ L + 1`, so
`1000^k k^k ≤ (1000 (L+1))^{L+1} = exp ((L+1)(log 1000 + log (L+1)))`.
The exponent is compared with `2 L log log T`, using `log T ≥ L log 2` (from `P ≥ 2`)
and `log T ≥ log 3` (from `T ≥ 3`), with a case split on the size of `L`.
-/

namespace Work.BMF.mr_direct

/-- `log 1000 ≤ 10`. -/
private lemma log_1000_le_ten : Real.log 1000 ≤ 10 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1000)]
  have h : Real.exp 10 = Real.exp 1 ^ 10 := by
    have hh : (10 : ℝ) = (10 : ℕ) * 1 := by norm_num
    rw [hh, Real.exp_nat_mul]
  rw [h]
  have h2 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hp := pow_lt_pow_left₀ h2 (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (10 : ℕ) ≠ 0)
  norm_num at hp ⊢
  linarith

/-- `2 ≤ log 10`. -/
private lemma log_ten_ge_two : 2 ≤ Real.log 10 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10)]
  have h : Real.exp 2 = Real.exp 1 ^ 2 := by
    have hh : (2 : ℝ) = (2 : ℕ) * 1 := by norm_num
    rw [hh, Real.exp_nat_mul]
  rw [h]
  have h3 : (Real.exp 1 : ℝ) < 3 := Real.exp_one_lt_three
  have hp := pow_lt_pow_left₀ h3 (le_of_lt (Real.exp_pos 1)) (by norm_num : (2 : ℕ) ≠ 0)
  norm_num at hp ⊢
  linarith

/-- `log 2 ≤ 1`. -/
private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
  linarith [Real.exp_one_gt_two]

/-- `-1 ≤ log (log 2)`. -/
private lemma log_log_two_ge_neg_one : -1 ≤ Real.log (Real.log 2) := by
  have hpos2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.le_log_iff_exp_le hpos2]
  have h1 : Real.exp (-1) < (1 : ℝ) / 2 := by
    have h := one_div_lt_one_div_of_lt (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) < Real.exp 1 from Real.exp_one_gt_two)
    rw [one_div, ← Real.exp_neg] at h
    exact h
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  linarith

/-- `log (L+1) ≤ log L + 1` for `L ≥ 1`. -/
private lemma log_succ_le_log_add_one (L : ℝ) (hL : 1 ≤ L) :
    Real.log (L + 1) ≤ Real.log L + 1 := by
  have h2L : L + 1 ≤ 2 * L := by linarith
  calc Real.log (L + 1) ≤ Real.log (2 * L) :=
        Real.log_le_log (by linarith) h2L
    _ = Real.log 2 + Real.log L := by
        rw [Real.log_mul (by norm_num) (by linarith)]
    _ ≤ 1 + Real.log L := by linarith [log_two_le_one]
    _ = Real.log L + 1 := by ring

/-- The key analytic inequality: the exponent of `1000^{L+1} (L+1)^{L+1}` is dominated
by `2 L log log T` up to the additive constant `10^{15}`. -/
private lemma key_ineq (L T : ℝ) (hL : 0 < L) (hT : 3 ≤ T)
    (hLT : L * Real.log 2 ≤ Real.log T) :
    (L + 1) * (Real.log 1000 + Real.log (L + 1)) ≤
      (1000000000000000 : ℝ) + 2 * L * Real.log (Real.log T) := by
  have hlog1000 : Real.log 1000 ≤ 10 := log_1000_le_ten
  have hlog1000nn : 0 ≤ Real.log 1000 := Real.log_nonneg (by norm_num)
  have hlogT1 : 1 < Real.log T := by
    have h3 : Real.log 3 ≤ Real.log T := Real.log_le_log (by norm_num) hT
    have h13 : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_three
    linarith
  have hloglogT : 0 < Real.log (Real.log T) := Real.log_pos hlogT1
  rcases le_or_gt L 10000000 with hL7 | hL7
  · -- small `L`
    have hlogL1 : Real.log (L + 1) ≤ L := by
      have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < L + 1)
      linarith
    have hA : (L + 1) * (Real.log 1000 + Real.log (L + 1)) ≤ 10000001 * 10000010 := by
      have h1 : Real.log 1000 + Real.log (L + 1) ≤ 10000010 := by linarith
      have h2 : L + 1 ≤ 10000001 := by linarith
      have hc : 0 ≤ Real.log 1000 + Real.log (L + 1) := by
        have hpos : 0 ≤ Real.log (L + 1) := Real.log_nonneg (by linarith)
        linarith
      exact mul_le_mul h2 h1 hc (by norm_num)
    have hfin : (10000001 : ℝ) * 10000010 ≤ 1000000000000000 := by norm_num
    have hB : 0 ≤ 2 * L * Real.log (Real.log T) := by positivity
    linarith
  · -- large `L`
    have hlog10m : Real.log (10000000 : ℝ) = 7 * Real.log 10 := by
      rw [show (10000000 : ℝ) = (10 : ℝ) ^ 7 by norm_num, Real.log_pow]
      norm_num
    have hlogL : 14 ≤ Real.log L := by
      have hle : Real.log (10000000 : ℝ) ≤ Real.log L :=
        Real.log_le_log (by norm_num) (le_of_lt hL7)
      rw [hlog10m] at hle
      linarith [log_ten_ge_two]
    have hlogsucc : Real.log (L + 1) ≤ Real.log L + 1 :=
      log_succ_le_log_add_one L (by linarith)
    have hLlog2pos : 0 < L * Real.log 2 := mul_pos hL (Real.log_pos (by norm_num))
    have h1 : Real.log (L * Real.log 2) ≤ Real.log (Real.log T) :=
      Real.log_le_log hLlog2pos hLT
    have h2 : Real.log (L * Real.log 2) = Real.log L + Real.log (Real.log 2) :=
      Real.log_mul (ne_of_gt hL) (ne_of_gt (Real.log_pos (by norm_num)))
    have hLL : Real.log L - 1 ≤ Real.log (Real.log T) := by
      rw [h2] at h1
      linarith [log_log_two_ge_neg_one]
    have hA' : (L + 1) * (Real.log 1000 + Real.log (L + 1)) ≤ (L + 1) * (Real.log L + 11) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ L + 1)
      linarith
    have hB' : 2 * L * (Real.log L - 1) ≤ 2 * L * Real.log (Real.log T) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ 2 * L)
      linarith
    have h14 : (L - 1) * 14 ≤ (L - 1) * Real.log L :=
      mul_le_mul_of_nonneg_left hlogL (by linarith : (0 : ℝ) ≤ L - 1)
    have hkey : (L + 1) * (Real.log L + 11) ≤
        (1000000000000000 : ℝ) + 2 * L * (Real.log L - 1) := by
      nlinarith [h14, hL, hL7]
    linarith

theorem expLogLog_ineq_win :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P T : ℝ) (k : ℕ), 2 ≤ P → 3 ≤ T →
        Real.log T / Real.log P ≤ (k : ℝ) → (k : ℝ) ≤ Real.log T / Real.log P + 1 →
        (1000 : ℝ) ^ k * (k : ℝ) ^ k
          ≤ C * Real.exp (2 * (Real.log T / Real.log P) * Real.log (Real.log T)) := by
  refine ⟨Real.exp 1000000000000000, Real.exp_pos _, ?_⟩
  intro P T k hP hT hLk hkL
  set L : ℝ := Real.log T / Real.log P with hLdef
  have hP1 : 1 < P := by linarith
  have hT1 : 1 < T := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hLpos : 0 < L := by rw [hLdef]; exact div_pos hlogT hlogP
  have hLnonneg : 0 ≤ L := le_of_lt hLpos
  have hlogP2 : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hTL : Real.log T = L * Real.log P := by
    rw [hLdef, div_mul_cancel₀ _ (ne_of_gt hlogP)]
  have hLT2 : L * Real.log 2 ≤ Real.log T := by
    rw [hTL]; exact mul_le_mul_of_nonneg_left hlogP2 hLnonneg
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hLpos hLk
  have hknat : 0 < k := Nat.cast_pos.mp hkpos
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hknat
  have hkL1 : (k : ℝ) ≤ L + 1 := hkL
  have hpow1000 : (1000 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 1000) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1000)]
    congr 1; ring
  have hpowk : (k : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log (k : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hkpos]
    congr 1; ring
  have hlhs : (1000 : ℝ) ^ k * (k : ℝ) ^ k
      ≤ Real.exp ((L + 1) * (Real.log 1000 + Real.log (L + 1))) := by
    rw [hpow1000, hpowk, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog1000pos : 0 < Real.log 1000 := Real.log_pos (by norm_num)
    have hlogk_le : Real.log (k : ℝ) ≤ Real.log (L + 1) := Real.log_le_log hkpos hkL1
    have h1 : (k : ℝ) * Real.log 1000 ≤ (L + 1) * Real.log 1000 :=
      mul_le_mul_of_nonneg_right hkL1 (le_of_lt hlog1000pos)
    have h2 : (k : ℝ) * Real.log (k : ℝ) ≤ (L + 1) * Real.log (L + 1) :=
      mul_le_mul hkL1 hlogk_le (Real.log_nonneg hk1) (by linarith : (0 : ℝ) ≤ L + 1)
    linarith
  have hexp : Real.exp ((L + 1) * (Real.log 1000 + Real.log (L + 1)))
      ≤ Real.exp 1000000000000000 * Real.exp (2 * L * Real.log (Real.log T)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hk := key_ineq L T hLpos hT hLT2
    linarith
  calc (1000 : ℝ) ^ k * (k : ℝ) ^ k
      ≤ Real.exp ((L + 1) * (Real.log 1000 + Real.log (L + 1))) := hlhs
    _ ≤ Real.exp 1000000000000000 * Real.exp (2 * L * Real.log (Real.log T)) := hexp

end Work.BMF.mr_direct
