import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Asymptotics

/-- `(⌊z⌋₊ : ℝ) ≥ z / 2` for `z ≥ 2`. -/
private lemma psl_half_le_floor (z : ℝ) (hz : 2 ≤ z) : z / 2 ≤ (⌊z⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one z
  linarith

/-- `Real.log z ≤ 2 * Real.log ⌊z⌋₊` for `z ≥ 2`. -/
private lemma psl_half_log_le_log_floor (z : ℝ) (hz : 2 ≤ z) :
    Real.log z ≤ 2 * Real.log (⌊z⌋₊ : ℝ) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hn2 : (2 : ℕ) ≤ ⌊z⌋₊ := Nat.le_floor hz
  have hnpos : (0 : ℝ) < (⌊z⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊z⌋₊)
  have hlog2 : Real.log 2 ≤ Real.log (⌊z⌋₊ : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hzle : z ≤ 2 * (⌊z⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one z
    have h1 : (1 : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast (by omega : 1 ≤ ⌊z⌋₊)
    linarith
  have hlogz : Real.log z ≤ Real.log 2 + Real.log (⌊z⌋₊ : ℝ) := by
    have h1 : Real.log z ≤ Real.log (2 * (⌊z⌋₊ : ℝ)) := Real.log_le_log hz0 hzle
    have h2 : Real.log (2 * (⌊z⌋₊ : ℝ)) = Real.log 2 + Real.log (⌊z⌋₊ : ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hnpos)
    linarith
  linarith

/-- `Real.log z ≤ 10 * z^{1/10}` for `z ≥ 1`. -/
private lemma psl_log_le_ten_mul_rpow (z : ℝ) (hz : 1 ≤ z) :
    Real.log z ≤ 10 * z ^ ((1 : ℝ) / 10) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hw : 0 < z ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos hz0 _
  have h1 : Real.log (z ^ ((1 : ℝ) / 10)) ≤ z ^ ((1 : ℝ) / 10) - 1 :=
    Real.log_le_sub_one_of_pos hw
  have h2 : Real.log (z ^ ((1 : ℝ) / 10)) = (1 / 10) * Real.log z :=
    Real.log_rpow hz0 ((1 : ℝ) / 10)
  linarith

/-- `x ^ (-(10:ℝ)) = (x^10)⁻¹` for `x ≥ 0`. -/
private lemma psl_rpow_neg_eq_inv_pow (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(10 : ℝ)) = (x ^ 10)⁻¹ := by
  rw [show (-(10 : ℝ)) = -((10 : ℕ) : ℝ) by norm_num]
  rw [Real.rpow_neg hx, Real.rpow_natCast]

/-- `(x/2) ^ (-(10:ℝ)) = 2^10 * x ^ (-(10:ℝ))` for `x > 0`. -/
private lemma psl_half_rpow_neg (x : ℝ) (hx : 0 < x) :
    (x / 2) ^ (-(10 : ℝ)) = 2 ^ 10 * x ^ (-(10 : ℝ)) := by
  rw [psl_rpow_neg_eq_inv_pow (x / 2) (by linarith),
      psl_rpow_neg_eq_inv_pow x (le_of_lt hx)]
  rw [div_pow, inv_div, div_eq_mul_inv]

/-- `(Real.log z) ^ (-(10:ℝ)) = (Real.log z) ^ (-(10:ℤ))`. -/
private lemma psl_rpow_eq_zpow (x : ℝ) :
    x ^ (-(10 : ℝ)) = x ^ (-(10 : ℤ)) := by
  simp

/-- `1 / z ≤ 10^10 * (Real.log z) ^ (-(10:ℝ))` for `z ≥ 2`. -/
private lemma psl_inv_le_const_mul_log_rpow_neg (z : ℝ) (hz : 2 ≤ z) :
    1 / z ≤ 10 ^ 10 * (Real.log z) ^ (-(10 : ℝ)) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hL : 0 < Real.log z := Real.log_pos (by linarith)
  have hle : Real.log z ≤ 10 * z ^ ((1 : ℝ) / 10) := psl_log_le_ten_mul_rpow z hz1
  have hzpow : (z ^ ((1 : ℝ) / 10)) ^ 10 = z := by
    rw [show (1 : ℝ) / 10 = ((10 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow (le_of_lt hz0) (by norm_num)
  have hLpow : (Real.log z) ^ 10 ≤ 10 ^ 10 * z := by
    calc (Real.log z) ^ 10 ≤ (10 * z ^ ((1 : ℝ) / 10)) ^ 10 :=
          pow_le_pow_left₀ (le_of_lt hL) hle 10
      _ = 10 ^ 10 * (z ^ ((1 : ℝ) / 10)) ^ 10 := by rw [mul_pow]
      _ = 10 ^ 10 * z := by rw [hzpow]
  have hLpow_pos : 0 < (Real.log z) ^ 10 := pow_pos hL 10
  rw [psl_rpow_neg_eq_inv_pow (Real.log z) (le_of_lt hL)]
  rw [div_le_iff₀ hz0]
  have hLne : (Real.log z) ^ 10 ≠ 0 := ne_of_gt hLpow_pos
  have key : (1 : ℝ) ≤ 10 ^ 10 * ((Real.log z) ^ 10)⁻¹ * z := by
    have h1 : 1 = (Real.log z) ^ 10 * ((Real.log z) ^ 10)⁻¹ := (mul_inv_cancel₀ hLne).symm
    rw [h1]
    calc (Real.log z) ^ 10 * ((Real.log z) ^ 10)⁻¹
        ≤ (10 ^ 10 * z) * ((Real.log z) ^ 10)⁻¹ :=
          mul_le_mul_of_nonneg_right hLpow (by positivity)
      _ = 10 ^ 10 * ((Real.log z) ^ 10)⁻¹ * z := by ring
  exact key

/-- `1 / ⌊z⌋₊ ≤ 2 * 10^10 * (Real.log z) ^ (-(10:ℝ))` for `z ≥ 2`. -/
private lemma psl_inv_floor_le (z : ℝ) (hz : 2 ≤ z) :
    1 / (⌊z⌋₊ : ℝ) ≤ 2 * 10 ^ 10 * (Real.log z) ^ (-(10 : ℝ)) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hhalf : z / 2 ≤ (⌊z⌋₊ : ℝ) := psl_half_le_floor z hz
  have h1 : 1 / (⌊z⌋₊ : ℝ) ≤ 2 * (1 / z) := by
    calc 1 / (⌊z⌋₊ : ℝ) ≤ 1 / (z / 2) := one_div_le_one_div_of_le (by linarith) hhalf
      _ = 2 * (1 / z) := by rw [one_div_div]; ring
  have h3 := psl_inv_le_const_mul_log_rpow_neg z hz
  calc 1 / (⌊z⌋₊ : ℝ) ≤ 2 * (1 / z) := h1
    _ ≤ 2 * (10 ^ 10 * (Real.log z) ^ (-(10 : ℝ))) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = 2 * 10 ^ 10 * (Real.log z) ^ (-(10 : ℝ)) := by ring

/-- The log-log discrepancy between `z` and its floor. -/
private lemma psl_loglog_diff_le (z : ℝ) (hz : 2 ≤ z) :
    |Real.log (Real.log z) - Real.log (Real.log (⌊z⌋₊ : ℝ))| ≤
      (2 * 10 ^ 10 / Real.log 2) * (Real.log z) ^ (-(10 : ℝ)) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hn2 : (2 : ℕ) ≤ ⌊z⌋₊ := Nat.le_floor hz
  have hnpos : (0 : ℝ) < (⌊z⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊z⌋₊)
  have hn1 : (1 : ℝ) < (⌊z⌋₊ : ℝ) := by exact_mod_cast (by omega : 1 < ⌊z⌋₊)
  have hLn : 0 < Real.log (⌊z⌋₊ : ℝ) := Real.log_pos hn1
  have hL : 0 < Real.log z := Real.log_pos (by linarith)
  have hnle : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (le_of_lt hz0)
  have hLn_le : Real.log (⌊z⌋₊ : ℝ) ≤ Real.log z := Real.log_le_log hnpos hnle
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLn_ge : Real.log 2 ≤ Real.log (⌊z⌋₊ : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hdiff : Real.log (Real.log z) - Real.log (Real.log (⌊z⌋₊ : ℝ)) =
      Real.log (Real.log z / Real.log (⌊z⌋₊ : ℝ)) :=
    (Real.log_div (ne_of_gt hL) (ne_of_gt hLn)).symm
  rw [hdiff]
  have hratio : Real.log z / Real.log (⌊z⌋₊ : ℝ) =
      1 + (Real.log z - Real.log (⌊z⌋₊ : ℝ)) / Real.log (⌊z⌋₊ : ℝ) := by
    field_simp
    ring
  rw [hratio]
  set t : ℝ := (Real.log z - Real.log (⌊z⌋₊ : ℝ)) / Real.log (⌊z⌋₊ : ℝ) with ht_def
  have ht_nonneg : 0 ≤ t := div_nonneg (by linarith) (le_of_lt hLn)
  have h1t_pos : (0 : ℝ) < 1 + t := by linarith
  have hlog1t : Real.log (1 + t) ≤ t := by
    have := Real.log_le_sub_one_of_pos h1t_pos
    linarith
  have hlog_nonneg : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  rw [abs_of_nonneg hlog_nonneg]
  have hz_lt : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
  have hzdiv : z / (⌊z⌋₊ : ℝ) ≤ 1 + 1 / (⌊z⌋₊ : ℝ) := by
    rw [div_le_iff₀ hnpos]
    have h1 : (1 + 1 / (⌊z⌋₊ : ℝ)) * (⌊z⌋₊ : ℝ) = (⌊z⌋₊ : ℝ) + 1 := by field_simp
    rw [h1]; linarith
  have hlogs : Real.log z - Real.log (⌊z⌋₊ : ℝ) ≤ 1 / (⌊z⌋₊ : ℝ) := by
    have h1 : Real.log z - Real.log (⌊z⌋₊ : ℝ) = Real.log (z / (⌊z⌋₊ : ℝ)) :=
      (Real.log_div (ne_of_gt hz0) (ne_of_gt hnpos)).symm
    rw [h1]
    have h2 : Real.log (z / (⌊z⌋₊ : ℝ)) ≤ Real.log (1 + 1 / (⌊z⌋₊ : ℝ)) :=
      Real.log_le_log (div_pos hz0 hnpos) hzdiv
    have h3 : Real.log (1 + 1 / (⌊z⌋₊ : ℝ)) ≤ 1 / (⌊z⌋₊ : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / (⌊z⌋₊ : ℝ))
      linarith
    linarith
  have ht_le : t ≤ (1 / (⌊z⌋₊ : ℝ)) / Real.log (⌊z⌋₊ : ℝ) := by
    rw [ht_def]
    exact div_le_div_of_nonneg_right hlogs (le_of_lt hLn)
  have hfin : (1 / (⌊z⌋₊ : ℝ)) / Real.log (⌊z⌋₊ : ℝ) ≤
      (2 * 10 ^ 10 / Real.log 2) * (Real.log z) ^ (-(10 : ℝ)) := by
    have hinv := psl_inv_floor_le z hz
    have hLninv : 1 / Real.log (⌊z⌋₊ : ℝ) ≤ 1 / Real.log 2 :=
      one_div_le_one_div_of_le hlog2pos hLn_ge
    calc (1 / (⌊z⌋₊ : ℝ)) / Real.log (⌊z⌋₊ : ℝ)
        = (1 / (⌊z⌋₊ : ℝ)) * (1 / Real.log (⌊z⌋₊ : ℝ)) := by ring
      _ ≤ (2 * 10 ^ 10 * (Real.log z) ^ (-(10 : ℝ))) * (1 / Real.log 2) :=
            mul_le_mul hinv hLninv (by positivity) (by positivity)
      _ = (2 * 10 ^ 10 / Real.log 2) * (Real.log z) ^ (-(10 : ℝ)) := by ring
  linarith [hlog1t, ht_le, hfin]

/-- Primes in `Icc 1 n` agree with primes in `Icc 2 n`. -/
private lemma psl_filter_Icc (n : ℕ) :
    (Finset.Icc 1 n).filter Nat.Prime = (Finset.Icc 2 n).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨hp.two_le, h2⟩, hp⟩
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨by omega, h2⟩, hp⟩

theorem prime_sum_loglog_real_form {f : ℕ → ℝ} {c C : ℝ} (hC : 0 ≤ C)
    (h : ∀ y : ℕ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, f p) - Real.log (Real.log (y : ℝ)) - c|
        ≤ C * ((Real.log (y : ℝ)) ^ (-(10 : ℝ)) + 1 / (y : ℝ))) :
    ∃ c' C' : ℝ, 0 < C' ∧ ∀ z : ℝ, 2 ≤ z →
      |(∑ p ∈ (Finset.Icc 2 ⌊z⌋₊).filter Nat.Prime, f p) - Real.log (Real.log z) - c'|
        ≤ C' * (Real.log z) ^ (-(10 : ℤ)) := by
  refine ⟨c, C * ((2 : ℝ) ^ 10 + 2 * 10 ^ 10) + 2 * 10 ^ 10 / Real.log 2, ?_, ?_⟩
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hconstpos : 0 < 2 * 10 ^ 10 / Real.log 2 := div_pos (by norm_num) hlog2
    have hCnn : 0 ≤ C * ((2 : ℝ) ^ 10 + 2 * 10 ^ 10) := mul_nonneg hC (by norm_num)
    linarith
  · intro z hz
    have hz0 : (0 : ℝ) < z := by linarith
    have hn2 : 2 ≤ ⌊z⌋₊ := Nat.le_floor hz
    have hhyp := h ⌊z⌋₊ hn2
    rw [psl_filter_Icc] at hhyp
    set S : ℝ := ∑ p ∈ (Finset.Icc 2 ⌊z⌋₊).filter Nat.Prime, f p with hS
    have hLzp : 0 < Real.log z := Real.log_pos (by linarith)
    have hhalf : Real.log z ≤ 2 * Real.log (⌊z⌋₊ : ℝ) := psl_half_log_le_log_floor z hz
    have hB1 : (Real.log (⌊z⌋₊ : ℝ)) ^ (-(10 : ℝ)) ≤
        (2 : ℝ) ^ 10 * (Real.log z) ^ (-(10 : ℝ)) := by
      have hx : 0 < Real.log z / 2 := by linarith
      have hxy : Real.log z / 2 ≤ Real.log (⌊z⌋₊ : ℝ) := by linarith
      have hle := Real.rpow_le_rpow_of_nonpos hx hxy (by norm_num : (-(10 : ℝ)) ≤ 0)
      rw [psl_half_rpow_neg (Real.log z) hLzp] at hle
      exact hle
    have hB2 : 1 / (⌊z⌋₊ : ℝ) ≤ 2 * 10 ^ 10 * (Real.log z) ^ (-(10 : ℝ)) :=
      psl_inv_floor_le z hz
    have hB3 : |Real.log (Real.log (⌊z⌋₊ : ℝ)) - Real.log (Real.log z)| ≤
        (2 * 10 ^ 10 / Real.log 2) * (Real.log z) ^ (-(10 : ℝ)) := by
      rw [abs_sub_comm]
      exact psl_loglog_diff_le z hz
    have hA1 : |S - Real.log (Real.log (⌊z⌋₊ : ℝ)) - c| ≤
        C * (((2 : ℝ) ^ 10 + 2 * 10 ^ 10) * (Real.log z) ^ (-(10 : ℝ))) := by
      refine le_trans hhyp ?_
      apply mul_le_mul_of_nonneg_left _ hC
      have hsum := add_le_add hB1 hB2
      calc (Real.log (⌊z⌋₊ : ℝ)) ^ (-(10 : ℝ)) + 1 / (⌊z⌋₊ : ℝ)
          ≤ (2 : ℝ) ^ 10 * (Real.log z) ^ (-(10 : ℝ)) + 2 * 10 ^ 10 * (Real.log z) ^ (-(10 : ℝ)) := hsum
        _ = ((2 : ℝ) ^ 10 + 2 * 10 ^ 10) * (Real.log z) ^ (-(10 : ℝ)) := by ring
    have htri : |S - Real.log (Real.log z) - c| ≤
        |S - Real.log (Real.log (⌊z⌋₊ : ℝ)) - c| +
          |Real.log (Real.log (⌊z⌋₊ : ℝ)) - Real.log (Real.log z)| := by
      have heq : S - Real.log (Real.log z) - c =
          (S - Real.log (Real.log (⌊z⌋₊ : ℝ)) - c) +
            (Real.log (Real.log (⌊z⌋₊ : ℝ)) - Real.log (Real.log z)) := by ring
      rw [heq]
      exact abs_add_le _ _
    have hfinal : |S - Real.log (Real.log z) - c| ≤
        (C * ((2 : ℝ) ^ 10 + 2 * 10 ^ 10) + 2 * 10 ^ 10 / Real.log 2) *
          (Real.log z) ^ (-(10 : ℝ)) := by
      have hsum := add_le_add hA1 hB3
      calc |S - Real.log (Real.log z) - c|
          ≤ |S - Real.log (Real.log (⌊z⌋₊ : ℝ)) - c| +
              |Real.log (Real.log (⌊z⌋₊ : ℝ)) - Real.log (Real.log z)| := htri
        _ ≤ C * (((2 : ℝ) ^ 10 + 2 * 10 ^ 10) * (Real.log z) ^ (-(10 : ℝ))) +
              (2 * 10 ^ 10 / Real.log 2) * (Real.log z) ^ (-(10 : ℝ)) := hsum
        _ = (C * ((2 : ℝ) ^ 10 + 2 * 10 ^ 10) + 2 * 10 ^ 10 / Real.log 2) *
              (Real.log z) ^ (-(10 : ℝ)) := by ring
    have hconv : (Real.log z) ^ (-(10 : ℝ)) = (Real.log z) ^ (-(10 : ℤ)) :=
      psl_rpow_eq_zpow (Real.log z)
    rw [← hconv]
    exact hfinal

end Commons.Analysis.Asymptotics