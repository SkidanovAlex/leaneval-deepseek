import Mathlib

/-!
# A crude bound for the summatory divisor function

We prove that the summatory divisor function is `O(Y log Y)`:

`∑_{b ≤ Y} d(b) ≤ 4 * (Y + 1) * log (Y + 2)`

where `d(b) = b.divisors.card` is the number of divisors of `b`.

The proof is the classical one:

* `d(b) = #{d ≤ Y : d ∣ b}` for `b ≤ Y`;
* exchanging the two finite sums turns the sum into `∑_{d ≤ Y} #{b ≤ Y : d ∣ b}`;
* the inner cardinality is at most `Y / d`, and `⌊Y/d⌋ ≤ Y/d` over the reals;
* finally `∑_{d=1}^{Y} 1/d ≤ 1 + log Y` (a harmonic-sum bound,
  proved by induction from `1 - x⁻¹ ≤ log x`).
-/

namespace Work.FIArea7

open Finset

/-- Harmonic-sum bound: `∑_{d=1}^{n} 1/d ≤ 1 + log n` for every `n : ℕ`
(where `log 0 = 0` by convention). -/
lemma divisorSum_sum_inv_Icc_le (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, (1 / (d : ℝ))) ≤ 1 + Real.log n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
      have hnp1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      have hx : (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) := div_pos hnp1 hnR
      have h1 := Real.one_sub_inv_le_log_of_pos hx
      rw [Real.log_div (ne_of_gt hnp1) (ne_of_gt hnR)] at h1
      have heq : (1 : ℝ) - (((n : ℝ) + 1) / (n : ℝ))⁻¹ = 1 / ((n : ℝ) + 1) := by
        rw [inv_div]; field_simp; ring
      rw [heq] at h1
      push_cast
      linarith

/-- The number of multiples of `d` in `[1, Y]` is at most `Y / d`. -/
lemma divisorSum_card_filter_dvd_Icc_le (Y d : ℕ) :
    ((Finset.Icc 1 Y).filter (fun b => d ∣ b)).card ≤ Y / d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hempty : (Finset.Icc 1 Y).filter (fun b => 0 ∣ b) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.zero_dvd] at hb
      omega
    rw [hempty, Finset.card_empty, Nat.div_zero]
  · have hset : (Finset.Icc 1 Y).filter (fun b => d ∣ b)
        = (Finset.Icc 1 (Y / d)).image (fun k => d * k) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hb1, hbY⟩, hdvd⟩
        exact ⟨b / d, ⟨⟨by rw [Nat.le_div_iff_mul_le hd]; simpa using Nat.le_of_dvd (by omega) hdvd,
          Nat.div_le_div_right hbY⟩, Nat.mul_div_cancel' hdvd⟩⟩
      · rintro ⟨k, ⟨hk1, hkY⟩, rfl⟩
        exact ⟨⟨by
          rw [Nat.one_le_iff_ne_zero]
          exact Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hd) (Nat.pos_iff_ne_zero.mp hk1),
          le_trans (Nat.mul_le_mul_left d hkY) (Nat.mul_div_le Y d)⟩, ⟨k, rfl⟩⟩
    calc ((Finset.Icc 1 Y).filter (fun b => d ∣ b)).card
        = ((Finset.Icc 1 (Y / d)).image (fun k => d * k)).card := by rw [hset]
      _ = (Finset.Icc 1 (Y / d)).card := Finset.card_image_of_injective _ (fun a b hab => Nat.mul_left_cancel hd hab)
      _ ≤ Y / d := by rw [Nat.card_Icc, Nat.add_sub_cancel]

/-- Elementary real inequality closing the estimate. -/
lemma divisorSum_arith_le (Y : ℕ) :
    (Y : ℝ) * (1 + Real.log Y) ≤ 4 * ((Y : ℝ) + 1) * Real.log ((Y : ℝ) + 2) := by
  rcases Nat.eq_zero_or_pos Y with h | h
  · subst h
    have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    simp only [Nat.cast_zero, zero_mul, zero_add, mul_one]
    exact mul_nonneg (by norm_num) hpos.le
  · have h1 : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast h
    have hlogYle : Real.log (Y : ℝ) ≤ Real.log ((Y : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlogle : (1 / 3 : ℝ) ≤ Real.log ((Y : ℝ) + 2) := by
      have h2 : Real.log 2 ≤ Real.log ((Y : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
      have := Real.log_two_gt_d9
      linarith
    nlinarith

/-- The summatory divisor function is `O(Y log Y)`. -/
lemma divisorSum_main (Y : ℕ) :
    (∑ b ∈ Finset.Icc 1 Y, ((b.divisors.card : ℕ) : ℝ))
      ≤ 4 * ((Y : ℝ) + 1) * Real.log ((Y : ℝ) + 2) := by
  have step1 : (∑ b ∈ Finset.Icc 1 Y, ((b.divisors.card : ℕ) : ℝ))
      = ∑ b ∈ Finset.Icc 1 Y, ∑ d ∈ Finset.Icc 1 Y, (if d ∣ b then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hb1, hbY⟩ := hb
    have hbne : b ≠ 0 := by omega
    have hbpos : 0 < b := by omega
    have hset : b.divisors = (Finset.Icc 1 Y).filter (fun d => d ∣ b) := by
      ext d
      rw [Nat.mem_divisors]
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, -⟩
        exact ⟨⟨Nat.succ_le_of_lt (Nat.pos_of_dvd_of_pos hdvd hbpos),
          le_trans (Nat.le_of_dvd hbpos hdvd) hbY⟩, hdvd⟩
      · rintro ⟨⟨hd1, -⟩, hdvd⟩
        exact ⟨hdvd, hbne⟩
    rw [hset, Finset.card_eq_sum_ones]
    push_cast
    rw [Finset.sum_filter]
  have step3 : ∀ d ∈ Finset.Icc 1 Y,
      (∑ b ∈ Finset.Icc 1 Y, (if d ∣ b then (1 : ℝ) else 0))
        = (((Finset.Icc 1 Y).filter (fun b => d ∣ b)).card : ℝ) := by
    intro d hd
    rw [← Finset.sum_filter]
    rw [Finset.card_eq_sum_ones]
    push_cast
    rfl
  calc (∑ b ∈ Finset.Icc 1 Y, ((b.divisors.card : ℕ) : ℝ))
      = ∑ d ∈ Finset.Icc 1 Y, (((Finset.Icc 1 Y).filter (fun b => d ∣ b)).card : ℝ) := by
        rw [step1, Finset.sum_comm]
        exact Finset.sum_congr rfl step3
    _ ≤ ∑ d ∈ Finset.Icc 1 Y, (Y : ℝ) / (d : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact le_trans (Nat.cast_le.mpr (divisorSum_card_filter_dvd_Icc_le Y d)) Nat.cast_div_le
    _ = (Y : ℝ) * ∑ d ∈ Finset.Icc 1 Y, (1 / (d : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [div_eq_mul_inv, one_div]
    _ ≤ (Y : ℝ) * (1 + Real.log Y) :=
        mul_le_mul_of_nonneg_left (divisorSum_sum_inv_Icc_le Y) (Nat.cast_nonneg Y)
    _ ≤ 4 * ((Y : ℝ) + 1) * Real.log ((Y : ℝ) + 2) := divisorSum_arith_le Y

theorem divisor_sum_Icc_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ,
      (∑ b ∈ Finset.Icc 1 Y, ((b.divisors.card : ℕ) : ℝ))
        ≤ C * ((Y : ℝ) + 1) * Real.log ((Y : ℝ) + 2) := by
  exact ⟨4, by norm_num, fun Y => divisorSum_main Y⟩

end Work.FIArea7
