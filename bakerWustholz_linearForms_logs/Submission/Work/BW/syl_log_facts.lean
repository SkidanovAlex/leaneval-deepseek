import Mathlib
import Submission.Work.BW.ulcm_le_three_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # Numeric facts for the Sylvester weights -/

namespace Work.BW

open Finset

noncomputable section

private lemma syl_two_le' : ∀ n : ℕ, 2 ≤ syl n := by
  intro n
  induction n with
  | zero => show 2 ≤ 2; norm_num
  | succ n ih =>
      show 2 ≤ syl n * (syl n - 1) + 1
      have h1 : 1 ≤ syl n - 1 := by omega
      have h2 : 0 < syl n * (syl n - 1) := Nat.mul_pos (by omega) (by omega)
      omega

private lemma syl_mono' : Monotone syl := by
  apply monotone_nat_of_le_succ
  intro n
  show syl n ≤ syl n * (syl n - 1) + 1
  have h1 : 1 ≤ syl n - 1 := by have := syl_two_le' n; omega
  have h2 : syl n * 1 ≤ syl n * (syl n - 1) := Nat.mul_le_mul_left _ h1
  omega

private lemma syl_four : syl 4 = 1807 := rfl

private lemma syl_ge_1807 {i : ℕ} (hi : 4 ≤ i) : 1807 ≤ syl i := by
  have h := syl_mono' hi
  rwa [syl_four] at h

private lemma syl_succ_cast (i : ℕ) :
    (syl (i + 1) : ℝ) = (syl i : ℝ) * ((syl i : ℝ) - 1) + 1 := by
  have h1 : 1 ≤ syl i := by have := syl_two_le' i; omega
  have h : syl (i + 1) = syl i * (syl i - 1) + 1 := rfl
  rw [h, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub h1]
  ring

private lemma syl_succ_le_sq (i : ℕ) : (syl (i + 1) : ℝ) ≤ (syl i : ℝ) ^ 2 := by
  rw [syl_succ_cast i]
  have h : (2 : ℝ) ≤ (syl i : ℝ) := by exact_mod_cast syl_two_le' i
  nlinarith [sq_nonneg ((syl i : ℝ) - 1)]

private lemma syl_sq_le_succ (i : ℕ) : (syl i : ℝ) ^ 2 ≤ 2 * (syl (i + 1) : ℝ) := by
  rw [syl_succ_cast i]
  have h : (2 : ℝ) ≤ (syl i : ℝ) := by exact_mod_cast syl_two_le' i
  nlinarith [sq_nonneg ((syl i : ℝ) - 1)]

private def aw (i : ℕ) : ℝ := Real.log (syl i) / (syl i : ℝ)

private lemma aw_nonneg (i : ℕ) : 0 ≤ aw i := by
  have h1 : (1 : ℝ) ≤ (syl i : ℝ) := by
    have := syl_two_le' i
    exact_mod_cast (show (1 : ℕ) ≤ syl i by omega)
  rw [aw]
  exact div_nonneg (Real.log_nonneg h1) (by linarith)

private lemma aw_succ_le (i : ℕ) : aw (i + 1) ≤ 4 * aw i / (syl i : ℝ) := by
  have hpos : (0 : ℝ) < (syl i : ℝ) := by
    have := syl_two_le' i
    exact_mod_cast (show (0 : ℕ) < syl i by omega)
  have hlog_nonneg : 0 ≤ Real.log (syl i : ℝ) := by
    apply Real.log_nonneg
    have := syl_two_le' i
    exact_mod_cast (show (1 : ℕ) ≤ syl i by omega)
  have hpos' : (0 : ℝ) < (syl (i + 1) : ℝ) := by
    have := syl_two_le' (i + 1)
    exact_mod_cast (show (0 : ℕ) < syl (i + 1) by omega)
  have hlog : Real.log (syl (i + 1) : ℝ) ≤ 2 * Real.log (syl i : ℝ) := by
    have h : Real.log (syl (i + 1) : ℝ) ≤ Real.log ((syl i : ℝ) ^ 2) :=
      Real.log_le_log hpos' (syl_succ_le_sq i)
    rwa [Real.log_pow] at h
  have hnum : 0 ≤ Real.log (syl (i + 1) : ℝ) := by
    apply Real.log_nonneg
    have := syl_two_le' (i + 1)
    exact_mod_cast (show (1 : ℕ) ≤ syl (i + 1) by omega)
  have hden_pos : 0 < (syl i : ℝ) ^ 2 / 2 := by positivity
  have hden : (syl i : ℝ) ^ 2 / 2 ≤ (syl (i + 1) : ℝ) := by linarith [syl_sq_le_succ i]
  calc aw (i + 1) = Real.log (syl (i + 1) : ℝ) / (syl (i + 1) : ℝ) := rfl
    _ ≤ (2 * Real.log (syl i : ℝ)) / ((syl i : ℝ) ^ 2 / 2) :=
        div_le_div₀ (by linarith) hlog hden_pos hden
    _ = 4 * aw i / (syl i : ℝ) := by
        rw [aw]
        field_simp
        ring

private lemma aw_succ_le_half {i : ℕ} (hi : 4 ≤ i) : aw (i + 1) ≤ (1 / 2) * aw i := by
  have h := aw_succ_le i
  have h1807 : (1807 : ℝ) ≤ (syl i : ℝ) := by
    have := syl_ge_1807 hi
    exact_mod_cast this
  have haw : 0 ≤ aw i := aw_nonneg i
  have hstep : 4 * aw i / (syl i : ℝ) ≤ (4 / 1807) * aw i := by
    have h1 : 4 * aw i / (syl i : ℝ) ≤ 4 * aw i / 1807 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) h1807
    have h2 : 4 * aw i / (1807 : ℝ) = (4 / 1807) * aw i := by ring
    linarith [h1, h2]
  have h3 : (4 / 1807 : ℝ) * aw i ≤ (1 / 2) * aw i := by nlinarith
  linarith [h, hstep, h3]

private lemma log7_le : Real.log 7 ≤ (73 / 26 : ℝ) * Real.log 2 := by
  have h : (7 : ℝ) ^ 26 ≤ (2 : ℝ) ^ 73 := by norm_num
  have hlog : (26 : ℝ) * Real.log 7 ≤ (73 : ℝ) * Real.log 2 := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < (7 : ℝ) ^ 26) h
    rwa [Real.log_pow, Real.log_pow] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 26)]
  linarith

private lemma log43_le : Real.log 43 ≤ (38 / 7 : ℝ) * Real.log 2 := by
  have h : (43 : ℝ) ^ 7 ≤ (2 : ℝ) ^ 38 := by norm_num
  have hlog : (7 : ℝ) * Real.log 43 ≤ (38 : ℝ) * Real.log 2 := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < (43 : ℝ) ^ 7) h
    rwa [Real.log_pow, Real.log_pow] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 7)]
  linarith

private lemma log1807_le : Real.log 1807 ≤ (65 / 6 : ℝ) * Real.log 2 := by
  have h : (1807 : ℝ) ^ 6 ≤ (2 : ℝ) ^ 65 := by norm_num
  have hlog : (6 : ℝ) * Real.log 1807 ≤ (65 : ℝ) * Real.log 2 := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < (1807 : ℝ) ^ 6) h
    rwa [Real.log_pow, Real.log_pow] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
  linarith

private def C0 : ℝ := 0.6931471808 / 2
private def C1 : ℝ := 1.0986122888 / 3
private def C2 : ℝ := (73 / 26) * 0.6931471808 / 7
private def C3 : ℝ := (38 / 7) * 0.6931471808 / 43
private def C4 : ℝ := (65 / 6) * 0.6931471808 / 1807
private def B5 : ℝ := (65 / 3) * 0.6931471808 / 3263443

private lemma B5_nonneg : 0 ≤ B5 := by unfold B5; norm_num

private lemma aw0_le : aw 0 ≤ C0 := by
  have h : syl 0 = 2 := rfl
  have haw : aw 0 = Real.log 2 / 2 := by simp only [aw, h]; norm_num
  rw [haw, C0]
  linarith [Real.log_two_lt_d9]

private lemma aw1_le : aw 1 ≤ C1 := by
  have h : syl 1 = 3 := rfl
  have haw : aw 1 = Real.log 3 / 3 := by simp only [aw, h]; norm_num
  rw [haw, C1]
  linarith [Real.log_three_lt_d9]

private lemma aw2_le : aw 2 ≤ C2 := by
  have h : syl 2 = 7 := rfl
  have haw : aw 2 = Real.log 7 / 7 := by simp only [aw, h]; norm_num
  have h1 : (73 / 26 : ℝ) * Real.log 2 ≤ (73 / 26 : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) (by norm_num)
  rw [haw, C2]
  linarith [log7_le, h1]

private lemma aw3_le : aw 3 ≤ C3 := by
  have h : syl 3 = 43 := rfl
  have haw : aw 3 = Real.log 43 / 43 := by simp only [aw, h]; norm_num
  have h1 : (38 / 7 : ℝ) * Real.log 2 ≤ (38 / 7 : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) (by norm_num)
  rw [haw, C3]
  linarith [log43_le, h1]

private lemma aw4_le : aw 4 ≤ C4 := by
  have h : syl 4 = 1807 := rfl
  have haw : aw 4 = Real.log 1807 / 1807 := by simp only [aw, h]; norm_num
  have h1 : (65 / 6 : ℝ) * Real.log 2 ≤ (65 / 6 : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) (by norm_num)
  rw [haw, C4]
  linarith [log1807_le, h1]

private lemma aw5_le : aw 5 ≤ B5 := by
  have h : syl 5 = 3263443 := rfl
  have haw : aw 5 = Real.log 3263443 / 3263443 := by simp only [aw, h]; norm_num
  have hle : (3263443 : ℝ) ≤ (1807 : ℝ) ^ 2 := by norm_num
  have hlog : Real.log (3263443 : ℝ) ≤ 2 * Real.log 1807 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3263443) hle
    rwa [Real.log_pow] at hh
  have h1 : (65 / 6 : ℝ) * Real.log 2 ≤ (65 / 6 : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) (by norm_num)
  have h2 : (2 : ℝ) * Real.log 1807 ≤ (2 : ℝ) * ((65 / 6) * 0.6931471808) :=
    mul_le_mul_of_nonneg_left (by linarith [log1807_le, h1]) (by norm_num)
  have h3 : Real.log (3263443 : ℝ) ≤ (65 / 3) * 0.6931471808 := by linarith
  rw [haw, B5]
  linarith

private lemma aw_geo (j : ℕ) : aw (5 + j) ≤ B5 * (1 / 2) ^ j := by
  induction j with
  | zero => simpa using aw5_le
  | succ j ih =>
      have hstep : 5 + (j + 1) = (5 + j) + 1 := by omega
      rw [hstep]
      have h1 : aw ((5 + j) + 1) ≤ (1 / 2) * aw (5 + j) := aw_succ_le_half (by omega)
      have h2 : (1 / 2) * aw (5 + j) ≤ (1 / 2) * (B5 * (1 / 2) ^ j) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      calc aw ((5 + j) + 1) ≤ (1 / 2) * aw (5 + j) := h1
        _ ≤ (1 / 2) * (B5 * (1 / 2) ^ j) := h2
        _ = B5 * (1 / 2) ^ (j + 1) := by rw [pow_succ]; ring

private lemma tail_le (m : ℕ) : (∑ j ∈ Finset.range m, aw (5 + j)) ≤ 2 * B5 := by
  have h1 : (∑ j ∈ Finset.range m, aw (5 + j)) ≤ ∑ j ∈ Finset.range m, B5 * (1 / 2) ^ j :=
    Finset.sum_le_sum (fun j _ => aw_geo j)
  have h2 : (∑ j ∈ Finset.range m, B5 * (1 / 2) ^ j) = B5 * ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum]
  have h3 : (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j) ≤ 2 := by
    have hgeom : ∀ k : ℕ, (∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j) ≤ 2 - 2 * (1 / 2) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Finset.sum_range_succ, pow_succ]
          have hpow : (0 : ℝ) < (1 / 2) ^ k := by positivity
          linarith
    have hp : 0 ≤ 2 * (1 / 2 : ℝ) ^ m := by positivity
    linarith [hgeom m]
  have h5 : B5 * (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j) ≤ B5 * 2 :=
    mul_le_mul_of_nonneg_left h3 B5_nonneg
  linarith [h1, h2, h5]

private lemma prefix_le : (∑ i ∈ Finset.range 5, aw i) ≤ C0 + C1 + C2 + C3 + C4 := by
  have h0 := aw0_le
  have h1 := aw1_le
  have h2 := aw2_le
  have h3 := aw3_le
  have h4 := aw4_le
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith

private def K : ℝ := C0 + C1 + C2 + C3 + C4 + 2 * B5

private lemma K_le : K ≤ 1.0826 := by
  unfold K C0 C1 C2 C3 C4 B5
  norm_num

private lemma sum_le (N : ℕ) : (∑ i ∈ Finset.range N, aw i) ≤ K := by
  rcases le_or_gt N 5 with hN | hN
  · have hsub : Finset.range N ⊆ Finset.range 5 := Finset.range_subset_range.mpr hN
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => aw_nonneg i)
    have hpre := prefix_le
    have hB5 := B5_nonneg
    unfold K
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m, N = 5 + m := ⟨N - 5, by omega⟩
    rw [Finset.sum_range_add]
    have h1 := prefix_le
    have h2 := tail_le m
    unfold K
    linarith

/-- Numeric facts for the Sylvester weights (`Lw n = ∑_{syl i ≤ n} log (syl i)/syl i`, with `syl`
Sylvester's sequence from `Submission/Work/BW/ulcm_le_three_pow.lean`):
`1.0986 ≤ log 3 ≤ 1.0987`, `log 2 ≤ 0.6932`, and `Lw n ≤ 1.0826` for every `n`
(the first four terms give `1.07824`, then `log 1807/1807 < 0.00416`, `log 3263443/3263443 < 5·10⁻⁶`
and the tail decays doubly exponentially since `syl (i+1) ≥ syl i ^ 2 / 2`). -/
theorem syl_log_facts :
    (1.0986 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1.0987 ∧ Real.log 2 ≤ 0.6932 ∧
      (∀ n : ℕ, Lw n ≤ 1.0826) := by
  refine ⟨by linarith [Real.log_three_gt_d9], by linarith [Real.log_three_lt_d9],
    by linarith [Real.log_two_lt_d9], ?_⟩
  intro n
  have hle : Lw n ≤ ∑ i ∈ Finset.range (n + 1), aw i := by
    unfold Lw
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => ?_)
    exact aw_nonneg i
  exact le_trans hle (le_trans (sum_le (n + 1)) K_le)

end

end Work.BW
