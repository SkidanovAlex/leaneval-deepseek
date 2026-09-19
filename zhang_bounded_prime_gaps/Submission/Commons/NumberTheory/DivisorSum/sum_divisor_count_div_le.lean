import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.DivisorSum

/-- Reindexing the multiples of `d` in `[1,x]` by `k ↦ d*k`, `k ∈ [1, x/d]`. -/
lemma sum_Icc_filter_dvd (x d : ℕ) (hd : 1 ≤ d) (f : ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), f n)
      = ∑ k ∈ Finset.Icc 1 (x / d), f (d * k) := by
  classical
  have hdpos : 0 < d := by omega
  have hset : (Finset.Icc 1 x).filter (fun n => d ∣ n)
      = (Finset.Icc 1 (x / d)).image (fun k => d * k) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hn1, hnx⟩, hdn⟩
      refine ⟨n / d, ⟨⟨?_, ?_⟩, Nat.mul_div_cancel' hdn⟩⟩
      · exact (Nat.one_le_div_iff hdpos).mpr (Nat.le_of_dvd (by omega) hdn)
      · exact Nat.div_le_div_right hnx
    · rintro ⟨k, ⟨⟨hk1, hkx⟩, rfl⟩⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right d k⟩
      · have : 0 < d * k := Nat.mul_pos hdpos (by omega)
        omega
      · have h : k * d ≤ x := by
          calc k * d ≤ (x / d) * d := Nat.mul_le_mul_right d hkx
            _ = d * (x / d) := by ring
            _ ≤ x := Nat.mul_div_le x d
        calc d * k = k * d := by ring
          _ ≤ x := h
  rw [hset]
  apply Finset.sum_image
  intro a ha b hb hab
  exact Nat.mul_left_cancel hdpos hab

/-- The inner sum over `[1, x/d]` of `1/k` expressed via the harmonic number. -/
lemma harmonic_cast_eq_sum (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ Finset.Icc 1 n, (1:ℝ)/(k:ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- `1/k` summed over the multiples of `d` in `[1,x]`. -/
lemma sum_Icc_filter_dvd_inv (x d : ℕ) (hd : 1 ≤ d) :
    (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), (1:ℝ)/(n:ℝ))
      = (1/(d:ℝ)) * ∑ k ∈ Finset.Icc 1 (x / d), (1:ℝ)/(k:ℝ) := by
  rw [sum_Icc_filter_dvd x d hd (fun n => (1:ℝ)/(n:ℝ))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hd0 : (d:ℝ) ≠ 0 := by
    exact_mod_cast (by omega : d ≠ 0)
  have hk0 : (k:ℝ) ≠ 0 := by
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    exact_mod_cast (by omega : k ≠ 0)
  rw [Nat.cast_mul]
  field_simp

/-- The divisor-count divided by `n`, written as a sum over the divisors of `n`. -/
lemma card_divisors_div_eq (x n : ℕ) (hn1 : 1 ≤ n) (hnx : n ≤ x) :
    ((Nat.divisors n).card : ℝ) / (n:ℝ)
      = ∑ _d ∈ (Finset.Icc 1 x).filter (fun d => d ∣ n), (1:ℝ)/(n:ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hdvd : Nat.divisors n = (Finset.Icc 1 x).filter (fun d => d ∣ n) := by
    ext d
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdv, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdv (by omega),
        le_trans (Nat.le_of_dvd (by omega) hdv) hnx⟩, hdv⟩
    · rintro ⟨⟨hd1, _⟩, hdv⟩
      exact ⟨hdv, hn0⟩
  rw [hdvd, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- Bound on the inner harmonic-type sum. -/
lemma harmonic_div_bound (x d : ℕ) (hd : d ∈ Finset.Icc 1 x) :
    (∑ k ∈ Finset.Icc 1 (x/d), (1:ℝ)/(k:ℝ)) ≤ 1 + Real.log x - Real.log d := by
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdx : d ≤ x := (Finset.mem_Icc.mp hd).2
  have hdpos : 0 < d := by omega
  have hxpos : 0 < x := by omega
  have hdR : (0:ℝ) < d := by exact_mod_cast hdpos
  have hxR : (0:ℝ) < x := by exact_mod_cast hxpos
  calc (∑ k ∈ Finset.Icc 1 (x/d), (1:ℝ)/(k:ℝ))
      = (harmonic (x/d) : ℝ) := (harmonic_cast_eq_sum (x/d)).symm
    _ ≤ 1 + Real.log ((x/d : ℕ) : ℝ) := harmonic_le_one_add_log (x/d)
    _ ≤ 1 + Real.log ((x:ℝ)/(d:ℝ)) := by
          have hle : ((x/d : ℕ) : ℝ) ≤ (x:ℝ)/(d:ℝ) := Nat.cast_div_le
          have hpos : (0:ℝ) < ((x/d : ℕ) : ℝ) := by
            have h1 : 1 ≤ x / d := (Nat.one_le_div_iff hdpos).mpr hdx
            exact_mod_cast (by omega : 0 < x / d)
          linarith [Real.log_le_log hpos hle]
    _ = 1 + Real.log x - Real.log d := by
          rw [Real.log_div (ne_of_gt hxR) (ne_of_gt hdR)]; ring

lemma sum_divisor_count_div_le (x : ℕ) (hx : 1 ≤ x) :
    (∑ d ∈ Finset.Icc 1 x, ((Nat.divisors d).card : ℝ) / (d : ℝ))
      ≤ (1 + Real.log x) ^ 2 := by
  classical
  have key : (∑ n ∈ Finset.Icc 1 x, ((Nat.divisors n).card : ℝ) / (n:ℝ))
      = ∑ d ∈ Finset.Icc 1 x, (1/(d:ℝ)) * ∑ k ∈ Finset.Icc 1 (x/d), (1:ℝ)/(k:ℝ) := by
    calc
      (∑ n ∈ Finset.Icc 1 x, ((Nat.divisors n).card : ℝ) / (n:ℝ))
          = ∑ n ∈ Finset.Icc 1 x,
              ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ∣ n), (1:ℝ)/(n:ℝ) := by
              apply Finset.sum_congr rfl
              intro n hn
              exact card_divisors_div_eq x n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
      _ = ∑ n ∈ Finset.Icc 1 x,
              ∑ d ∈ Finset.Icc 1 x, (if d ∣ n then (1:ℝ)/(n:ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [Finset.sum_filter]
      _ = ∑ d ∈ Finset.Icc 1 x,
              ∑ n ∈ Finset.Icc 1 x, (if d ∣ n then (1:ℝ)/(n:ℝ) else 0) := by
              rw [Finset.sum_comm]
      _ = ∑ d ∈ Finset.Icc 1 x,
              ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), (1:ℝ)/(n:ℝ) := by
              apply Finset.sum_congr rfl
              intro d hd
              rw [Finset.sum_filter]
      _ = ∑ d ∈ Finset.Icc 1 x, (1/(d:ℝ)) * ∑ k ∈ Finset.Icc 1 (x/d), (1:ℝ)/(k:ℝ) := by
              apply Finset.sum_congr rfl
              intro d hd
              exact sum_Icc_filter_dvd_inv x d (Finset.mem_Icc.mp hd).1
  rw [key]
  have hterm : ∀ d ∈ Finset.Icc 1 x,
      (1/(d:ℝ)) * ∑ k ∈ Finset.Icc 1 (x/d), (1:ℝ)/(k:ℝ)
        ≤ (1/(d:ℝ)) * (1 + Real.log x - Real.log d) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdR : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact mul_le_mul_of_nonneg_left (harmonic_div_bound x d hd) (by positivity)
  calc (∑ d ∈ Finset.Icc 1 x, (1/(d:ℝ)) * ∑ k ∈ Finset.Icc 1 (x/d), (1:ℝ)/(k:ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 x, (1/(d:ℝ)) * (1 + Real.log x - Real.log d) :=
          Finset.sum_le_sum hterm
    _ = ∑ d ∈ Finset.Icc 1 x, ((1 + Real.log x) * (1/(d:ℝ)) - (Real.log d)/(d:ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          ring
    _ = (1 + Real.log x) * (∑ d ∈ Finset.Icc 1 x, (1:ℝ)/(d:ℝ))
          - ∑ d ∈ Finset.Icc 1 x, (Real.log d)/(d:ℝ) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ ≤ (1 + Real.log x) * (∑ d ∈ Finset.Icc 1 x, (1:ℝ)/(d:ℝ)) := by
          have hnn : 0 ≤ ∑ d ∈ Finset.Icc 1 x, (Real.log d)/(d:ℝ) := by
            apply Finset.sum_nonneg
            intro d hd
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
            have hdR : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
            exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd1)) (le_of_lt hdR)
          linarith
    _ ≤ (1 + Real.log x) * (1 + Real.log x) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · rw [← harmonic_cast_eq_sum x]
            exact harmonic_le_one_add_log x
          · have : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
            linarith
    _ = (1 + Real.log x) ^ 2 := by ring

end Commons.NumberTheory.DivisorSum