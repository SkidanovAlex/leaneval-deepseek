import Mathlib
import Submission.Commons.NumberTheory.Divisors.small_divisor_tau_le
import Submission.Commons.NumberTheory.Divisors.sum_divisors_filter_swap_of_pred

namespace Commons.NumberTheory.DivisorSum

open Finset

/-- Core pointwise inequality: for every `n ≥ 1` the eighth power of the divisor count
`τ n` is bounded by the sum, over the divisors `d` of `n` with `d ^ 3 ≤ n`, of
`(2 τ d) ^ 40`.  It is obtained from `small_divisor_tau_le` with `k = 3`: there is a
divisor `d` with `d ^ 3 ≤ n` and `τ n ≤ (2 τ d) ^ (3 log 3 / log 2)`, and
`3 log 3 / log 2 ≈ 4.755 < 5`, so `(τ n) ^ 8 ≤ (2 τ d) ^ 40`. -/
private theorem tau_pow_eight_le_sum_dvd_cube_aux (n : ℕ) (hn : 1 ≤ n) :
    ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ))
      ≤ ∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ n),
          (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) := by
  obtain ⟨d, hdvd, hdcube, hbound⟩ :=
    Commons.NumberTheory.Divisors.small_divisor_tau_le (k := 3) (by norm_num) hn
  have hn0 : n ≠ 0 := by omega
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hcard_ge : 1 ≤ d.divisors.card :=
    Finset.one_le_card.mpr ⟨1, Nat.one_mem_divisors.mpr hdpos.ne'⟩
  have hcard1 : (1:ℝ) ≤ (d.divisors.card : ℝ) := by exact_mod_cast hcard_ge
  have hA1 : (1:ℝ) ≤ 2 * (d.divisors.card : ℝ) := by linarith
  -- the exponent estimate `3 log 3 / log 2 ≤ 5` (equivalently `log 27 ≤ log 32`)
  have hE : (3:ℝ) * Real.log 3 / Real.log 2 ≤ 5 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h27 : Real.log (27:ℝ) = 3 * Real.log 3 := by
      rw [show (27:ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have h32 : Real.log (32:ℝ) = 5 * Real.log 2 := by
      rw [show (32:ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
      norm_num
    have hle : Real.log (27:ℝ) ≤ Real.log (32:ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [h27, h32] at hle
    rw [div_le_iff₀ hlog2]
    linarith
  have hle5 : (n.divisors.card : ℝ) ≤ (2 * (d.divisors.card : ℝ)) ^ 5 := by
    calc (n.divisors.card : ℝ)
        ≤ (2 * (d.divisors.card : ℝ)) ^ ((3:ℝ) * Real.log 3 / Real.log 2) := hbound
      _ ≤ (2 * (d.divisors.card : ℝ)) ^ (5:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hA1 hE
      _ = (2 * (d.divisors.card : ℝ)) ^ 5 := Real.rpow_natCast _ 5
  have hτ8 : (n.divisors.card : ℝ) ^ 8 ≤ (2 * (d.divisors.card : ℝ)) ^ 40 := by
    calc (n.divisors.card : ℝ) ^ 8
        ≤ ((2 * (d.divisors.card : ℝ)) ^ 5) ^ 8 :=
            pow_le_pow_left₀ (by positivity) hle5 8
      _ = (2 * (d.divisors.card : ℝ)) ^ 40 := by rw [← pow_mul]
  have hsingle : ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ))
      ≤ (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact hτ8
  have hdmem : d ∈ n.divisors.filter (fun e => e ^ 3 ≤ n) := by
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨hdvd, hn0⟩, hdcube⟩
  have hnonneg : ∀ b ∈ n.divisors.filter (fun e => e ^ 3 ≤ n),
      0 ≤ (2 * (b.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) :=
    fun b _ => Real.rpow_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg b.divisors.card)) _
  exact le_trans hsingle (Finset.single_le_sum hnonneg hdmem)

theorem sum_mul_tau_pow_eight_le_cube (a : ℕ → ℝ) (ha : ∀ n : ℕ, 0 ≤ a n) (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, a n * ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ)))
      ≤ ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 3 ≤ x),
          (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) *
            (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n) := by
  have hstep : (∑ n ∈ Finset.Icc 1 x, a n * ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ)))
      ≤ ∑ n ∈ Finset.Icc 1 x,
          a n * (∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ x),
                    (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ)) := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
    refine mul_le_mul_of_nonneg_left ?_ (ha n)
    calc ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ))
        ≤ ∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ n),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) :=
              tau_pow_eight_le_sum_dvd_cube_aux n hn1
      _ ≤ ∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ x),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro d hd
              rw [Finset.mem_filter] at hd ⊢
              exact ⟨hd.1, le_trans hd.2 hnx⟩
            · intro d _ _
              exact Real.rpow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) _
  have heq : (∑ n ∈ Finset.Icc 1 x,
        a n * (∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ x),
                  (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ)))
      = ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 3 ≤ x),
          (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) *
            (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n) := by
    calc ∑ n ∈ Finset.Icc 1 x,
          a n * (∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ x),
                    (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ))
        = ∑ n ∈ Finset.Icc 1 x,
            ∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ x),
              a n * (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [Finset.mul_sum]
      _ = ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 3 ≤ x),
            ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n),
              a n * (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) :=
            Commons.NumberTheory.Divisors.sum_divisors_filter_swap_of_pred
              (fun d => d ^ 3 ≤ x)
              (fun n d => a n * (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ))
      _ = ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 3 ≤ x),
            (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) *
              (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), a n) := by
            refine Finset.sum_congr rfl (fun d _ => ?_)
            rw [← Finset.sum_mul, mul_comm]
  exact le_trans hstep (le_of_eq heq)

end Commons.NumberTheory.DivisorSum
