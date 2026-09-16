import Mathlib
import Submission.Commons.NumberTheory.Goldbach.vaughan_identity
import Submission.Commons.Analysis.ExponentialSums.third_derivative_test

open scoped BigOperators

namespace Commons.NumberTheory.Goldbach

/-- Reindex a sum over the multiples of `d` inside `[1, M]` by writing `n = d * m`. -/
lemma sum_Icc_filter_dvd_eq {M d : ℕ} (hd : 1 ≤ d) (h : ℕ → ℂ) :
    (∑ n ∈ (Finset.Icc 1 M).filter (fun n => d ∣ n), h n)
      = ∑ m ∈ Finset.Icc 1 (M / d), h (d * m) := by
  have hd0 : 0 < d := hd
  refine Finset.sum_bij (fun n _ => n / d) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnM⟩, hdv⟩ := hn
    rw [Finset.mem_Icc]
    refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdv) hd0, Nat.div_le_div_right hnM⟩
  · intro a1 ha1 a2 ha2 heq
    have h1 : d ∣ a1 := (Finset.mem_filter.mp ha1).2
    have h2 : d ∣ a2 := (Finset.mem_filter.mp ha2).2
    rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
  · intro b hb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hb1, hbM⟩ := hb
    refine ⟨d * b, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right d b⟩
      · calc (1 : ℕ) = 1 * 1 := by norm_num
          _ ≤ d * b := Nat.mul_le_mul hd hb1
      · have := (Nat.le_div_iff_mul_le hd0).mp hbM
        rwa [mul_comm b d] at this
    · rw [Nat.mul_div_right b hd0]
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact congrArg h (Nat.mul_div_cancel' hn.2).symm

/-- Exchange the order of summation in a double sum indexed by `(n, d)` with `d ∣ n`,
`1 ≤ n ≤ M`, `1 ≤ d ≤ U`, writing `n = d * m`. -/
lemma sum_Icc_filter_dvd_swap {M U : ℕ} (g : ℕ → ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 M, ∑ d ∈ (Finset.Icc 1 U).filter (fun d => d ∣ n), g n d)
      = ∑ d ∈ Finset.Icc 1 U, ∑ m ∈ Finset.Icc 1 (M / d), g (d * m) d := by
  have h1 : (∑ n ∈ Finset.Icc 1 M,
        ∑ d ∈ (Finset.Icc 1 U).filter (fun d => d ∣ n), g n d)
      = ∑ n ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 U, if d ∣ n then g n d else 0 := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_filter]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hdmem => ?_)
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
  rw [← Finset.sum_filter]
  exact sum_Icc_filter_dvd_eq hd1 (fun n => g n d)

theorem sum_vaughan_log_part {M U : ℕ} (η : ℕ → ℝ) (α : ℝ) :
    (∑ n ∈ Finset.Icc 1 M,
        (∑ d ∈ (Finset.Icc 1 U).filter (fun d => d ∣ n),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (Real.log ((n:ℝ) / (d:ℝ)) : ℂ))
        * (η n : ℂ) * Commons.Analysis.ExponentialSums.ch ((n:ℝ) * α))
      = ∑ d ∈ Finset.Icc 1 U, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ m ∈ Finset.Icc 1 (M / d),
            (Real.log (m:ℝ) : ℂ) * (η (d * m) : ℂ) *
              Commons.Analysis.ExponentialSums.ch (((d * m : ℕ) : ℝ) * α) := by
  trans ∑ n ∈ Finset.Icc 1 M, ∑ d ∈ (Finset.Icc 1 U).filter (fun d => d ∣ n),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (Real.log ((n:ℝ) / (d:ℝ)) : ℂ)
          * (η n : ℂ) * Commons.Analysis.ExponentialSums.ch ((n:ℝ) * α)
  · refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_mul, Finset.sum_mul]
  · rw [sum_Icc_filter_dvd_swap]
    refine Finset.sum_congr rfl (fun d hdmem => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
    have hdiv : (((d * m : ℕ) : ℝ) / (d : ℝ)) = (m : ℝ) := by
      rw [Nat.cast_mul]
      exact mul_div_cancel_left₀ (m : ℝ) (Nat.cast_ne_zero.mpr (by omega))
    rw [hdiv]
    ring

end Commons.NumberTheory.Goldbach
