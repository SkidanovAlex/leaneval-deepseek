import Mathlib
import Submission.Work.ZeroDensity.Ingham.doubleSumUpperReduce
import Submission.Work.ZeroDensity.Ingham.upperTermOneBound
import Submission.Work.ZeroDensity.Ingham.upperTermTwoBound

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

/-- Pointwise AM–GM summed over the upper triangle: for `w ≥ 0` on the summation range,
`2 ∑_{m<n} f m f n w ≤ ∑_{m<n} f m² w + ∑_{m<n} f n² w`. -/
theorem twoMulSum_le (Y : ℕ) (f : ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ m ∈ Finset.Icc 1 Y, ∀ n ∈ Finset.Icc (m+1) Y, 0 ≤ w m n) :
    2 * (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc (m+1) Y, f m * f n * w m n)
      ≤ (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc (m+1) Y, f m ^ 2 * w m n)
        + (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc (m+1) Y, f n ^ 2 * w m n) := by
  have h : ∀ m ∈ Finset.Icc 1 Y,
      2 * (∑ n ∈ Finset.Icc (m+1) Y, f m * f n * w m n)
        ≤ (∑ n ∈ Finset.Icc (m+1) Y, f m ^ 2 * w m n)
          + (∑ n ∈ Finset.Icc (m+1) Y, f n ^ 2 * w m n) := by
    intro m hm
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    have hw' : 0 ≤ w m n := hw m hm n hn
    have h2 : 2 * (f m * f n) ≤ f m ^ 2 + f n ^ 2 := by nlinarith [sq_nonneg (f m - f n)]
    nlinarith [mul_le_mul_of_nonneg_right h2 hw']
  calc 2 * (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc (m+1) Y, f m * f n * w m n)
      = ∑ m ∈ Finset.Icc 1 Y, 2 * (∑ n ∈ Finset.Icc (m+1) Y, f m * f n * w m n) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ Finset.Icc 1 Y, ((∑ n ∈ Finset.Icc (m+1) Y, f m ^ 2 * w m n)
          + (∑ n ∈ Finset.Icc (m+1) Y, f n ^ 2 * w m n)) := Finset.sum_le_sum h
    _ = (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc (m+1) Y, f m ^ 2 * w m n)
        + (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc (m+1) Y, f n ^ 2 * w m n) := by
        rw [Finset.sum_add_distrib]

theorem divPairKernelBound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 2 ≤ Y →
      (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
          ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ) *
            max (K : ℝ) (K' : ℝ) / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|))
        ≤ C * (Y : ℝ) * (Real.log (Y : ℝ)) ^ 4 := by
  obtain ⟨C1, hC1pos, hC1⟩ := upperTermOneBound
  obtain ⟨C2, hC2pos, hC2⟩ := upperTermTwoBound
  refine ⟨16 * (C1 + C2), by positivity, ?_⟩
  intro Y hY
  have hY2R : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hYpos : (0 : ℝ) < (Y : ℝ) := by linarith
  have hw : ∀ m ∈ Finset.Icc 1 Y, ∀ n ∈ Finset.Icc (m+1) Y,
      0 ≤ (n : ℝ) / ((n : ℝ) - (m : ℝ)) := by
    intro m hm n hn
    have hnm : m + 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hmn : (m : ℝ) < (n : ℝ) := by
      have : ((m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
      push_cast at this; linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h1 : 1 ≤ n := by omega
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      linarith
    exact div_nonneg (le_of_lt hnpos) (by linarith)
  have h2U := twoMulSum_le Y (fun n => ((Nat.divisors n).card : ℝ) / Real.sqrt (n : ℝ))
      (fun m n => (n : ℝ) / ((n : ℝ) - (m : ℝ))) hw
  have hU1 := hC1 Y hY
  have hU2 := hC2 Y hY
  have hlogpow : (Real.log (2 * (Y : ℝ))) ^ 4 ≤ 16 * (Real.log (Y : ℝ)) ^ 4 := by
    have hlog2Y_nn : 0 ≤ Real.log (2 * (Y : ℝ)) := Real.log_nonneg (by linarith)
    have h2Ysq : 2 * (Y : ℝ) ≤ (Y : ℝ) ^ 2 := by nlinarith
    have hlog_le : Real.log (2 * (Y : ℝ)) ≤ 2 * Real.log (Y : ℝ) := by
      calc Real.log (2 * (Y : ℝ)) ≤ Real.log ((Y : ℝ) ^ 2) :=
            Real.log_le_log (by linarith) h2Ysq
        _ = 2 * Real.log (Y : ℝ) := by rw [Real.log_pow]; norm_num
    calc (Real.log (2 * (Y : ℝ))) ^ 4 ≤ (2 * Real.log (Y : ℝ)) ^ 4 :=
          pow_le_pow_left₀ hlog2Y_nn hlog_le 4
      _ = 16 * (Real.log (Y : ℝ)) ^ 4 := by ring
  have hnonneg : 0 ≤ (C1 + C2) * (Y : ℝ) := by positivity
  calc (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
          ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ) *
            max (K : ℝ) (K' : ℝ) / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|))
      ≤ 2 * (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc (m+1) Y,
            (((Nat.divisors m).card : ℝ) / Real.sqrt (m : ℝ))
              * (((Nat.divisors n).card : ℝ) / Real.sqrt (n : ℝ))
              * ((n : ℝ) / ((n : ℝ) - (m : ℝ)))) := doubleSumUpperReduce Y
    _ ≤ (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc (m+1) Y,
            (((Nat.divisors m).card : ℝ) / Real.sqrt (m : ℝ)) ^ 2
              * ((n : ℝ) / ((n : ℝ) - (m : ℝ))))
          + (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc (m+1) Y,
            (((Nat.divisors n).card : ℝ) / Real.sqrt (n : ℝ)) ^ 2
              * ((n : ℝ) / ((n : ℝ) - (m : ℝ)))) := h2U
    _ ≤ (C1 * (Y : ℝ) * (Real.log (2 * (Y : ℝ))) ^ 4)
          + (C2 * (Y : ℝ) * (Real.log (2 * (Y : ℝ))) ^ 4) := add_le_add hU1 hU2
    _ = (C1 + C2) * (Y : ℝ) * (Real.log (2 * (Y : ℝ))) ^ 4 := by ring
    _ ≤ (C1 + C2) * (Y : ℝ) * (16 * (Real.log (Y : ℝ)) ^ 4) :=
        mul_le_mul_of_nonneg_left hlogpow hnonneg
    _ = 16 * (C1 + C2) * (Y : ℝ) * (Real.log (Y : ℝ)) ^ 4 := by ring

end Work.ZeroDensity.Ingham
