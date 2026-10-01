import Mathlib
import Submission.Work.ZeroDensity.Montgomery.normCpowAddIt_le_abel
import Submission.Work.ZeroDensity.Ingham.dirPolyWeightBound
import Submission.Work.ZeroDensity.Ingham.sumIccOneSplit
import Submission.Work.ZeroDensity.Ingham.sumIccWeightBound


open scoped BigOperators

namespace Work.ZeroDensity.Ingham

theorem dirPolySigmaReduction :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 2 ≤ N → ∀ (b : ℕ → ℂ) (σ t : ℝ), 0 ≤ σ →
      ‖∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2
        ≤ C * (‖b 1‖ ^ 2
            + ‖∑ n ∈ Finset.Icc 2 N, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2
            + ∑ k ∈ Finset.Icc 2 (N - 1),
                ‖∑ n ∈ Finset.Icc 2 k, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2
                  / ((k : ℝ) * Real.log (k : ℝ))) := by
  refine ⟨8, by norm_num, ?_⟩
  intro N hN b σ t hσ
  have hN1 : 1 ≤ N := by omega
  set P : ℕ → ℂ := fun m => ∑ n ∈ Finset.Icc 2 m, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I)) with hP
  have hP1 : P 1 = 0 := by
    simp only [hP]
    apply Finset.sum_eq_zero
    intro n hn
    exfalso
    simp only [Finset.mem_Icc] at hn
    omega
  have hX : ∀ m, 1 ≤ m →
      (∑ k ∈ Finset.Icc 1 m, b k * (k : ℂ) ^ (-((t : ℂ) * Complex.I))) = b 1 + P m := by
    intro m hm
    rw [sumIccOneSplit m hm]
    simp only [hP]
    rw [show (((1 : ℕ) : ℂ)) = 1 from Nat.cast_one, Complex.one_cpow, mul_one]
  have habel := Work.ZeroDensity.Montgomery.normCpowAddIt_le_abel N hN1 b
      (σ₀ := 0) (σ := σ) (t := t) hσ
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one, sub_zero] at habel
  have hXsum : (∑ n ∈ Finset.Icc 1 (N - 1),
        ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ))
          * ‖∑ k ∈ Finset.Icc 1 n, b k * (k : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2)
      = ∑ n ∈ Finset.Icc 1 (N - 1),
          ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * ‖b 1 + P n‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hX n (Finset.mem_Icc.mp hn).1]
  rw [hX N hN1, hXsum] at habel
  have hsq : ∀ Q : ℂ, ‖b 1 + Q‖ ^ 2 ≤ 2 * ‖b 1‖ ^ 2 + 2 * ‖Q‖ ^ 2 := by
    intro Q
    nlinarith [norm_add_le (b 1) Q, norm_nonneg (b 1), norm_nonneg Q,
      norm_nonneg (b 1 + Q), sq_nonneg (‖b 1‖ - ‖Q‖)]
  have hDnonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ (n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ) := by
    intro n hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hle : (n : ℝ) ≤ (((n + 1 : ℕ)) : ℝ) := by exact_mod_cast (Nat.le_succ n)
    have h := Real.rpow_le_rpow_of_nonpos hpos hle (by linarith : -σ ≤ 0)
    linarith
  have hlogpos : ∀ n : ℕ, 2 ≤ n → 0 < (n : ℝ) * Real.log (n : ℝ) := by
    intro n hn2
    have hlt : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    exact mul_pos (by positivity) (Real.log_pos hlt)
  have hWle : ∑ n ∈ Finset.Icc 2 (N - 1),
        ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * ‖P n‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc 2 (N - 1), ‖P n‖ ^ 2 / ((n : ℝ) * Real.log (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hd : (n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)
        ≤ 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
      rw [le_div_iff₀ (hlogpos n hn2)]
      exact dirPolyWeightBound σ hσ n hn2
    calc ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * ‖P n‖ ^ 2
        ≤ (1 / ((n : ℝ) * Real.log (n : ℝ))) * ‖P n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hd (sq_nonneg _)
      _ = ‖P n‖ ^ 2 / ((n : ℝ) * Real.log (n : ℝ)) := by ring
  have hsplitW : ∑ n ∈ Finset.Icc 1 (N - 1),
        ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * ‖P n‖ ^ 2
      = ∑ n ∈ Finset.Icc 2 (N - 1),
        ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * ‖P n‖ ^ 2 := by
    have hIns : Finset.Icc 1 (N - 1) = insert 1 (Finset.Icc 2 (N - 1)) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIns, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    simp [hP1]
  have hD1 : ∑ n ∈ Finset.Icc 1 (N - 1),
        ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * ‖b 1 + P n‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 (N - 1),
        ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * (2 * ‖b 1‖ ^ 2 + 2 * ‖P n‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_left (hsq (P n)) (hDnonneg n (Finset.mem_Icc.mp hn).1)
  have hD2 : ∑ n ∈ Finset.Icc 1 (N - 1),
        ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * (2 * ‖b 1‖ ^ 2 + 2 * ‖P n‖ ^ 2)
      ≤ 2 * ‖b 1‖ ^ 2
        + 2 * ∑ n ∈ Finset.Icc 2 (N - 1), ‖P n‖ ^ 2 / ((n : ℝ) * Real.log (n : ℝ)) := by
    have heq : ∑ n ∈ Finset.Icc 1 (N - 1),
          ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * (2 * ‖b 1‖ ^ 2 + 2 * ‖P n‖ ^ 2)
        = (∑ n ∈ Finset.Icc 1 (N - 1),
            2 * ‖b 1‖ ^ 2 * ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)))
          + (∑ n ∈ Finset.Icc 1 (N - 1),
            2 * (((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * ‖P n‖ ^ 2)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn; ring
    rw [heq]
    have hs1 : (∑ n ∈ Finset.Icc 1 (N - 1),
          2 * ‖b 1‖ ^ 2 * ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)))
        ≤ 2 * ‖b 1‖ ^ 2 := by
      rw [← Finset.mul_sum]
      exact mul_le_of_le_one_right (by positivity) (sumIccWeightBound N hN1 σ hσ)
    have hs2 : (∑ n ∈ Finset.Icc 1 (N - 1),
          2 * (((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * ‖P n‖ ^ 2))
        ≤ 2 * ∑ n ∈ Finset.Icc 2 (N - 1),
            ‖P n‖ ^ 2 / ((n : ℝ) * Real.log (n : ℝ)) := by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
      rw [hsplitW]
      exact hWle
    linarith
  have hD : 2 * (∑ n ∈ Finset.Icc 1 (N - 1),
        ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * ‖b 1 + P n‖ ^ 2)
      ≤ 4 * ‖b 1‖ ^ 2 + 4 * (∑ n ∈ Finset.Icc 2 (N - 1),
          ‖P n‖ ^ 2 / ((n : ℝ) * Real.log (n : ℝ))) := by
    have h := hD1.trans hD2
    linarith
  have hPN : 2 * ‖b 1 + P N‖ ^ 2 ≤ 4 * ‖b 1‖ ^ 2 + 4 * ‖P N‖ ^ 2 := by
    have := hsq (P N); linarith
  have hWnn : 0 ≤ ∑ n ∈ Finset.Icc 2 (N - 1),
      ‖P n‖ ^ 2 / ((n : ℝ) * Real.log (n : ℝ)) := by
    apply Finset.sum_nonneg
    intro n hn
    exact div_nonneg (sq_nonneg _) (le_of_lt (hlogpos n (Finset.mem_Icc.mp hn).1))
  calc ‖∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2
      ≤ 2 * ‖b 1 + P N‖ ^ 2 + 2 * ∑ n ∈ Finset.Icc 1 (N - 1),
          ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) * ‖b 1 + P n‖ ^ 2 := habel
    _ ≤ (4 * ‖b 1‖ ^ 2 + 4 * ‖P N‖ ^ 2)
        + (4 * ‖b 1‖ ^ 2 + 4 * ∑ n ∈ Finset.Icc 2 (N - 1),
            ‖P n‖ ^ 2 / ((n : ℝ) * Real.log (n : ℝ))) := add_le_add hPN hD
    _ ≤ 8 * (‖b 1‖ ^ 2 + ‖P N‖ ^ 2 + ∑ n ∈ Finset.Icc 2 (N - 1),
            ‖P n‖ ^ 2 / ((n : ℝ) * Real.log (n : ℝ))) := by
      nlinarith [sq_nonneg ‖b 1‖, sq_nonneg ‖P N‖, hWnn]

end Work.ZeroDensity.Ingham
