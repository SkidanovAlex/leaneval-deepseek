import Mathlib
import Submission.Work.LinnikAreas.Density4.BzBilinDefs
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex
import Submission.Work.LinnikAreas.Density4.sum_inv_mul_sqrt_le

namespace Work.ZeroDensity.Jutila

open Finset

/-- Divisor-swap identity for `σ_{-1/2}`: the partial sums of `σ_{-1/2}` can be
written as a single sum over `d ≤ N`, where the multiplicity of `d` is the number
`N / d` of multiples of `d` in `[1, N]`.

Concretely `Σ_{m ≤ N} Σ_{d | m} d^{-1/2} = Σ_{d ≤ N} (N / d) · d^{-1/2}`. -/
lemma sum_sigmaHalf_eq (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, Work.LinnikAreas.Density4.sigmaHalf m)
      = ∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ) * (1 / Real.sqrt (d : ℝ)) := by
  have h := Work.LinnikAreas.Density4.sum_Icc_div_reindex N (fun _ => True)
      (fun d _ => (1 : ℝ) / Real.sqrt (d : ℝ))
  have hR : (∑ n ∈ Finset.Icc 1 N,
        ∑ d ∈ n.divisors.filter (fun _ => True), (1 : ℝ) / Real.sqrt (d : ℝ))
      = ∑ n ∈ Finset.Icc 1 N, Work.LinnikAreas.Density4.sigmaHalf n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.filter_true]
    rfl
  have hL : (∑ d ∈ (Finset.Icc 1 N).filter (fun _ => True),
        ∑ m ∈ Finset.Icc 1 (N / d), (1 : ℝ) / Real.sqrt (d : ℝ))
      = ∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ) * (1 / Real.sqrt (d : ℝ)) := by
    rw [Finset.filter_true]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    simp [Nat.card_Icc]
  calc ∑ m ∈ Finset.Icc 1 N, Work.LinnikAreas.Density4.sigmaHalf m
      = ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors.filter (fun _ => True), (1 : ℝ) / Real.sqrt (d : ℝ) := hR.symm
    _ = ∑ d ∈ (Finset.Icc 1 N).filter (fun _ => True),
          ∑ m ∈ Finset.Icc 1 (N / d), (1 : ℝ) / Real.sqrt (d : ℝ) := h.symm
    _ = ∑ d ∈ Finset.Icc 1 N, ((N / d : ℕ) : ℝ) * (1 / Real.sqrt (d : ℝ)) := hL

/-- The average order of `σ_{-1/2}(n) = Σ_{d | n} d^{-1/2}` is bounded: there is
an absolute constant `C` with `Σ_{m ≤ n} σ_{-1/2}(m) ≤ C n` for all `n`.

Taking `C = 6` works: by the divisor-swap identity the partial sum equals
`Σ_{d ≤ n} (n/d) d^{-1/2}`, and the number `n/d` of multiples of `d` in `[1,n]`
is at most `n/d`, giving `≤ n Σ_{d ≤ n} d^{-3/2} ≤ 6n` since
`Σ_{d ≥ 1} d^{-3/2} ≤ 4`. -/
theorem SigmaHalfAvg :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∑ m ∈ Finset.Icc 1 n, Work.LinnikAreas.Density4.sigmaHalf m) ≤ C * (n : ℝ) := by
  refine ⟨6, by norm_num, fun n => ?_⟩
  rw [sum_sigmaHalf_eq n]
  calc ∑ d ∈ Finset.Icc 1 n, ((n / d : ℕ) : ℝ) * (1 / Real.sqrt (d : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 n, (n : ℝ) * (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hcast : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := Nat.cast_div_le
        have hnn : (0 : ℝ) ≤ 1 / Real.sqrt (d : ℝ) := by positivity
        calc ((n / d : ℕ) : ℝ) * (1 / Real.sqrt (d : ℝ))
            ≤ ((n : ℝ) / (d : ℝ)) * (1 / Real.sqrt (d : ℝ)) :=
              mul_le_mul_of_nonneg_right hcast hnn
          _ = (n : ℝ) * (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
              have hs : Real.sqrt (d : ℝ) ≠ 0 := by positivity
              have hd0 : (d : ℝ) ≠ 0 := by positivity
              field_simp
    _ = (n : ℝ) * ∑ d ∈ Finset.Icc 1 n, 1 / ((d : ℝ) * Real.sqrt (d : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (n : ℝ) * 6 :=
        mul_le_mul_of_nonneg_left
          (Work.LinnikAreas.Density4.sum_inv_mul_sqrt_le n) (Nat.cast_nonneg n)
    _ = 6 * (n : ℝ) := by ring

end Work.ZeroDensity.Jutila
