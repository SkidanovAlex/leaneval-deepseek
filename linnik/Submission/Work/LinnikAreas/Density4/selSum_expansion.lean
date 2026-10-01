import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.LamRDefs

namespace Work.LinnikAreas.Density4

open Finset

noncomputable section

/-- The truncated Selberg weight `∑_{d ∣ n, d ≤ z} λ_d` is exactly `LambdaR z n`. -/
lemma selSum_eq_LambdaR (z n : ℕ) :
    (∑ d ∈ n.divisors.filter (fun d => d ≤ z), selLam z d)
      = Commons.NumberTheory.Sieve.LambdaR z n := rfl

/-- At `n = 1` the truncated Selberg weight is `log z`. -/
lemma selSum_one {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ (1 : ℕ).divisors.filter (fun d => d ≤ z), selLam z d) = Real.log (z : ℝ) := by
  rw [selSum_eq_LambdaR]
  exact LambdaR_one hz

/-- **Exact three-term expansion of the Selberg `Λ²`-sum in Graham's case `N < z²`.**  Splitting
off `n = 1` (where the Selberg weight is `Λ_z(1) = log z`) and using
`Λ_z(n) = Λ(n) + B_z(n)` for `n ≥ 2` (`Bz_eq_LambdaR_sub_vonMangoldt`), the square expands into
the von Mangoldt second moment, the mixed sum and the `B_z` second moment. -/
theorem selSum_expansion (z N : ℕ) (hz : 2 ≤ z) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors.filter (fun d => d ≤ z), selLam z d) ^ 2)
      = (Real.log (z : ℝ)) ^ 2
        + (∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
        + 2 * (∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n * Bz z n)
        + (∑ n ∈ Finset.Icc 2 N, (Bz z n) ^ 2) := by
  have hz1 : 1 ≤ z := by omega
  have hI : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1mem : (1 : ℕ) ∉ Finset.Icc 2 N := by simp
  have hsplit : (∑ n ∈ Finset.Icc 1 N,
        (∑ d ∈ n.divisors.filter (fun d => d ≤ z), selLam z d) ^ 2)
      = (Real.log (z : ℝ)) ^ 2
        + ∑ n ∈ Finset.Icc 2 N, (∑ d ∈ n.divisors.filter (fun d => d ≤ z), selLam z d) ^ 2 := by
    rw [hI, Finset.sum_insert h1mem, selSum_one hz1]
  have hpt : ∀ n ∈ Finset.Icc 2 N,
      (∑ d ∈ n.divisors.filter (fun d => d ≤ z), selLam z d) ^ 2
        = (ArithmeticFunction.vonMangoldt n + Bz z n) ^ 2 := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hsum : ArithmeticFunction.vonMangoldt n + Bz z n
        = Commons.NumberTheory.Sieve.LambdaR z n := by
      rw [Bz_eq_LambdaR_sub_vonMangoldt hn2 hz1]
      ring
    rw [selSum_eq_LambdaR, hsum]
  have hexp : (∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n + Bz z n) ^ 2)
      = (∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
        + 2 * (∑ n ∈ Finset.Icc 2 N, ArithmeticFunction.vonMangoldt n * Bz z n)
        + (∑ n ∈ Finset.Icc 2 N, (Bz z n) ^ 2) := by
    rw [Finset.sum_congr rfl (fun n (_ : n ∈ Finset.Icc 2 N) => by
      ring : ∀ n ∈ Finset.Icc 2 N,
        (ArithmeticFunction.vonMangoldt n + Bz z n) ^ 2
          = (ArithmeticFunction.vonMangoldt n) ^ 2
            + 2 * (ArithmeticFunction.vonMangoldt n * Bz z n)
            + (Bz z n) ^ 2)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsplit, Finset.sum_congr rfl hpt, hexp]
  ring

end

end Work.LinnikAreas.Density4
