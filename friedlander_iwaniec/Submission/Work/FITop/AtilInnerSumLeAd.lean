import Mathlib
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25

namespace Work.FITop

/-!
# `AtilInnerSumLeAd`

The squarefree-supported sequence `ã = μ²·FIa` satisfies `ã_n ≤ a_n` (as `|μ| ≤ 1`), hence the
inner congruence sum of the chain over `n ∈ [1,x]`, `d ∣ n` is bounded by the *full* congruence
sum `Ad d x = ∑_{0 ≤ n ≤ x, d ∣ n} a_n` of the main paper, which contains it as a sub-sum.
-/

/-- The basic pointwise bound `ã_n ≤ a_n`: `ã_n = μ(n)²·a_n` and `μ(n)² ∈ {0,1}` while `a_n ≥ 0`. -/
private lemma atilFIa_le_an (n : ℕ) :
    atilFIa n ≤ (Submission.an n : ℝ) := by
  have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := n)
    have h' : ((|ArithmeticFunction.moebius n| : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by
      exact_mod_cast h
    rwa [Int.cast_abs, Int.cast_one] at h'
  have h2 : (ArithmeticFunction.moebius n : ℝ) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr hmu
  rw [atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
  exact mul_le_of_le_one_left (by positivity) h2

theorem AtilInnerSumLeAd (d x : ℕ) :
    (∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), Work.FITop.atilFIa n)
      ≤ (Submission.Ad d x : ℝ) := by
  calc ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), Work.FITop.atilFIa n
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n => d ∣ n), (Submission.an n : ℝ) :=
        Finset.sum_le_sum (fun n _ => atilFIa_le_an n)
    _ ≤ ∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n), (Submission.an n : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hn ⊢
          omega
        · intro n _ _
          positivity
    _ = (Submission.Ad d x : ℝ) := by
        rw [Submission.Ad, Nat.cast_sum]

end Work.FITop
