import Mathlib
import Submission.Work.TMComp.RedC7T.cf_num_den_integral
import Submission.Work.TMComp.RedC7T.cf_num_den_coprime
import Submission.Work.TMComp.RedC7T.cf_convs_lt_inv_dens_sq

namespace Work.TMComp.RedC7T

open GenContFract

/-- Given an irrational real `α`, there is a sequence of rational approximations whose
numerators `a n` and denominators `q n` are coprime, with monotone, unbounded denominators,
and which approximate `α` at least as well as the continued fraction convergents:
`|α - a n / q n| ≤ 1/(q n * q (n+1))` and `< 1/(q n)^2`. -/
theorem conv_chain (α : ℝ) (hα : Irrational α) :
    ∃ (a : ℕ → ℤ) (q : ℕ → ℕ),
      (∀ n, 1 ≤ q n) ∧ (∀ n, q n ≤ q (n + 1)) ∧ Filter.Tendsto q Filter.atTop Filter.atTop ∧
      (∀ n, Nat.Coprime (Int.natAbs (a n)) (q n)) ∧
      (∀ n, |α - (a n : ℝ) / (q n : ℝ)| ≤ 1 / ((q n : ℝ) * (q (n + 1) : ℝ))) ∧
      (∀ n, |α - (a n : ℝ) / (q n : ℝ)| < 1 / ((q n : ℝ) ^ 2)) := by
  have hterm : ¬ (GenContFract.of α).Terminates := by
    rw [GenContFract.terminates_iff_rat]
    rintro ⟨q, hq⟩
    exact hα ⟨q, hq.symm⟩
  have hv : ∀ n, ¬ (GenContFract.of α).TerminatedAt n := fun n hn => hterm ⟨n, hn⟩
  obtain ⟨a, q, hA, hB, hq1⟩ := cf_num_den_integral α hv
  refine ⟨a, q, hq1, ?_, ?_, ?_, ?_, ?_⟩
  · -- denominators are monotone
    intro n
    have h := GenContFract.of_den_mono (v := α) (n := n)
    rw [hB n, hB (n + 1)] at h
    exact_mod_cast h
  · -- denominators tend to infinity
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro n hn
    have hfib : (Nat.fib (n + 1) : ℝ) ≤ (GenContFract.of α).dens n :=
      GenContFract.succ_nth_fib_le_of_nth_den (v := α) (n := n) (Or.inr (hv (n - 1)))
    rw [hB n] at hfib
    have hcast : Nat.fib (n + 1) ≤ q n := by exact_mod_cast hfib
    have hb : b ≤ Nat.fib (n + 1) := by
      have := Nat.le_fib_add_one (n + 1); omega
    omega
  · -- numerators and denominators are coprime
    exact cf_num_den_coprime α hv a q hA hB
  · -- the weak approximation bound
    intro n
    have h := GenContFract.abs_sub_convs_le (v := α) (n := n) (hv n)
    rw [GenContFract.conv_eq_num_div_den, hA n, hB n, hB (n + 1)] at h
    exact h
  · -- the strict approximation bound
    intro n
    have h := cf_convs_lt_inv_dens_sq α hv n
    rw [GenContFract.conv_eq_num_div_den, hA n, hB n] at h
    exact h

end Work.TMComp.RedC7T
