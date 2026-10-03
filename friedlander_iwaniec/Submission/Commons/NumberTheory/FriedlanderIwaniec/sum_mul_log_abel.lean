import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The log ratio identity underlying Abel summation: for `1 ≤ n`,
`log((n+1)/n) = log(n+1) − log n`. -/
private lemma log_ratio_succ (n : ℕ) (hn : 1 ≤ n) :
    Real.log (((n : ℝ) + 1) / (n : ℝ)) = Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
  rw [Real.log_div (by positivity) (by exact_mod_cast (by omega : n ≠ 0))]
  simp only [Nat.cast_add, Nat.cast_one]

/-- One step of the inductive proof of discrete Abel summation: if the identity holds for `N ≥ 1`
then it holds for `N + 1`. -/
private lemma abel_step (a : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (ih : (∑ d ∈ Finset.Icc 1 N, a d * Real.log d)
      = (∑ d ∈ Finset.Icc 1 N, a d) * Real.log N
        - ∑ d ∈ Finset.Icc 1 (N - 1),
            (∑ e ∈ Finset.Icc 1 d, a e) * Real.log (((d : ℝ) + 1) / (d : ℝ))) :
    (∑ d ∈ Finset.Icc 1 (N + 1), a d * Real.log d)
      = (∑ d ∈ Finset.Icc 1 (N + 1), a d) * Real.log ((N + 1 : ℕ) : ℝ)
        - ∑ d ∈ Finset.Icc 1 (N + 1 - 1),
            (∑ e ∈ Finset.Icc 1 d, a e) * Real.log (((d : ℝ) + 1) / (d : ℝ)) := by
  have hL := Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega : 1 ≤ N + 1)
    (fun d => a d * Real.log d)
  have hS := Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega : 1 ≤ N + 1)
    (fun d => a d)
  have hW := Finset.sum_Icc_succ_top (a := 1) (b := N - 1) (by omega : 1 ≤ N - 1 + 1)
    (fun d => (∑ e ∈ Finset.Icc 1 d, a e) * Real.log (((d : ℝ) + 1) / (d : ℝ)))
  rw [Nat.sub_add_cancel hN] at hW
  have hlog := log_ratio_succ N hN
  rw [Nat.add_sub_cancel N 1]
  rw [hL, hS, hW, hlog, ih]
  push_cast
  ring

/-- Discrete Abel summation (summation by parts) with weight `log`: for any `a : ℕ → ℝ`,
`∑_{d ≤ N} a d · log d = (∑_{d ≤ N} a d) · log N − ∑_{d ≤ N−1} (∑_{e ≤ d} a e) · log((d+1)/d)`,
where all sums are over `Finset.Icc 1 _`. -/
theorem sum_mul_log_abel (a : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, a d * Real.log d)
      = (∑ d ∈ Finset.Icc 1 N, a d) * Real.log N
        - ∑ d ∈ Finset.Icc 1 (N - 1),
            (∑ e ∈ Finset.Icc 1 d, a e) * Real.log (((d : ℝ) + 1) / (d : ℝ)) := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp [Finset.Icc_eq_empty_of_lt]
    · exact abel_step a N hN ih

end Commons.NumberTheory.FriedlanderIwaniec