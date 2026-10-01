import Mathlib
import Submission.Work.ZeroDensity.Jutila.bvDefs

namespace Work.ZeroDensity.Jutila

/-- Double counting / swap of summation: for any finite set `s` of integer cutoffs and any
weights `f`, the sum of `f j * P j n` over `j ∈ s` equals the sum over the divisors `d ∣ n` of
`μ d` times the sum of `f j` over those `j ∈ s` with `d ≤ j`; here
`P t n = Σ_{d ∣ n, d ≤ t} μ(d)` (`bvDefs.lean`). -/
lemma SumStepsMulP (s : Finset ℕ) (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ s, f j * P (j : ℝ) n
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) *
          ∑ j ∈ s.filter (fun j => d ≤ j), f j := by
  -- Expand `P (j : ℝ) n` and view both sides as sums over the pairs `(j, d) ∈ s × n.divisors`
  -- of `f j * μ d` restricted to those pairs with `d ≤ j`.
  have hstep : ∀ j : ℕ, f j * P (j : ℝ) n
      = ∑ d ∈ n.divisors, (if d ≤ j then f j * (ArithmeticFunction.moebius d : ℝ) else 0) := by
    intro j
    calc f j * P (j : ℝ) n
        = f j * ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (j : ℝ)),
            (ArithmeticFunction.moebius d : ℝ) := by rw [P]
      _ = ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (j : ℝ)),
            f j * (ArithmeticFunction.moebius d : ℝ) := by rw [Finset.mul_sum]
      _ = ∑ d ∈ n.divisors,
            (if (d : ℝ) ≤ (j : ℝ) then f j * (ArithmeticFunction.moebius d : ℝ) else 0) := by
            rw [Finset.sum_filter]
      _ = ∑ d ∈ n.divisors, (if d ≤ j then f j * (ArithmeticFunction.moebius d : ℝ) else 0) := by
            refine Finset.sum_congr rfl (fun d _ => ?_)
            by_cases h : d ≤ j
            · have h' : (d : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
              rw [if_pos h', if_pos h]
            · have h' : ¬ ((d : ℝ) ≤ (j : ℝ)) := by exact_mod_cast h
              rw [if_neg h', if_neg h]
  have hstep2 : ∀ d : ℕ, (ArithmeticFunction.moebius d : ℝ) * ∑ j ∈ s.filter (fun j => d ≤ j), f j
      = ∑ j ∈ s, (if d ≤ j then f j * (ArithmeticFunction.moebius d : ℝ) else 0) := by
    intro d
    calc (ArithmeticFunction.moebius d : ℝ) * ∑ j ∈ s.filter (fun j => d ≤ j), f j
        = ∑ j ∈ s.filter (fun j => d ≤ j), (ArithmeticFunction.moebius d : ℝ) * f j := by
            rw [Finset.mul_sum]
      _ = ∑ j ∈ s.filter (fun j => d ≤ j), f j * (ArithmeticFunction.moebius d : ℝ) := by
            exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ = ∑ j ∈ s, (if d ≤ j then f j * (ArithmeticFunction.moebius d : ℝ) else 0) := by
            rw [Finset.sum_filter]
  calc ∑ j ∈ s, f j * P (j : ℝ) n
      = ∑ j ∈ s, ∑ d ∈ n.divisors,
          (if d ≤ j then f j * (ArithmeticFunction.moebius d : ℝ) else 0) :=
        Finset.sum_congr rfl (fun j _ => hstep j)
    _ = ∑ d ∈ n.divisors, ∑ j ∈ s,
          (if d ≤ j then f j * (ArithmeticFunction.moebius d : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) *
          ∑ j ∈ s.filter (fun j => d ≤ j), f j :=
        Finset.sum_congr rfl (fun d _ => (hstep2 d).symm)

end Work.ZeroDensity.Jutila
