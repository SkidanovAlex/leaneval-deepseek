import Mathlib.NumberTheory.Chebyshev

namespace Commons.NumberTheory.Chebyshev

open Finset in
open scoped BigOperators in
/-- `θ(b)`, for a natural number `b`, viewed as a sum over `range (b+1)`. -/
private lemma theta_nat_eq_sum_range (b : ℕ) :
    Chebyshev.theta (b : ℝ)
      = ∑ p ∈ Finset.range (b + 1), (if p.Prime then Real.log (p : ℝ) else 0) := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter]
  apply Finset.sum_congr
  · ext y; simp only [Finset.mem_Icc, Finset.mem_range]; omega
  · intro y _; rfl

open Finset in
open scoped BigOperators in
/-- `θ(n) − θ(l)` is the sum of `log p` over the primes `l < p ≤ n`. -/
theorem theta_sub_theta_eq (l n : ℕ) (hln : l ≤ n) :
    Chebyshev.theta (n : ℝ) - Chebyshev.theta (l : ℝ)
      = ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ l < p), Real.log (p : ℝ) := by
  rw [theta_nat_eq_sum_range n, theta_nat_eq_sum_range l,
    ← Finset.sum_Ico_eq_sub (f := fun p => if p.Prime then Real.log (p : ℝ) else 0)
      (m := l + 1) (n := n + 1) (by omega)]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext y
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨by omega, by omega⟩, hp, by omega⟩
  · rintro ⟨⟨h1, h2⟩, hp, h3⟩
    exact ⟨⟨by omega, by omega⟩, hp⟩

end Commons.NumberTheory.Chebyshev
