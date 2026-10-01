import Mathlib
import Submission.Work.LinnikBurgess.cubic_phase_defs

namespace Work.LinnikBurgess

open scoped BigOperators

/-- The range-sum `Tsum (p^K) H` splits according to the base-`p` digit decomposition
`j = a + p * (u + p^(K-2) * w)` with `a, w < p` and `u < p^(K-2)`. -/
theorem Tsum_split (p K : ℕ) [Fact p.Prime] (hK : 2 ≤ K) (H : Polynomial ℤ) :
    Commons.NumberTheory.GaussSum.Tsum (p ^ K) H
      = ∑ a ∈ Finset.range p, ∑ u ∈ Finset.range (p ^ (K - 2)), ∑ w ∈ Finset.range p,
          Commons.NumberTheory.GaussSum.E (p ^ K)
            (Polynomial.eval ((a : ℤ) + (p : ℤ) * ((u : ℤ) + (p : ℤ) ^ (K - 2) * (w : ℤ))) H) := by
  let F : ℕ → ℂ := fun j => Commons.NumberTheory.GaussSum.E (p ^ K) (Polynomial.eval (j : ℤ) H)
  have hL : Commons.NumberTheory.GaussSum.Tsum (p ^ K) H
      = ∑ j ∈ Finset.range (p ^ K), F j := rfl
  have hpK : p ^ K = p * p ^ (K - 1) := by
    conv_lhs => rw [show K = (K - 1) + 1 from by omega]
    rw [pow_succ, Nat.mul_comm]
  have hpK1 : p ^ (K - 1) = p ^ (K - 2) * p := by
    conv_lhs => rw [show K - 1 = (K - 2) + 1 from by omega]
    rw [pow_succ]
  rw [hL]
  conv_lhs => rw [hpK]
  rw [Commons.Algebra.BigOperators.sum_range_mul_eq F p (p ^ (K - 1))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hpK1,
    Commons.Algebra.BigOperators.sum_range_mul_eq (fun b => F (a + p * b)) (p ^ (K - 2)) p]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [F]
  congr 1

end Work.LinnikBurgess
