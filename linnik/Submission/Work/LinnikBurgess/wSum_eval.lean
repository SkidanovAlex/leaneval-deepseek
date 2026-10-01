import Mathlib
import Submission.Work.LinnikBurgess.cubic_phase_defs

namespace Work.LinnikBurgess

open scoped BigOperators

/-- Evaluating the innermost `w`-sum: the Taylor expansion of `H` at `a + p*u` shows that
shifting `u ↦ u + p^(K-2)*w` contributes a linear additive character
`E p (w * H'(a))`, whose complete sum over `w < p` is the orthogonality relation. -/
theorem wSum_eval (p K : ℕ) [Fact p.Prime] (hK : 2 ≤ K) (H : Polynomial ℤ) (a u : ℕ) :
    (∑ w ∈ Finset.range p,
        Commons.NumberTheory.GaussSum.E (p ^ K)
          (Polynomial.eval ((a : ℤ) + (p : ℤ) * ((u : ℤ) + (p : ℤ) ^ (K - 2) * (w : ℤ))) H))
      = Commons.NumberTheory.GaussSum.E (p ^ K)
            (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) H)
          * (if (p : ℤ) ∣ Polynomial.eval (a : ℤ) (Polynomial.derivative H) then (p:ℂ) else 0) := by
  -- `H'(a + p*u) ≡ H'(a) mod p`, since `(a + p*u) - a = p*u`
  have hdvd : (p : ℤ) ∣ Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) (Polynomial.derivative H)
      - Polynomial.eval (a : ℤ) (Polynomial.derivative H) := by
    have h1 : (p : ℤ) ∣ ((a : ℤ) + (p : ℤ) * (u : ℤ)) - (a : ℤ) := by
      rw [show ((a : ℤ) + (p : ℤ) * (u : ℤ)) - (a : ℤ) = (p : ℤ) * (u : ℤ) by ring]
      exact dvd_mul_right _ _
    exact dvd_trans h1 (Polynomial.sub_dvd_eval_sub _ _ _)
  -- Taylor expansion of the exponential summand
  rw [show (∑ w ∈ Finset.range p,
        Commons.NumberTheory.GaussSum.E (p ^ K)
          (Polynomial.eval ((a : ℤ) + (p : ℤ) * ((u : ℤ) + (p : ℤ) ^ (K - 2) * (w : ℤ))) H))
      = ∑ w ∈ Finset.range p,
        Commons.NumberTheory.GaussSum.E (p ^ K) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) H)
          * Commons.NumberTheory.GaussSum.E p
              (w * Polynomial.eval (a : ℤ) (Polynomial.derivative H))
      from Finset.sum_congr rfl
        (fun w _ => Commons.NumberTheory.GaussSum.E_taylor p K hK H a u w hdvd)]
  rw [← Finset.mul_sum, Commons.NumberTheory.GaussSum.orth_sum]

end Work.LinnikBurgess
