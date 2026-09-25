import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Submission.Commons.Analysis.Polynomial.dvd_eval_sub_eval_mul

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators

/-- The exponential phase `n ↦ e(a P(n)/q)` of an integer polynomial is periodic modulo
`q`: `e(a P (p q + r)/q) = e(a P(r)/q)`.  This turns a polynomial Weyl sum into a sum of
complete exponential sums `S(a/q)` twisted by the `β = α - a/q` oscillation. -/
theorem exp_eval_div_eq_exp_eval_mod (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q) (a : ℤ) (p r : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((a : ℂ) * ((P.eval (p * (q : ℤ) + r) : ℤ) : ℂ) / (q : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I *
        ((a : ℂ) * ((P.eval r : ℤ) : ℂ) / (q : ℂ))) := by
  -- The arithmetic input: `q ∣ P (p q + r) − P r`.
  obtain ⟨m, hm⟩ := Commons.Analysis.Polynomial.dvd_eval_sub_eval_mul P (q : ℤ) p r
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  -- Cast the divisibility to `ℂ`: `↑E − ↑F = ↑q * ↑m`.
  have hcast : ((P.eval (p * (q : ℤ) + r) : ℤ) : ℂ) - ((P.eval r : ℤ) : ℂ)
      = (q : ℂ) * ((m : ℤ) : ℂ) := by
    have h : ((P.eval (p * (q : ℤ) + r) - P.eval r : ℤ) : ℂ)
        = (((q : ℤ) * m : ℤ) : ℂ) := by rw [hm]
    push_cast at h
    exact h
  have hm' : ((P.eval (p * (q : ℤ) + r) : ℤ) : ℂ)
      = ((P.eval r : ℤ) : ℂ) + (q : ℂ) * ((m : ℤ) : ℂ) := by
    have h := sub_eq_iff_eq_add.mp hcast
    linear_combination h
  have hmul : (a : ℂ) * ((P.eval (p * (q : ℤ) + r) : ℤ) : ℂ)
      = (a : ℂ) * ((P.eval r : ℤ) : ℂ) + (q : ℂ) * ((a * m : ℤ) : ℂ) := by
    rw [hm']
    have h2 : ((a * m : ℤ) : ℂ) = (a : ℂ) * ((m : ℤ) : ℂ) := by push_cast; ring
    rw [h2]; ring
  -- The two phases differ by the integer `a * m`.
  have hinner : (a : ℂ) * ((P.eval (p * (q : ℤ) + r) : ℤ) : ℂ) / (q : ℂ)
      = (a : ℂ) * ((P.eval r : ℤ) : ℂ) / (q : ℂ) + ((a * m : ℤ) : ℂ) := by
    rw [hmul, add_div, mul_div_cancel_left₀ _ hqC]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨a * m, ?_⟩
  have h2 := congrArg (fun w : ℂ => 2 * Real.pi * Complex.I * w) hinner
  rw [mul_add] at h2
  rw [h2]
  ring

end Commons.Analysis.ExponentialSums