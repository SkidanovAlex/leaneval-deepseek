import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Submission.Commons.Analysis.ExponentialSums.poly_phase_residue_split

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators

/-- Pointwise factorisation of the quadratic phase along a residue class: writing
`α = a/q + β` and `n = p q + r`, the phase `e(α n²)` splits as the product of the
`q`-periodic factor `e(a r²/q)` and the `β`-oscillating factor `e(β n²)`.  The reason is
that the two phases differ by an integer multiple of `2πi`:
`α n² - (a r²/q + β n²) = (a/q)(n² - r²) = a p (n + r)`. -/
lemma quadratic_phase_factor_term (q : ℕ) (hq : 0 < q) (a : ℤ) (β : ℝ) (p r : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((((a : ℝ) / (q : ℝ) + β) * ((p * q + r : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * ((r : ℝ) ^ 2 : ℂ) / (q : ℂ)))
        * Complex.exp (2 * Real.pi * Complex.I * ((β * ((p * q + r : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) := by
  have hn : ((p * q + r : ℕ) : ℝ) = (p : ℝ) * (q : ℝ) + (r : ℝ) := by push_cast; ring
  -- The real phase difference is the integer `a * p * (n + r)`.
  have hreal : (((a : ℝ) / (q : ℝ) + β) * ((p : ℝ) * (q : ℝ) + (r : ℝ)) ^ 2
        - ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) + β * ((p : ℝ) * (q : ℝ) + (r : ℝ)) ^ 2))
      = (a : ℝ) * (p : ℝ) * (((p : ℝ) * (q : ℝ) + (r : ℝ)) + (r : ℝ)) := by
    have hfac : ((p : ℝ) * (q : ℝ) + (r : ℝ)) ^ 2 - (r : ℝ) ^ 2
        = (p : ℝ) * (q : ℝ) * (((p : ℝ) * (q : ℝ) + (r : ℝ)) + (r : ℝ)) := by ring
    have hgrp : ((a : ℝ) / (q : ℝ) + β) * ((p : ℝ) * (q : ℝ) + (r : ℝ)) ^ 2
        - ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) + β * ((p : ℝ) * (q : ℝ) + (r : ℝ)) ^ 2)
        = ((a : ℝ) / (q : ℝ)) * (((p : ℝ) * (q : ℝ) + (r : ℝ)) ^ 2 - (r : ℝ) ^ 2) := by ring
    rw [hgrp, hfac]
    have hqR : (q : ℝ) ≠ 0 := by positivity
    field_simp
  set k : ℤ := a * ((p : ℤ) * (((p * q + r : ℕ) : ℤ) + (r : ℤ))) with hk
  have hY1 : ((a : ℂ) * ((r : ℝ) ^ 2 : ℂ) / (q : ℂ))
      = (((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) : ℝ) : ℂ) := by
    push_cast; ring
  -- Coerce the real phase difference to `ℂ`.
  have hsub : ((((a : ℝ) / (q : ℝ) + β) * ((p * q + r : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)
      - ((a : ℂ) * ((r : ℝ) ^ 2 : ℂ) / (q : ℂ)
          + ((β * ((p * q + r : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) = (k : ℂ) := by
    rw [hY1, ← Complex.ofReal_add, ← Complex.ofReal_sub]
    congr 1
    simp only [hk]
    push_cast
    rw [hreal]
    ring
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  linear_combination (2 * Real.pi * Complex.I) * hsub

/-- The quadratic Weyl sum factorises modulo `q`: writing `α = a/q + β`, the sum
`∑_{n<N} e(α n²)` equals the sum over residues `r < q` of the complete quadratic phase
`e(a r²/q)` times the `β`-oscillating sum over `p` with `p q + r < N`.  This is the
algebraic reduction at the heart of the major-arc analysis of the squares. -/
theorem quadratic_phase_residue_factor (N q : ℕ) (hq : 0 < q) (a : ℤ) (β : ℝ) :
    (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I *
          ((((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ 2 : ℝ) : ℂ)))
      = ∑ r ∈ Finset.range q,
          Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * ((r : ℝ) ^ 2 : ℂ) / (q : ℂ)))
          * ∑ p ∈ Finset.range ((N + q - 1 - r) / q),
              Complex.exp (2 * Real.pi * Complex.I *
                ((β * ((((p * q + r : ℕ) : ℝ)) ^ 2) : ℝ) : ℂ)) := by
  rw [sum_range_residue_split
    (fun n : ℕ => Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ 2 : ℝ) : ℂ))) N q hq]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => quadratic_phase_factor_term q hq a β p r)

end Commons.Analysis.ExponentialSums