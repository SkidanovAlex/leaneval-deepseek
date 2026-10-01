import Mathlib
import Submission.Work.LinnikAreas.Density4.MuSqTotientDefs

namespace Work.LinnikAreas.Density4

open Finset BigOperators

/-- `cw u · 2^{ω(u)} · √u` factors over the prime divisors of a squarefree `u` as
`∏_{p ∣ u} (2/(p(p-1)) · √p)`. -/
theorem cw_two_pow_mul_sqrt (u : ℕ) (hu : Squarefree u) :
    cw u * (2 : ℝ) ^ u.primeFactors.card * Real.sqrt (u : ℝ)
      = ∏ p ∈ u.primeFactors, (2 / ((p : ℝ) * ((p : ℝ) - 1)) * Real.sqrt (p : ℝ)) := by
  -- On a squarefree `u`, `u = ∏_{p ∣ u} p`.
  have hsq : (u : ℝ) = ∏ p ∈ u.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hu]
  -- Hence `√u = ∏_{p ∣ u} √p`.
  have hsqrt : Real.sqrt (u : ℝ) = ∏ p ∈ u.primeFactors, Real.sqrt (p : ℝ) := by
    rw [hsq, Real.sqrt_prod]
    intro p _
    positivity
  -- And `2^{ω(u)} = ∏_{p ∣ u} 2`.
  have h2pow : (2 : ℝ) ^ u.primeFactors.card = ∏ _p ∈ u.primeFactors, (2 : ℝ) :=
    (Finset.prod_const (2 : ℝ)).symm
  rw [cw, h2pow, hsqrt, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  simp only [cc]
  ring

end Work.LinnikAreas.Density4
