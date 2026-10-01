import Mathlib

namespace Work.Sieve

/-- Solving the "top edge" relation `P - Q + I*(R - S) = Res * (2πI)` for `R`
as a real part of the residue: an algebraic rearrangement over `ℂ`. -/
theorem perronShift_topEdge_solve {P Q R S Res : ℂ}
    (h : P - Q + Complex.I * (R - S) = Res * (2 * (Real.pi : ℂ) * Complex.I)) :
    (1 / (2 * (Real.pi : ℂ))) * R
      = Res + (1 / (2 * (Real.pi : ℂ))) * S
        + (1 / (2 * (Real.pi : ℂ) * Complex.I)) * (Q - P) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [hpi, hI]
  field_simp at h
  field_simp
  linear_combination h

end Work.Sieve
