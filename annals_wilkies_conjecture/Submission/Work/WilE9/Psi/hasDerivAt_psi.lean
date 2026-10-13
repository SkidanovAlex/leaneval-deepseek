import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Psi

/-- The value of `deriv psi` computed from the quotient rule, written over the common
denominator `√(1+x²)²`. -/
theorem psi_deriv_value (x : ℝ) :
    (1 * Real.sqrt (1 + x ^ 2) - x * (x / Real.sqrt (1 + x ^ 2))) / Real.sqrt (1 + x ^ 2) ^ 2
      = Work.WilE9.psig x ^ 3 := by
  have hs : (0 : ℝ) ≤ 1 + x ^ 2 := by positivity
  rw [Work.WilE9.psig, div_pow]
  field_simp
  rw [Real.sq_sqrt hs]
  ring

/-- The `√(1+x²)` factor is nonzero. -/
theorem sqrt_one_add_sq_ne_zero (x : ℝ) : Real.sqrt (1 + x ^ 2) ≠ 0 := by positivity

/-- `psi' = psig^3`; with `psi_sq_add_psig_sq` this makes the psi-factors algebraic. -/
theorem hasDerivAt_psi (x : ℝ) :
    HasDerivAt WilkiesDesign.E.psi (Work.WilE9.psig x ^ 3) x := by
  have hsq : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  have hsqrt_ne : Real.sqrt (1 + x ^ 2) ≠ 0 := sqrt_one_add_sq_ne_zero x
  -- derivative of the denominator `y ↦ √(1+y²)`
  have hg : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2)) (x / Real.sqrt (1 + x ^ 2)) x := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      have h := (hasDerivAt_id x).pow 2
      have h' : (fun y : ℝ => y ^ 2) = (id : ℝ → ℝ) ^ 2 := by ext y; simp
      rw [h']
      simpa using h
    have h0 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := h1.const_add 1
    have h2 := h0.sqrt hsq
    convert h2 using 1
    field_simp
  have h := (hasDerivAt_id x).div hg hsqrt_ne
  have hfun : WilkiesDesign.E.psi = (id : ℝ → ℝ) / fun y => Real.sqrt (1 + y ^ 2) := by
    ext y; simp [WilkiesDesign.E.psi]
  rw [hfun]
  convert h using 1
  simp only [id_eq]
  exact (psi_deriv_value x).symm

end Work.WilE9.Psi
