import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Complex
set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- Critical-line magnitude of the complex Gamma function (reflection formula):
`‖Γ(1/2+it)‖² = π/cosh(πt)` for all real `t`. -/
theorem gamma_abs_sq_half (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  let z : ℂ := (1 / 2 : ℂ) + I * (t : ℂ)
  change ‖Complex.Gamma z‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t)
  -- `z` lies on the critical line `Re z = 1/2`, so `1 - z = conj z`.
  have hz1 : 1 - z = starRingEnd ℂ z := by
    subst z
    apply Complex.ext <;> simp <;> ring
  -- The sine in the reflection formula: `sin (π * z) = cosh (π * t)` (a real
  -- number embedded in ℂ).
  have hsin : Complex.sin ((Real.pi : ℂ) * z) = (Real.cosh (Real.pi * t) : ℂ) := by
    subst z
    calc
      Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℂ) + I * (t : ℂ)))
          = Complex.sin (I * ((Real.pi : ℂ) * (t : ℂ)) + (Real.pi : ℂ) / 2) := by
              congr 1
              ring
      _ = Complex.cos (I * ((Real.pi : ℂ) * (t : ℂ))) := by
              rw [Complex.sin_add_pi_div_two]
      _ = Complex.cos (I * ((Real.pi * t : ℝ) : ℂ)) := by
              rw [← Complex.ofReal_mul]
      _ = Complex.cos (((Real.pi * t : ℝ) : ℂ) * I) := by
              congr 1
              ring
      _ = Complex.cosh (((Real.pi * t : ℝ) : ℂ)) := by
              rw [Complex.cos_mul_I]
      _ = (Real.cosh (Real.pi * t) : ℂ) := by
              rw [Complex.ofReal_cosh]
  -- Euler's reflection formula `Γ(z)·Γ(1-z) = π / sin (πz)` rewritten through
  -- conjugation of the Gamma function:
  -- `normSq (Γ z) = Γ z * conj (Γ z) = π / sin (π z) = π / cosh (π t)`.
  have h_main : ((Complex.normSq (Complex.Gamma z) : ℝ) : ℂ) =
      ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    calc
      ((Complex.normSq (Complex.Gamma z) : ℝ) : ℂ)
          = Complex.Gamma z * starRingEnd ℂ (Complex.Gamma z) := by
              rw [← Complex.mul_conj]
      _ = Complex.Gamma z * Complex.Gamma (starRingEnd ℂ z) := by
              rw [← Complex.Gamma_conj]
      _ = Complex.Gamma z * Complex.Gamma (1 - z) := by
              rw [← hz1]
      _ = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) := by
              rw [Complex.Gamma_mul_Gamma_one_sub]
      _ = ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
              rw [hsin, ← Complex.ofReal_div]
  -- `normSq w = ‖w‖²`, so compare the coerced real equalities.
  have hns := Complex.normSq_eq_norm_sq (Complex.Gamma z)
  exact Complex.ofReal_inj.mp (by
    rw [hns.symm]
    exact h_main)

end Commons.Analysis.SpecialFunctions.Gamma