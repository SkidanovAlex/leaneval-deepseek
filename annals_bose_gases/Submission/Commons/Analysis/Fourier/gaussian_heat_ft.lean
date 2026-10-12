import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open scoped Real FourierTransform RealInnerProductSpace
open Complex hiding exp

/-- Inverse Fourier transform of the Gaussian `q ↦ exp (−π·s·‖q‖²)` on `ℝ³`
(with the convention `𝓕⁻g(z) = ∫ g(q) e^{+2π i ⟨q,z⟩} dq`):

`∫_q exp(−π·s·‖q‖²)·exp(2π i ⟨q,z⟩) dq = s^{−3/2}·exp(−π‖z‖²/s)`.

This is the identity `1/‖z‖ = ∫₀^∞ H_s(z) ds` in its Fourier form; here
`H_s(z) := s^{−3/2} exp(−π‖z‖²/s)` is the heat kernel. -/
theorem gaussian_heat_ft {s : ℝ} (hs : 0 < s)
    (z : EuclideanSpace ℝ (Fin 3)) :
    (∫ q : EuclideanSpace ℝ (Fin 3),
        Complex.exp (-(↑(Real.pi * s) * (‖q‖ : ℂ) ^ 2)) *
          Complex.exp ((↑(2 * Real.pi * ⟪q, z⟫) : ℂ) * Complex.I))
      = (↑(s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-(↑(Real.pi / s) * (‖z‖ : ℂ) ^ 2)) := by
  let b : ℂ := (↑(Real.pi * s) : ℂ)
  have hbz : 0 < b.re := by
    dsimp [b]
    simp [Real.pi_pos, hs]
  have hgz := fourier_gaussian_innerProductSpace (V := EuclideanSpace ℝ (Fin 3)) hbz (-z)
  have hfirst : (𝓕 (fun v : EuclideanSpace ℝ (Fin 3) => cexp (-b * (‖v‖ : ℂ) ^ 2)) (-z)) =
      (∫ q : EuclideanSpace ℝ (Fin 3),
        Complex.exp (-(↑(Real.pi * s) * (‖q‖ : ℂ) ^ 2)) *
          Complex.exp ((↑(2 * Real.pi * ⟪q, z⟫) : ℂ) * Complex.I)) := by
    rw [Real.fourier_eq']
    simp
    congr 1
    funext q
    rw [← Complex.exp_add]
    rw [← Complex.exp_add]
    congr 1
    dsimp [b]
    rw [Complex.ofReal_mul]
    ring
  rw [← hfirst]
  rw [hgz]
  have hfin : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) / 2 : ℂ) = (3 / 2 : ℂ) := by
    norm_num
  rw [hfin]
  have hpi : (↑Real.pi / (↑(Real.pi * s) : ℂ) : ℂ) = (↑(1 / s) : ℂ) := by
    rw [← Complex.ofReal_div]
    congr 1
    field_simp [Real.pi_ne_zero, ne_of_gt hs]
  have hcoef : (↑Real.pi / b : ℂ) ^ (3 / 2 : ℂ) = (↑(s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
    dsimp [b]
    rw [hpi]
    have hconv : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by norm_num
    rw [hconv]
    rw [← Complex.ofReal_cpow (by positivity : 0 ≤ 1 / s)]
    congr 1
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul (le_of_lt hs)]
    norm_num
  rw [hcoef]
  congr 1
  congr 1
  dsimp [b]
  rw [norm_neg]
  field_simp [Complex.ofReal_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero (ne_of_gt hs))]
  rw [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
    Complex.ofReal_ne_zero.mpr (ne_of_gt hs)]

end Commons.Analysis.Fourier