import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Submission.Work.BoseBoxFock.SqrtKinDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKin.heat_ft_p`

The `p`-Fourier inversion of the Gaussian symbol: for `t > 0` and every `z : ℝ³`,

`∫_p e^{i⟪p,z⟫} e^{-t‖p‖²} dp = (2π)³ · heatK t z`,

where `heatK t z = (4πt)^{-3/2} e^{-‖z‖²/(4t)}` (see `Work.BoseBoxFock.SqrtKinDefs`).
Equivalently: `heatK t` is the inverse `p`-Fourier transform of `p ↦ e^{-t‖p‖²}`.

The proof has three ingredients, all of them elementary:

* Mathlib's complex Gaussian integral (`GaussianFourier.integral_cexp_neg_mul_sq_norm_add`,
  applied with `b = t`, `c = I`, `w = z`) gives
  `∫_p e^{-t‖p‖² + i⟪z,p⟫} = (π/t)^{3/2} e^{-‖z‖²/(4t)}`;
* the integrand rewrite `e^{i⟪p,z⟫} e^{-t‖p‖²} = e^{-t‖p‖² + i⟪z,p⟫}`
  (`Complex.ofReal_exp`, `Complex.exp_add`, `inner ℝ p z = inner ℝ z p`);
* the constant identity `(π/t)^{3/2} = (2π)³ (4πt)^{-3/2}` (`heatK_const_eq`).
-/

open MeasureTheory

namespace Work.BoseBoxFock.SqrtKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The constant identity behind the normalisation of `heatK`:
`(π/t)^{3/2} = (2π)³ (4πt)^{-3/2}` for `t > 0`.

Both sides equal `π^{3/2} t^{-3/2}`; the proof writes the right-hand side as
`((2π)²)^{3/2} · ((4πt)^{-1})^{3/2} = (4π²/(4πt))^{3/2}` and uses `(2π)² = 4π²`. -/
lemma heatK_const_eq {t : ℝ} (ht : 0 < t) :
    (Real.pi / t) ^ ((3 : ℝ) / 2) = (2 * Real.pi) ^ 3 * (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) := by
  have h1 : (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) = ((4 * Real.pi * t)⁻¹) ^ ((3 : ℝ) / 2) := by
    rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring, Real.rpow_neg (by positivity),
      Real.inv_rpow (by positivity)]
  rw [h1]
  have h2 : (2 * Real.pi) ^ 3 = ((2 * Real.pi) ^ 2) ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast (2 * Real.pi) 3, ← Real.rpow_two (2 * Real.pi),
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (2 : ℝ) ((3 : ℝ) / 2)]
    norm_num
  rw [h2, ← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- The complex Gaussian integral in the corpus's `p`-convention:
`∫_p e^{i⟪p,z⟫} e^{-t‖p‖²} = (π/t)^{3/2} e^{-‖z‖²/(4t)}` (the second factor being
`exp (I² ‖z‖²/(4t))`, which is how Mathlib's Gaussian integral writes it). -/
lemma integral_cexp_gaussian {t : ℝ} (ht : 0 < t) (z : ℝ³) :
    ∫ p : ℝ³,
        Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ)
      = (↑Real.pi / (t : ℂ)) ^ ((3 : ℂ) / 2)
          * Complex.exp ((Complex.I : ℂ) ^ 2 * ↑‖z‖ ^ 2 / (4 * (t : ℂ))) := by
  have hb : 0 < ((t : ℂ)).re := by simpa using ht
  have hfr : Module.finrank ℝ ℝ³ = 3 := by simp
  have hcongr : (∫ p : ℝ³,
        Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ))
      = ∫ p : ℝ³, Complex.exp (-(t : ℂ) * ↑‖p‖ ^ 2 + Complex.I * ↑(inner ℝ z p)) := by
    apply integral_congr_ae
    filter_upwards with p
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [real_inner_comm]
    push_cast
    ring
  rw [hcongr, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb Complex.I z,
    show (↑(Module.finrank ℝ ℝ³) : ℂ) / 2 = (3 : ℂ) / 2 by rw [hfr]; norm_num]

/-- The exponent of the second Gaussian factor, as a real exponential. -/
lemma cexp_gauss_arg (t : ℝ) (z : ℝ³) :
    Complex.exp ((Complex.I : ℂ) ^ 2 * ↑‖z‖ ^ 2 / (4 * (t : ℂ)))
      = ↑(Real.exp (-(‖z‖ ^ 2 / (4 * t)))) := by
  rw [Complex.I_sq, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem heat_ft_p {t : ℝ} (ht : 0 < t) (z : EuclideanSpace ℝ (Fin 3)) :
    ∫ p : EuclideanSpace ℝ (Fin 3),
        Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * (Real.exp (-(t * ‖p‖ ^ 2)) : ℂ)
      = (((2 * Real.pi) ^ 3 * heatK t z : ℝ) : ℂ) := by
  have hcpow : (↑Real.pi / (t : ℂ)) ^ ((3 : ℂ) / 2)
      = (((2 * Real.pi) ^ 3 * (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← heatK_const_eq ht, ← Complex.ofReal_div,
      show ((3 : ℂ) / 2) = ↑((3 : ℝ) / 2) by norm_num,
      ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ Real.pi / t)]
  rw [integral_cexp_gaussian ht z, hcpow, cexp_gauss_arg t z, ← Complex.ofReal_mul]
  congr 1
  unfold heatK
  ring

end Work.BoseBoxFock.SqrtKin
