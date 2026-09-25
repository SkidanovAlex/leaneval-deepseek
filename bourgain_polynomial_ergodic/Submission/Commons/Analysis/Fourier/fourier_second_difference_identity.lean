import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform

namespace Commons.Analysis.Fourier

open MeasureTheory Filter
open scoped FourierTransform

private noncomputable def phi (t : ℝ) (x : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * t * x))

private lemma phi_norm (t x : ℝ) : ‖phi t x‖ = 1 := by
  rw [phi, show -(2 * Real.pi * Complex.I * t * x)
      = ((-(2 * Real.pi * t * x) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma phi_continuous (t : ℝ) : Continuous (phi t) := by
  unfold phi; fun_prop

private lemma phi_shift (t a y : ℝ) :
    phi t (y - a) = phi t y * Complex.exp (2 * Real.pi * Complex.I * t * a) := by
  simp only [phi, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Fourier transform of `m` is the integral against the phase `phi t`. -/
private lemma fourier_eq_phi (m : ℝ → ℂ) (t : ℝ) :
    FourierTransform.fourier m t = ∫ x : ℝ, phi t x * m x := by
  have harg : ∀ x : ℝ, (↑(-2 * Real.pi * x * t) : ℂ) * Complex.I
      = -(2 * Real.pi * Complex.I * t * x) := by
    intro x; push_cast; ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul, harg x, phi]

/-- Shifting the argument of an integrable function multiplies the integral against `phi t`
by the corresponding character. -/
private lemma integral_shift (m : ℝ → ℂ) (t a : ℝ) :
    ∫ x : ℝ, phi t x * m (x + a)
      = Complex.exp (2 * Real.pi * Complex.I * t * a) * FourierTransform.fourier m t := by
  have h1 : (∫ x, phi t x * m (x + a))
      = ∫ x, (fun y => phi t (y - a) * m y) (x + a) := by
    apply integral_congr_ae
    filter_upwards with x
    simp
  rw [h1, integral_add_right_eq_self (fun y => phi t (y - a) * m y) a]
  have h2 : (∫ y, phi t (y - a) * m y)
      = ∫ y, Complex.exp (2 * Real.pi * Complex.I * t * a) * (phi t y * m y) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [phi_shift]; ring
  rw [h2, integral_const_mul, ← fourier_eq_phi]

theorem fourier_second_difference_identity (m : ℝ → ℂ) (hm : MeasureTheory.Integrable m) (t h : ℝ) :
    ∫ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * t * x)) * (m x - 2 * m (x + h) + m (x + 2 * h))
      = (Complex.exp (2 * Real.pi * Complex.I * t * h) - 1) ^ 2 * FourierTransform.fourier m t := by
  change (∫ x : ℝ, phi t x * (m x - 2 * m (x + h) + m (x + 2 * h)))
      = (Complex.exp (2 * Real.pi * Complex.I * t * h) - 1) ^ 2 * FourierTransform.fourier m t
  have hmA : MeasureTheory.Integrable (fun x => phi t x * m x) :=
    hm.bdd_mul (phi_continuous t).aestronglyMeasurable
      (Eventually.of_forall (fun x => by rw [phi_norm]))
  have hmB : MeasureTheory.Integrable (fun x => phi t x * m (x + h)) :=
    (hm.comp_add_right h).bdd_mul (phi_continuous t).aestronglyMeasurable
      (Eventually.of_forall (fun x => by rw [phi_norm]))
  have hmC : MeasureTheory.Integrable (fun x => phi t x * m (x + 2 * h)) :=
    (hm.comp_add_right (2 * h)).bdd_mul (phi_continuous t).aestronglyMeasurable
      (Eventually.of_forall (fun x => by rw [phi_norm]))
  have e1 : (∫ x, phi t x * (m x - 2 * m (x + h) + m (x + 2 * h)))
      = ∫ x, (phi t x * m x - 2 * (phi t x * m (x + h)) + phi t x * m (x + 2 * h)) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hADD := integral_add
    (f := fun x => phi t x * m x - 2 * (phi t x * m (x + h)))
    (g := fun x => phi t x * m (x + 2 * h)) (hmA.sub (hmB.const_mul 2)) hmC
  have hSUB := integral_sub (f := fun x => phi t x * m x)
    (g := fun x => 2 * (phi t x * m (x + h))) hmA (hmB.const_mul 2)
  have hexp2 : Complex.exp (2 * Real.pi * Complex.I * t * ((2 * h : ℝ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * t * h)
          * Complex.exp (2 * Real.pi * Complex.I * t * h) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e1, hADD, hSUB, integral_const_mul, integral_shift m t h, integral_shift m t (2 * h),
    hexp2, ← fourier_eq_phi]
  ring

end Commons.Analysis.Fourier