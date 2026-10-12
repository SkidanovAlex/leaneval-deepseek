import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseKinLoc.Momentum.cubFT_1d
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The complex 1D cube factor is the real one

`chFT t = ∫_{-1/2}^{1/2} e^{i t s} ds` is the complex one-dimensional factor of the unit-cube
Fourier symbol, and `hFT t = ∫_{-1/2}^{1/2} cos (t s) ds` its real part.  Since
`e^{iθ} = cos θ + i sin θ` and `s ↦ sin (t s)` is odd while the interval `[-1/2, 1/2]` is
symmetric about `0`, the imaginary part of the complex integral vanishes:

    `chFT t = (hFT t : ℂ)`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Momentum

/-- `chFT t = (hFT t : ℂ)`: the sine part of the complex exponential integrates to zero by the
symmetry of `[-1/2, 1/2]`. -/
theorem chFT_eq_ofReal (t : ℝ) : chFT t = (hFT t : ℂ) := by
  have hI : volume (Set.Icc (-(1/2)) (1/2) : Set ℝ) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  -- The sine integral vanishes by the oddness of `s ↦ sin (t s)`.
  have hsin : (∫ s in Set.Icc (-(1/2)) (1/2), Real.sin (t * s)) = 0 := by
    have hA : (∫ x in (-(1/2))..(1/2), Real.sin (t * x)) = 0 := by
      have h1 : (∫ x in (-(1/2))..(1/2), Real.sin (t * (-x)))
          = (∫ x in (-(1/2))..(1/2), Real.sin (t * x)) := by
        simpa only [neg_neg] using
          (intervalIntegral.integral_comp_neg (f := fun x : ℝ => Real.sin (t * x))
            (a := -(1/2)) (b := 1/2))
      have h2 : (∫ x in (-(1/2))..(1/2), Real.sin (t * (-x)))
          = -(∫ x in (-(1/2))..(1/2), Real.sin (t * x)) := by
        rw [intervalIntegral.integral_congr (g := fun x : ℝ => -(Real.sin (t * x)))
              (fun x _ => by rw [mul_neg, Real.sin_neg])]
        exact intervalIntegral.integral_neg
      have h3 : (∫ x in (-(1/2))..(1/2), Real.sin (t * x))
          = -(∫ x in (-(1/2))..(1/2), Real.sin (t * x)) := h1.symm.trans h2
      linarith
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2)]
    exact hA
  -- Integrability of the two pieces over the finite-measure interval.
  have hIc : IntegrableOn (fun s : ℝ => ((Real.cos (t*s)) : ℂ))
      (Set.Icc (-(1/2)) (1/2)) volume := by
    refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) ?_ (by fun_prop) ?_
    · exact integrableOn_const (C := (1 : ℝ)) hI (by norm_num)
    · filter_upwards with x
      rw [Complex.norm_real]
      simpa using Real.abs_cos_le_one (t * x)
  have hIs : IntegrableOn (fun s : ℝ => ((Real.sin (t*s)) : ℂ) * Complex.I)
      (Set.Icc (-(1/2)) (1/2)) volume := by
    refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) ?_ (by fun_prop) ?_
    · exact integrableOn_const (C := (1 : ℝ)) hI (by norm_num)
    · filter_upwards with x
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
      simpa using Real.abs_sin_le_one (t * x)
  -- `e^{i t s} = cos (t s) + i sin (t s)` pointwise.
  have hpoint : ∀ s : ℝ, Complex.exp (Complex.I * ((t*s : ℝ) : ℂ))
      = ((Real.cos (t*s) : ℝ) : ℂ) + ((Real.sin (t*s) : ℝ) : ℂ) * Complex.I := by
    intro s
    rw [mul_comm Complex.I ((t*s : ℝ) : ℂ), Complex.exp_mul_I, Complex.ofReal_cos,
        Complex.ofReal_sin]
  have hcosC : (∫ s in Set.Icc (-(1/2)) (1/2), ((Real.cos (t*s) : ℝ) : ℂ))
      = Complex.ofReal (∫ s in Set.Icc (-(1/2)) (1/2), Real.cos (t*s)) := integral_ofReal
  have hsinC : (∫ s in Set.Icc (-(1/2)) (1/2), ((Real.sin (t*s) : ℝ) : ℂ)) = 0 := by
    rw [show (∫ s in Set.Icc (-(1/2)) (1/2), ((Real.sin (t*s) : ℝ) : ℂ))
        = Complex.ofReal (∫ s in Set.Icc (-(1/2)) (1/2), Real.sin (t*s)) from integral_ofReal,
      hsin]
    simp
  rw [chFT, hFT]
  trans (∫ s in Set.Icc (-(1/2)) (1/2),
      (((Real.cos (t*s) : ℝ) : ℂ) + ((Real.sin (t*s) : ℝ) : ℂ) * Complex.I))
  · exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [integral_add hIc hIs, integral_mul_const, hcosC, hsinC]
  simp

end Work.BoseKinLoc.Momentum
