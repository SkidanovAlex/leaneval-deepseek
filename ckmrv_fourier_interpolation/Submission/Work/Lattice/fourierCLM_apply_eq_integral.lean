import Mathlib
import Submission.Work.Lattice.poissonBasics

/-!
# The Fourier transform at an integer vector as an integral against circle characters

For a Schwartz function `f` on `ℝⁿ` and an integer vector `w ∈ ℤⁿ`, the Fourier transform
`𝓕 f w = ∫ z, exp (-2π i ⟪z, w⟫) f z` can be written as an integral over `ℝⁿ` against the
product of the circle Fourier monomials `fourier (-(w i))`:

`𝓕 f w = ∫ y, (∏ i, fourier (-(w i)) yᵢ) * f y`.

The point is that `exp (-2π i ⟪z, w⟫) = ∏ i exp (-2π i wᵢ zᵢ)` because `w` has integer
coordinates, and `exp (-2π i wᵢ zᵢ) = fourier (-(w i)) zᵢ` is exactly the `(-wᵢ)`-th Fourier
monomial on the circle `ℝ/ℤ`.
-/

namespace Work.Lattice

open MeasureTheory
open scoped FourierTransform SchwartzMap

/-- The product of the circle Fourier monomials `fourier (-(w i))` at a point
`y : Fin n → ℝ`, expanded as a single complex exponential. -/
lemma prod_fourier_eq_exp {n : ℕ} (w : Fin n → ℤ) (y : Fin n → ℝ) :
    (∏ i, fourier (-(w i)) ((y i : ℝ) : UnitAddCircle))
      = Complex.exp (↑(-2 * Real.pi * (∑ i, y i * (w i : ℝ))) * Complex.I) := by
  have hfac : ∀ i, fourier (-(w i)) ((y i : ℝ) : UnitAddCircle)
      = Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-(w i)) * ↑(y i) / ↑(1 : ℝ)) :=
    fun _ => fourier_coe_apply
  simp only [hfac, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [show (∑ x, 2 * ↑Real.pi * Complex.I * -↑(w x) * ↑(y x) / 1)
      = ∑ x, (-(2 * ↑Real.pi * Complex.I)) * (↑(y x) * ↑(w x)) from
        Finset.sum_congr rfl (fun i _ => by ring)]
  rw [← Finset.mul_sum]
  ring

theorem fourierCLM_apply_eq_integral {n : ℕ} (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (w : Fin n → ℤ) :
    FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) f
        (WithLp.toLp 2 (Work.Lattice.intVecToReal w))
      = ∫ y : Fin n → ℝ, (∏ i, fourier (-(w i)) ((y i : ℝ) : UnitAddCircle))
          * f (WithLp.toLp 2 y) := by
  -- unfold the Fourier transform to the integral `∫ z, exp (-2π i ⟪z, w⟫) • f z`
  rw [FourierTransform.fourierCLM_apply, SchwartzMap.fourier_coe]
  rw [Real.fourier_eq' f (WithLp.toLp 2 (Work.Lattice.intVecToReal w))]
  -- change variables `z = WithLp.toLp 2 y`: the map `WithLp.toLp 2` is measure preserving
  have hchange : (∫ z : EuclideanSpace ℝ (Fin n),
        Complex.exp (↑(-2 * Real.pi *
          inner ℝ z (WithLp.toLp 2 (Work.Lattice.intVecToReal w))) * Complex.I) • f z)
      = ∫ y : Fin n → ℝ,
        Complex.exp (↑(-2 * Real.pi * inner ℝ (WithLp.toLp 2 y)
          (WithLp.toLp 2 (Work.Lattice.intVecToReal w))) * Complex.I) • f (WithLp.toLp 2 y) := by
    rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp'
      (f := MeasurableEquiv.toLp 2 (Fin n → ℝ))
      (g := fun z : EuclideanSpace ℝ (Fin n) =>
        Complex.exp (↑(-2 * Real.pi * inner ℝ z
          (WithLp.toLp 2 (Work.Lattice.intVecToReal w))) * Complex.I) • f z)]
    simp only [MeasurableEquiv.coe_toLp]
  rw [hchange]
  -- compare the integrands pointwise
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only []
  rw [smul_eq_mul, PiLp.inner_apply]
  simp only [Work.Lattice.intVecToReal_apply, Real.inner_apply]
  rw [prod_fourier_eq_exp]

end Work.Lattice
