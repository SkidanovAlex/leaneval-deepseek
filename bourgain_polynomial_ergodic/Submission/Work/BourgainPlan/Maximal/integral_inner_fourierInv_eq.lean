import Mathlib

namespace Work.BourgainPlan.Maximal

/-- Parseval-type pairing identity for the Fourier transform on `ℝ`: pairing the inverse
Fourier transform of `f` against `h` is the same as pairing `f` against the Fourier transform
of `h`. This is the self-adjointness/duality form of the Fourier transform and follows from
Fubini for the Fourier integral. -/
theorem integral_inner_fourierInv_eq (f h : ℝ → ℂ) (hf : MeasureTheory.Integrable f)
    (hh : MeasureTheory.Integrable h) :
    (∫ x : ℝ, inner ℂ (FourierTransform.fourierInv f x) (h x))
      = ∫ x : ℝ, inner ℂ (f x) (FourierTransform.fourier h x) := by
  -- Continuity of the bilinear form `L = -innerₗ ℝ` used to define the inverse transform.
  have hcont : Continuous fun p : ℝ × ℝ => ((-innerₗ ℝ) p.1) p.2 := by
    rw [show (fun p : ℝ × ℝ => ((-innerₗ ℝ) p.1) p.2) = fun p => - inner ℝ p.1 p.2 by
      ext p; simp]
    exact continuous_neg.comp continuous_inner
  -- `-(-innerₗ ℝ).flip = innerₗ ℝ` by symmetry of the inner product.
  have hflip : -((-innerₗ ℝ).flip) = innerₗ ℝ := by ext; simp
  -- The general Plancherel/duality identity for the Fourier integral.
  have key := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (M := innerSL ℂ) (e := Real.fourierChar) (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
    (L := -innerₗ ℝ) (f := f) (g := h) Real.continuous_fourierChar hcont hf hh
  rw [hflip] at key
  -- Unfold the `fourier`/`fourierInv` notation to the underlying Fourier integrals.
  change (∫ x : ℝ, ((innerSL ℂ)
        (VectorFourier.fourierIntegral Real.fourierChar MeasureTheory.volume (-innerₗ ℝ) f x)) (h x))
      = ∫ x : ℝ, ((innerSL ℂ) (f x))
        (VectorFourier.fourierIntegral Real.fourierChar MeasureTheory.volume (innerₗ ℝ) h x)
  exact key

end Work.BourgainPlan.Maximal
