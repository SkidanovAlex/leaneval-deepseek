import Mathlib

namespace Work.Mostow

/-- If the derivative of `f` at `x` maps everything into the orthogonal complement of the
nonzero vector `f x`, then the derivative is singular. -/
theorem detFDerivEqZero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → E) {x : E} (hx : f x ≠ 0)
    (h : ∀ v : E, inner ℝ (fderiv ℝ f x v) (f x) = 0) :
    (fderiv ℝ f x).det = 0 := by
  set L : E →ₗ[ℝ] E := (fderiv ℝ f x).toLinearMap
  have hne : ¬ Function.Injective L := by
    intro hinj
    have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hinj
    obtain ⟨w, hw⟩ := hsurj (f x)
    have hw' : fderiv ℝ f x w = f x := hw
    have h1 : inner ℝ (f x) (f x) = 0 := by
      have h2 := h w
      rw [hw'] at h2
      exact h2
    exact hx (inner_self_eq_zero.mp h1)
  have hnd : L.normDet = 0 := (L.normDet_eq_zero_tfae.out 1 6).mpr hne
  have hdet : L.det = 0 := by
    have h2 := LinearMap.normDet_eq_abs_det L
    rw [hnd] at h2
    exact abs_eq_zero.mp h2.symm
  simpa [L] using hdet

end Work.Mostow
