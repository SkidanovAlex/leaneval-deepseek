import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.modelBall
import Submission.Work.Drive.N2.modelFlowDefs

/-!
# The complex coordinate of a chart: injectivity and the level relation

The window blocks of the compact `n = 2` movie use, at a Morse chart `φ` with normal form
`f = f p + s₁ (φ·0)² + s₂ (φ·1)²`, the complex coordinate

    Z := fun y => (φ y 0 : ℂ) + (φ y 1 : ℂ) * I

because in the *saddle* case (`s₁ = -s₂`) the normal form is (up to the sign of the first term)
`c ± Re (Z ·)²`.  This file records the small bridges from the chart data to the hypotheses of the
window assembly: `Z` is injective on the chart source, and the level relation holds with either sign
convention.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- The complex coordinate of a chart. -/
noncomputable def chartZ (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) : M → ℂ :=
  fun m => ((φ m 0 : ℝ) : ℂ) + ((φ m 1 : ℝ) : ℂ) * Complex.I

lemma chartZ_apply (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (m : M) :
    chartZ φ m = ((φ m 0 : ℝ) : ℂ) + ((φ m 1 : ℝ) : ℂ) * Complex.I := rfl

lemma chartZ_re (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (m : M) :
    (chartZ φ m).re = φ m 0 := by
  simp [chartZ]

lemma chartZ_im (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (m : M) :
    (chartZ φ m).im = φ m 1 := by
  simp [chartZ]

/-- **`Z` is injective on the chart source** (because the chart is). -/
lemma chartZ_injOn (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) :
    Set.InjOn (chartZ φ) φ.source := by
  intro x hx y hy hxy
  have h1 : (chartZ φ x).re = (chartZ φ y).re := by rw [hxy]
  have h2 : (chartZ φ x).im = (chartZ φ y).im := by rw [hxy]
  rw [chartZ_re, chartZ_re] at h1
  rw [chartZ_im, chartZ_im] at h2
  refine φ.injOn hx hy ?_
  ext j
  fin_cases j
  · exact h1
  · exact h2

/-- `(z ^ 2).re = z.re ^ 2 - z.im ^ 2`. -/
lemma complex_sq_re (z : ℂ) : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
  rw [pow_two, Complex.mul_re]; ring

/-- `(z ^ 2).im = 2 * z.re * z.im`. -/
lemma complex_sq_im (z : ℂ) : (z ^ 2).im = 2 * z.re * z.im := by
  rw [pow_two, Complex.mul_im]; ring

/-- The real part of `(i z) ^ 2` is the negative of that of `z ^ 2`. -/
lemma complex_I_sq : (Complex.I : ℂ) ^ 2 = -1 := by
  rw [pow_two, Complex.I_mul_I]

lemma complex_mul_I_sq_re (z : ℂ) : ((Complex.I * z) ^ 2).re = -((z ^ 2).re) := by
  have h : (Complex.I * z) ^ 2 = -(z ^ 2) := by
    rw [mul_pow, complex_I_sq]; ring
  rw [h, Complex.neg_re]

lemma chartZ_sq_re (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (y : M) :
    ((chartZ φ y) ^ 2).re = (φ y 0) ^ 2 - (φ y 1) ^ 2 := by
  rw [complex_sq_re, chartZ_re, chartZ_im]

lemma chartZ_sq_im (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (y : M) :
    ((chartZ φ y) ^ 2).im = 2 * φ y 0 * φ y 1 := by
  rw [complex_sq_im, chartZ_re, chartZ_im]

/-- The saddle normal form with signs `(1, -1)` is `Re (Z ·)²`. -/
lemma chartQ_one_neg_one (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (y : M) :
    chartQ φ 1 (-1) y = ((chartZ φ y) ^ 2).re := by
  rw [chartZ_sq_re]
  simp [chartQ]
  ring

/-- The saddle normal form with signs `(-1, 1)` is `Re ((i Z ·)²)`. -/
lemma chartQ_neg_one_one (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (y : M) :
    chartQ φ (-1) 1 y = (((Complex.I * chartZ φ y) ^ 2)).re := by
  rw [complex_mul_I_sq_re, chartZ_sq_re]
  simp [chartQ]
  ring

end Work.Drive.N2
