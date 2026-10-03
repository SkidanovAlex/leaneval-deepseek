import Mathlib

namespace Work.Fatou.Analysis

/-- For a real-linear endomorphism `L` of `ℂ`, the (real) determinant equals
`|α|² - |β|²` where `α = (L 1 - i L i)/2` and `β = (L 1 + i L i)/2` are the
complex-linear and conjugate-linear parts of `L` written in the basis `(1, i)`. -/
theorem fderiv_det_eq (L : ℂ →L[ℝ] ℂ) :
    L.det = ‖(L 1 - Complex.I * L Complex.I) / 2‖ ^ 2 - ‖(L 1 + Complex.I * L Complex.I) / 2‖ ^ 2 := by
  -- Matrix of `L` in the real basis `(1, i)` of `ℂ`.
  have hmat : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (L : ℂ →ₗ[ℝ] ℂ)
      = !![(L 1).re, (L Complex.I).re; (L 1).im, (L Complex.I).im] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply]
  -- The determinant is thus `re(L 1) * im(L i) - re(L i) * im(L 1)`.
  have hdet : L.det = (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im := by
    change LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) = _
    rw [← LinearMap.det_toMatrix Complex.basisOneI (L : ℂ →ₗ[ℝ] ℂ), hmat, Matrix.det_fin_two]
    simp
  -- Rewrite the two norms as `normSq` and expand.
  rw [hdet, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  norm_num
  ring

end Work.Fatou.Analysis
