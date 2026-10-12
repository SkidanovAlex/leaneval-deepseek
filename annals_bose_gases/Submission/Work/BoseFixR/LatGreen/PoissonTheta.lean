import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.LatGreen.ThetaSteps
import Submission.Work.BoseFixR.LatGreen.tsum_heatK1_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

/-- Poisson/Jacobi summation: the periodisation of the heat kernel is its Fourier series on the
unit torus `ℝ³/ℤ³`, `Σ_n p_t(u−n) = Σ_k exp(−4π²t‖k‖²) cos(2π k·u)`, valid for `t > 0`.  (Both
sides are absolutely convergent; the proof should use Mathlib's general Poisson summation
`Real.tsum_eq_tsum_fourier_of_rpow_decay` together with the Gaussian Fourier transform
`fourier_gaussian_innerProductSpace`.) -/
theorem PoissonTheta {t : ℝ} (ht : 0 < t) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.LatGreen.heatPeriod t u
      = ∑' k : Fin 3 → ℤ,
          Real.exp (-(4 * Real.pi ^ 2 * t) * ‖Work.BoseFixR.LatGreen.latVec k‖ ^ 2)
            * Real.cos (2 * Real.pi * ∑ i, (k i : ℝ) * u i) := by
  -- The one-dimensional Poisson/Jacobi identity (`Complex.tsum_exp_neg_quadratic`).
  have hC1 : ∀ x : ℝ, (∑' n : ℤ, (heatK1 t (x - n) : ℂ)) = ∑' m : ℤ, thetaTerm1 t x m :=
    fun x => tsum_heatK1_eq ht x
  -- The complex form of the identity: split the periodised heat kernel into the three
  -- one-dimensional periodisations, apply the one-dimensional identity to each, and recombine.
  have hcomplex : ((heatPeriod t u : ℝ) : ℂ) = ∑' k : Fin 3 → ℤ, thetaTerm t u k := by
    have e0 : (((∑' m : ℤ, heatK1 t (u 0 - m)) : ℝ) : ℂ)
        = ∑' m : ℤ, (heatK1 t (u 0 - m) : ℂ) := Complex.ofReal_tsum _
    have e1 : (((∑' m : ℤ, heatK1 t (u 1 - m)) : ℝ) : ℂ)
        = ∑' m : ℤ, (heatK1 t (u 1 - m) : ℂ) := Complex.ofReal_tsum _
    have e2 : (((∑' m : ℤ, heatK1 t (u 2 - m)) : ℝ) : ℂ)
        = ∑' m : ℤ, (heatK1 t (u 2 - m) : ℂ) := Complex.ofReal_tsum _
    rw [heatPeriod_eq_prod ht u, Complex.ofReal_mul, Complex.ofReal_mul, e0, e1, e2,
      hC1 (u 0), hC1 (u 1), hC1 (u 2)]
    exact thetaTerm1_tsum_mul_eq_thetaTerm_tsum ht u
  have hsum : Summable fun k : Fin 3 → ℤ => thetaTerm t u k := summable_thetaTerm ht u
  calc heatPeriod t u
      = ((heatPeriod t u : ℝ) : ℂ).re := (Complex.ofReal_re _).symm
    _ = (∑' k : Fin 3 → ℤ, thetaTerm t u k).re := by rw [hcomplex]
    _ = ∑' k : Fin 3 → ℤ, (thetaTerm t u k).re := Complex.re_tsum hsum
    _ = ∑' k : Fin 3 → ℤ, Real.exp (-(4 * Real.pi ^ 2 * t) * ‖latVec k‖ ^ 2)
          * Real.cos (2 * Real.pi * ∑ i, (k i : ℝ) * u i) :=
        tsum_congr (fun k => thetaTerm_re t u k)

end Work.BoseFixR.LatGreen
