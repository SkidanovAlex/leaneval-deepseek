import ChallengeDeps
import Submission.Work.Core.Basic
import Submission.Work.Radial.gaussian_schwartz
import Submission.Work.Radial.fourier_gaussian
import Submission.Work.Sampling.rapidlyDecreasing_coeffs

/-!
# The complex Gaussian as a Schwartz function

For `Im τ > 0` the function `x ↦ exp (π i τ ‖x‖²)` is a Schwartz function on `R^n`
(`Work.Radial.gaussian_schwartz`).  This file names a choice of such a Schwartz map,
`Work.Core.gaussianSchwartz`, and records its basic calculus: its values, its
radiality, its Fourier transform (`(i/τ)^{n/2}` times the Gaussian with parameter
`-1/τ`, from `Work.Radial.fourier_gaussian`), and the derivative of its profile along
the coordinate axis.  These are the computations needed to check the interpolation
formula on Gaussians.
-/

open LeanEval.Analysis.CKMRVInterpolation
open scoped FourierTransform SchwartzMap

namespace Work.Core

/-- The Gaussian `x ↦ exp (π i τ ‖x‖ ^ 2)` as a complex Schwartz function on `R^n`,
for `0 < τ.im`. -/
noncomputable def gaussianSchwartz (n : ℕ) (τ : ℂ) (hτ : 0 < τ.im) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  Classical.choose (Work.Radial.gaussian_schwartz n τ hτ)

theorem gaussianSchwartz_apply (n : ℕ) (τ : ℂ) (hτ : 0 < τ.im)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussianSchwartz n τ hτ x = gaussianFun n τ x :=
  Classical.choose_spec (Work.Radial.gaussian_schwartz n τ hτ) x

/-- The Fourier transform of the complex Gaussian: it is `(i/τ)^{n/2}` times the
Gaussian with parameter `-1/τ`. -/
theorem fourier_gaussianSchwartz (n : ℕ) (τ : ℂ) (hτ : 0 < τ.im)
    (w : EuclideanSpace ℝ (Fin n)) :
    (FourierTransform.fourierCLM ℂ 𝓢(EuclideanSpace ℝ (Fin n), ℂ) (gaussianSchwartz n τ hτ)) w
      = (Complex.I / τ) ^ ((n : ℂ) / 2) * gaussianFun n (-1 / τ) w :=
  Work.Radial.fourier_gaussian n τ hτ _ (fun x => gaussianSchwartz_apply n τ hτ x) w

/-- The complex Gaussian is radial. -/
theorem radial_gaussianFun (n : ℕ) (τ : ℂ) : Radial (gaussianFun n τ) :=
  fun x y hxy => by simp only [gaussianFun, hxy]

/-- The Gaussian is radial as a Schwartz function. -/
theorem radial_gaussianSchwartz (n : ℕ) (τ : ℂ) (hτ : 0 < τ.im) :
    Radial (gaussianSchwartz n τ hτ) :=
  fun x y hxy => by
    rw [gaussianSchwartz_apply, gaussianSchwartz_apply]
    exact radial_gaussianFun n τ x y hxy

/-- The profile of the Gaussian along the coordinate axis. -/
theorem gaussianFun_realIncl (n : ℕ) [NeZero n] (τ : ℂ) (t : ℝ) :
    gaussianFun n τ (realIncl (n := n) t)
      = Complex.exp (↑Real.pi * Complex.I * τ * (t : ℂ) ^ 2) := by
  simp only [gaussianFun, Work.Sampling.realIncl_norm, sq_abs]
  rw [Complex.ofReal_pow]

end Work.Core
