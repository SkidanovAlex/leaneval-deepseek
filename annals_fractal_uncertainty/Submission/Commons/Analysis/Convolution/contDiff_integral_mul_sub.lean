import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory
open scoped Convolution

namespace Commons.Analysis.Convolution

/-- **Smoothness of a mollification / convolution with a compactly supported smooth kernel.**

If `k : ℂᵈ → ℝ` is `C^∞` with compact support and `u : ℂᵈ → ℂ` is locally integrable, then the
convolution `z ↦ ∫ t, k (z - t) • u t` is `C^∞`.

Here `•` is the (real) scalar multiplication of `ℂ`, so the integrand is `k (z - t) * u t`.
The proof identifies the integral with the convolution
`u ⋆[ContinuousLinearMap.smulRightL ℝ ℝ ℂ 1, volume] k` and applies
`HasCompactSupport.contDiff_convolution_right`. -/
theorem contDiff_integral_mul_sub {d : ℕ} {u : (Fin d → ℂ) → ℂ} {k : (Fin d → ℂ) → ℝ}
    (hk : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) k) (hks : HasCompactSupport k)
    (hu : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun z => ∫ t, k (z - t) • u t
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) := by
  -- The bilinear pairing `L a b = b • a` realises the integrand `k (z - t) • u t`
  -- as `L (u t) (k (z - t))`, i.e. as a convolution of `u` with the kernel `k`.
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ →L[ℝ] ℝ)
  have h := hks.contDiff_convolution_right (L := L) (μ := volume) hu hk
  have hfun : (u ⋆[L, volume] k) = (fun z => ∫ t, k (z - t) • u t ∂(volume : MeasureTheory.Measure (Fin d → ℂ))) := by
    funext z
    rw [convolution_def]
    simp only [L, ContinuousLinearMap.smulRightL_apply_apply,
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
  rw [hfun] at h
  exact h

end Commons.Analysis.Convolution