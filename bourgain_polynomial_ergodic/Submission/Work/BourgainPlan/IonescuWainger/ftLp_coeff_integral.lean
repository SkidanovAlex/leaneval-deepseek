import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_coeff

/-!
# The Fourier coefficient formula as a circle integral

`ftLp_coeff` computes the `m`-th Fourier coefficient of `ftLp h hh` against the Hilbert basis
`fourierBasis` as an `L²` inner product.  Here we rewrite that inner product as the concrete
circle integral `∫_𝕋 𝓕h(θ) · conj (e^{2πi m θ}) dθ`, using that the Hilbert basis element
`fourierBasis m` is (a.e.) the function `fourier m` (`coeFn_fourierLp`).
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

theorem ftLp_coeff_integral {h : ℤ → ℂ} (hh : Memℓp h 2) (m : ℤ) :
    h m = ∫ θ : Circle, (ftLp h hh : Circle → ℂ) θ * star (fourier m θ)
      ∂AddCircle.haarAddCircle := by
  rw [← ftLp_coeff hh m]
  -- The `L²` inner product is the integral of `inner ℂ (F θ) (G θ)`.
  rw [MeasureTheory.L2.inner_def]
  -- Replace the Hilbert basis element `fourierBasis m` by the function `fourier m` a.e.
  have hcoe : (fun θ : Circle =>
        (fourierBasis (T := 1) m : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) θ)
      =ᵐ[AddCircle.haarAddCircle] ⇑(fourier m) := by
    simpa using (coeFn_fourierLp (T := 1) 2 (n := m))
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with θ hθ
  rw [hθ]
  simp [RCLike.inner_apply]

end Work.BourgainPlan.IonescuWainger
