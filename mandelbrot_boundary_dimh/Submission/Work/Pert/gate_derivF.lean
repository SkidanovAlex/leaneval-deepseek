import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.deriv_sfun

namespace Work.Pert

open Complex

/-- **Shishikura (A.1.7)(ii)**, `HasDerivAt` form of `Work.Pert.deriv`: the lift
`F_f(w) = w + log(1 - s(w))/(2πiα)` is differentiable at `w` with
`F_f'(w) = 1 + τ(τ-σ)(u'(τ) - u(τ)²)/((1 + τu(τ) - σu(τ))(1 + τu(τ)))`, where `τ = τ_f(w)`.
The extra hypotheses `hz`, `h1`, `hk`, `hE` keep the auxiliary expressions nonzero and `hslit` is
the branch condition making `Complex.log` differentiable at `1 - sfun u σ α w`. -/
theorem gate_derivF {u : ℂ → ℂ} {σ α w : ℂ} (hα : α ≠ 0) (hσ : σ ≠ 0)
    (hz : tauC σ α w ≠ 0)
    (hu : DifferentiableAt ℂ u (tauC σ α w))
    (hslit : 1 - sfun u σ α w ∈ Complex.slitPlane)
    (hE : Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1)
    (h1 : (1 : ℂ) + tauC σ α w * u (tauC σ α w) ≠ 0)
    (hk : 1 + tauC σ α w * u (tauC σ α w) - σ * u (tauC σ α w) ≠ 0) :
    HasDerivAt (liftF u σ α)
      (1 + tauC σ α w * (tauC σ α w - σ) * (_root_.deriv u (tauC σ α w) - u (tauC σ α w) ^ 2)
          / ((1 + tauC σ α w * u (tauC σ α w) - σ * u (tauC σ α w))
             * (1 + tauC σ α w * u (tauC σ α w)))) w := by
  -- `Work.Pert.deriv_sfun` (A.1.7)(ii) for the inner quantity `s(w) = sfun u σ α w`.
  have hsf := deriv_sfun hα hσ hu hz hE h1
  -- the chain rule for `log (1 - s)`: `deriv log (1 - s) = -s'/(1-s)`.
  have hlog := (hsf.const_sub 1).clog hslit
  -- `liftF u σ α w = w + (2πiα)⁻¹ log (1 - s(w))`.
  have hlift := (hasDerivAt_id w).add (hlog.const_mul (1 / (2 * Real.pi * I * α)))
  have hfin : HasDerivAt (liftF u σ α) _ w := hlift
  -- `hfin.congr_deriv` reduces to the algebraic identity between the two derivative values.
  refine hfin.congr_deriv ?_
  have h1u : (1 : ℂ) + u (tauC σ α w) * tauC σ α w ≠ 0 := by
    rw [mul_comm]; exact h1
  have hku : 1 + u (tauC σ α w) * tauC σ α w - σ * u (tauC σ α w) ≠ 0 := by
    rw [mul_comm]; exact hk
  have hsdecomp : (1 : ℂ) - sfun u σ α w
      = (1 + tauC σ α w * u (tauC σ α w) - σ * u (tauC σ α w))
        / (1 + tauC σ α w * u (tauC σ α w)) := by
    rw [sfun]
    field_simp [h1u]
  have h2pa : (2 * Real.pi * I * α) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero h2 (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) hα
  rw [hsdecomp]
  field_simp [hα, hσ, h1, hk, h2pa, h1u, hku]

end Work.Pert
