import Mathlib
import Submission.Work.Pert.Basic

namespace Work.Pert

-- `Basic.lean` states its identities with `open Complex` in scope, so that `I` means
-- `Complex.I`; the same opening is needed here for the statement below to elaborate
-- (the workspace builds with `autoImplicit = false`).
open Complex

/-- Shishikura (A.1.7)(iii): `τ_f (F_f w) = f (τ_f w)`, i.e. `F_f` is a lift of the germ `f` in the
covering coordinate `τ_f`. -/
theorem abel {u f : ℂ → ℂ} {σ α w : ℂ} (hα : α ≠ 0) (hσ : σ ≠ 0)
    (hz : tauC σ α w ≠ 0)
    (hu2 : 1 + tauC σ α w * u (tauC σ α w) ≠ 0)
    (hk : 1 + tauC σ α w * u (tauC σ α w) - σ * u (tauC σ α w) ≠ 0)
    (hE : Complex.exp (-(2 * Real.pi * I * α * w)) ≠ 1)
    (hs : 1 - sfun u σ α w ≠ 0)
    (hnf : ∀ z : ℂ, f z = z + z * (z - σ) * u z) :
    tauC σ α (liftF u σ α w) = f (tauC σ α w) := by
  have h2pi : (2 * Real.pi * Complex.I * α : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by simp [Real.pi_ne_zero]) Complex.I_ne_zero) hα
  -- The argument of the exponential shifts by `-log (1 - s)`, hence the value of `E` gets
  -- divided by `1 - s`.
  have hexp : Complex.exp (-(2 * Real.pi * Complex.I * α *
        (w + (1 / (2 * Real.pi * Complex.I * α)) * Complex.log (1 - sfun u σ α w))))
      = Complex.exp (-(2 * Real.pi * Complex.I * α * w)) / (1 - sfun u σ α w) := by
    have hA : 2 * Real.pi * Complex.I * α *
          (w + (1 / (2 * Real.pi * Complex.I * α)) * Complex.log (1 - sfun u σ α w))
        = 2 * Real.pi * Complex.I * α * w + Complex.log (1 - sfun u σ α w) := by
      rw [mul_add, ← mul_assoc, one_div, mul_inv_cancel₀ h2pi, one_mul]
    have harg : -(2 * Real.pi * Complex.I * α *
          (w + (1 / (2 * Real.pi * Complex.I * α)) * Complex.log (1 - sfun u σ α w)))
        = -(2 * Real.pi * Complex.I * α * w) + (-Complex.log (1 - sfun u σ α w)) := by
      rw [hA]; ring
    rw [harg, Complex.exp_add]
    have hL : Complex.exp (-Complex.log (1 - sfun u σ α w)) = (1 - sfun u σ α w)⁻¹ := by
      rw [Complex.exp_neg, Complex.exp_log hs]
    rw [hL, div_eq_mul_inv, Complex.exp_neg]
  have hEeq : Complex.exp (-(2 * Real.pi * Complex.I * α * w))
      = (tauC σ α w - σ) / tauC σ α w := exp_eq_tauC σ α w hσ hE
  -- `τ_f (F_f w) = σ / (1 - E/(1-s))`.
  have hLHS : tauC σ α (w + (1 / (2 * Real.pi * Complex.I * α)) * Complex.log (1 - sfun u σ α w))
      = σ / (1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w)) / (1 - sfun u σ α w)) := by
    rw [tauC, hexp]
  -- The key algebraic identity: `(1 - E/(1-s)) * τ(1 + τu - σu) = σ`.
  have hDW : (1 - ((tauC σ α w - σ) / tauC σ α w) / (1 - sfun u σ α w))
      * (tauC σ α w * (1 + tauC σ α w * u (tauC σ α w) - σ * u (tauC σ α w))) = σ := by
    rw [sfun]
    have hs' : 1 - σ * u (tauC σ α w) / (1 + tauC σ α w * u (tauC σ α w)) ≠ 0 := by
      rw [← sfun]; exact hs
    field_simp
    ring
  have hDne : (1 - ((tauC σ α w - σ) / tauC σ α w) / (1 - sfun u σ α w)) ≠ 0 := by
    intro h0
    have h1 : (0 : ℂ) = σ := by rw [← hDW, h0, zero_mul]
    exact hσ h1.symm
  rw [liftF, hLHS, hEeq]
  rw [div_eq_iff hDne]
  rw [hnf]
  have hW : tauC σ α w + tauC σ α w * (tauC σ α w - σ) * u (tauC σ α w)
      = tauC σ α w * (1 + tauC σ α w * u (tauC σ α w) - σ * u (tauC σ α w)) := by ring
  rw [hW, mul_comm]
  exact hDW.symm

end Work.Pert
