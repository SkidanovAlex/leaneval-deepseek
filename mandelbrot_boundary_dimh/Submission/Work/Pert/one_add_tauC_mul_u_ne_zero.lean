import Mathlib
import Submission.Work.Pert.Basic

namespace Work.Pert

/-- If the denominator `1 + τ_f(w) · u(τ_f(w))` of `s = σu(τ)/(1+τu(τ))` vanished at `w`,
then `sfun u σ α w = 0`, hence `1 - sfun = 1` and `log (1 - sfun) = 0`, so that
`liftF u σ α w = w`; the hypothesis `‖liftF u σ α w - (w+1)‖ ≤ 1/32` would then read
`‖w - (w+1)‖ = 1 ≤ 1/32`, a contradiction. -/
theorem one_add_tauC_mul_u_ne_zero {u : ℂ → ℂ} {σ α w : ℂ}
    (hNT : ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32) :
    (1 : ℂ) + Work.Pert.tauC σ α w * u (Work.Pert.tauC σ α w) ≠ 0 := by
  intro h
  -- If the denominator vanishes, `sfun` (a division by zero) is `0`.
  have hsfun : sfun u σ α w = 0 := by
    unfold sfun
    rw [h, div_zero]
  -- Hence `log (1 - sfun) = log 1 = 0` and `liftF u σ α w = w`.
  have hlift : liftF u σ α w = w := by
    unfold liftF
    rw [hsfun, sub_zero, Complex.log_one, mul_zero, add_zero]
  -- The hypothesis then forces `‖w - (w+1)‖ = 1 ≤ 1/32`, absurd.
  rw [hlift] at hNT
  have hnorm : ‖w - (w + 1)‖ = 1 := by
    have : w - (w + 1) = (-1 : ℂ) := by ring
    rw [this, norm_neg, norm_one]
  rw [hnorm] at hNT
  norm_num at hNT

end Work.Pert
