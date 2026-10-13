/-
# `Work.CoreResiduals.BiotSavart.norm_bsIntegrand_le_interp` — the interpolation bound for the
derivative integrand

For a vorticity `g : ℝ³ → ℝ³` that is *bounded* by `A ≥ 0` and `α`-Hölder with constant `2H ≥ 0`
(`0 < α < 1`), the derivative integrand of the Biot–Savart field obeys the two-parameter bound

  `‖bsIntegrand g x a‖ ≤ 4 (2A)^α (2H)^{1-α} ‖x - a‖^{α(1-α) - 3}`.

This is the pointwise input of `norm_bsDerivCLM_le_of_bdd_holder`: it combines the *interpolation*
of the uniform bound `‖g a - g x‖ ≤ 2A` with the Hölder bound `‖g a - g x‖ ≤ 2H ‖a - x‖^α`
(lemma `norm_gSub_le_interp`, the `(2A)^{1-t}(2H)^t` computation at `t = 1 - α`) with the
kernel estimate `‖kDerivCLM b‖ ≤ 4/‖b‖³` and the identity
`‖b‖^{α(1-α)} · (4/‖b‖³) = 4 ‖b‖^{α(1-α) - 3}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.BiotSavart.IntegrandDefs
import Submission.Work.StabilityFar.Decay.norm_crossL_le
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_le
import Submission.Work.CoreResiduals.BiotSavart.norm_gSub_le_interp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

theorem norm_bsIntegrand_le_interp {α A H : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 ≤ A) (hH : 0 ≤ H)
    {g : Work.LWP.R3 → Work.LWP.R3} (hbdd : ∀ a, ‖g a‖ ≤ A)
    (hhold : ∀ a b : Work.LWP.R3, ‖g a - g b‖ ≤ 2 * H * ‖a - b‖ ^ α)
    (x a : Work.LWP.R3) :
    ‖Work.CoreResiduals.BiotSavart.bsIntegrand g x a‖ ≤
      4 * (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α) - 3) := by
  rcases eq_or_ne x a with hxa | hxa
  · -- the singular point `x = a`: both sides vanish
    rw [hxa]
    have hz : bsIntegrand g a a = 0 := by
      simp [bsIntegrand, crossL_zero]
    rw [hz, norm_zero, sub_self, norm_zero, Real.zero_rpow]
    · norm_num
    · have h1 : (0 : ℝ) < 1 - α := by linarith
      have h2 : α * (1 - α) < 3 := by nlinarith
      linarith
  · have hr : (0 : ℝ) < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
    -- the interpolation of the bounded-ness and Hölder bounds on `g a - g x`
    have hd : ‖g a - g x‖ ≤ (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α)) :=
      norm_gSub_le_interp hα hα1 hA hH hbdd hhold x a
    calc ‖bsIntegrand g x a‖
        ≤ ‖crossL (g a - g x)‖ * ‖kDerivCLM (x - a)‖ := by
          rw [bsIntegrand]
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖g a - g x‖ * (4 / ‖x - a‖ ^ 3) := by
          gcongr
          · exact norm_crossL_le _
          · exact norm_kDerivCLM_le (x - a) ‖x - a‖ hr le_rfl
      _ ≤ ((2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α))) *
            (4 / ‖x - a‖ ^ 3) :=
          mul_le_mul_of_nonneg_right hd (by positivity)
      _ = 4 * (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α) - 3) := by
          rw [Real.rpow_sub hr, Real.rpow_ofNat]
          ring

end Work.CoreResiduals.BiotSavart
