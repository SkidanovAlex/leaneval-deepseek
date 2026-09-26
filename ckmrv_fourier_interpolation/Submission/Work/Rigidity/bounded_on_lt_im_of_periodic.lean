import Mathlib

namespace Work.Rigidity

open UpperHalfPlane
open scoped Manifold

/-- A holomorphic function on the upper half plane which is periodic with a positive real
period `h` and bounded at `i∞` is bounded on every half plane `{τ | a ≤ τ.im}` with `a > 0`.

Indeed, if `F` has period `h` then `F τ = (cuspFunction h F) (exp (2 * π * I * τ / h))`, and
`cuspFunction h F` is holomorphic on the unit disc (this is where holomorphy, periodicity and
boundedness at `i∞` are used).  For `τ.im ≥ a > 0` the point `exp (2 * π * I * τ / h)` lies in
the closed disc of radius `exp (-2 * π * a / h) < 1`, a compact set, so `cuspFunction h F` is
bounded there. -/
theorem bounded_on_lt_im_of_periodic {F : UpperHalfPlane → Complex} {h a : ℝ} (hh : 0 < h)
    (ha : 0 < a)
    (hper : Function.Periodic (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) h)
    (hfhol : MDiff F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) :
    ∃ M : ℝ, ∀ τ : UpperHalfPlane, a ≤ τ.im → ‖F τ‖ ≤ M := by
  set R : ℝ := Real.exp (-2 * Real.pi * a / h) with hR
  have hRlt : R < 1 := by
    rw [hR, Real.exp_lt_one_iff]
    have hnum : -2 * Real.pi * a < 0 := by nlinarith [Real.pi_pos, ha]
    exact div_neg_of_neg_of_pos hnum hh
  have hcont : ContinuousOn (UpperHalfPlane.cuspFunction h F) (Metric.closedBall 0 R) :=
    (UpperHalfPlane.differentiableOn_cuspFunction_ball hh hper hfhol hbdd).continuousOn.mono
      (Metric.closedBall_subset_ball hRlt)
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_closedBall (0:ℂ) R) hcont
  refine ⟨M, fun τ hτ => ?_⟩
  rw [← UpperHalfPlane.eq_cuspFunction (h := h) τ hh.ne' hper]
  refine hM _ ?_
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Function.Periodic.norm_qParam, hR]
  refine Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ hh.le)
  have hτ' : a ≤ (τ : ℂ).im := by simpa using hτ
  nlinarith [hτ', Real.pi_pos]

end Work.Rigidity
