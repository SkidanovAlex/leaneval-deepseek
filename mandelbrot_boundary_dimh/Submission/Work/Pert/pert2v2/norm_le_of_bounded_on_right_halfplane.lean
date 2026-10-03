import Mathlib

namespace Work.Pert.pert2v2

open Set Metric Filter Topology Asymptotics Bornology

-- `hM` is part of the (fixed) statement but is not needed by the proof, since `hbdd` forces `M ≥ 0`.
set_option linter.unusedVariables false in
/-- **Phragmén–Lindelöf on the closed right half-plane.**

Let `F : ℂ → ℂ` be holomorphic on the open right half-plane `{z | 0 < z.re}` (and continuous on
its closure), bounded there by `M`, and bounded by `C` on the imaginary axis.  Then `‖F z‖ ≤ C`
on the *whole* closed right half-plane `{z | 0 ≤ z.re}`: a bounded holomorphic function on a
half-plane is controlled by its boundary values, the bound at infinity being irrelevant because
`F` is bounded (`cobounded ℂ ⊓ 𝓟 {z | 0 < z.re}` admits the sub-exponential majorant
`w ↦ exp 0 = 1`).

This is exactly Mathlib's `PhragmenLindelof.right_half_plane_of_bounded_on_real`, whose growth
condition `c < 2` is met with the exponent `c = 0`. -/
theorem norm_le_of_bounded_on_right_halfplane {F : ℂ → ℂ} {C M : ℝ} (hM : 0 < M)
    (hd : DiffContOnCl ℂ F {z : ℂ | 0 < z.re}) (hbdd : ∀ z : ℂ, 0 < z.re → ‖F z‖ ≤ M)
    (him : ∀ x : ℝ, ‖F ((x : ℂ) * Complex.I)‖ ≤ C) :
    ∀ z : ℂ, 0 ≤ z.re → ‖F z‖ ≤ C := by
  intro z hz
  refine PhragmenLindelof.right_half_plane_of_bounded_on_real hd ?_ ?_ him hz
  · -- growth condition: `F` is bounded on the half-plane, so the majorant `exp (0 * ‖z‖ ^ 0) = 1`
    -- suffices (exponent `0 < 2`).
    refine ⟨0, by norm_num, 0, ?_⟩
    refine IsBigO.of_bound M ?_
    refine Filter.Eventually.filter_mono inf_le_right ?_
    rw [Filter.eventually_principal]
    intro w hw
    have h1 : ‖F w‖ ≤ M := hbdd w hw
    simp only [Real.rpow_zero, mul_one, Real.exp_zero, norm_one] at h1 ⊢
    exact h1
  · -- boundedness on the positive real axis, from `hbdd` at large `x`
    refine ⟨M, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hbdd (x : ℂ) (by simpa using hx)

end Work.Pert.pert2v2
