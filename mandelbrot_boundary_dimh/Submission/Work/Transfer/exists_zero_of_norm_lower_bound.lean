import Mathlib

namespace Work.Transfer

/-- **Minimum modulus / Rouché-type criterion.** If `g` is holomorphic on the closed ball
`closedBall c_s r` (i.e. differentiable there and continuous on its closure) and `‖g‖` is bounded
below by `δ > 0` on the boundary sphere, while the value at the centre is small (`< δ / 2`), then
`g` must vanish somewhere on the closed ball.

This is the maximum modulus principle applied to `g⁻¹`: if `g` had no zero on the closed ball,
`g⁻¹` would be holomorphic and `‖g⁻¹‖` would attain its maximum on the sphere, giving
`(δ/2)⁻¹ < ‖g c_s‖⁻¹ = ‖g⁻¹ c_s‖ ≤ δ⁻¹`, a contradiction. -/
theorem exists_zero_of_norm_lower_bound {g : ℂ → ℂ} {c_s : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hg : DiffContOnCl ℂ g (Metric.closedBall c_s r))
    (hgb : ∀ z ∈ Metric.sphere c_s r, δ ≤ ‖g z‖)
    (hc : ‖g c_s‖ < δ / 2) :
    ∃ z ∈ Metric.closedBall c_s r, g z = 0 := by
  by_contra hcon
  push Not at hcon
  -- `g` vanishes nowhere on the closed ball, hence on its closure (= itself).
  have hne : ∀ x ∈ closure (Metric.closedBall c_s r), g x ≠ 0 :=
    fun x hx => hcon x (by rwa [Metric.closure_closedBall] at hx)
  -- so `g⁻¹` is again holomorphic on the closed ball.
  have hginv : DiffContOnCl ℂ g⁻¹ (Metric.closedBall c_s r) := hg.inv hne
  have hbdd : Bornology.IsBounded (Metric.closedBall c_s r) := Metric.isBounded_closedBall
  -- `‖g⁻¹‖` is bounded by `δ⁻¹` on the boundary sphere.
  have hbound : ∀ z ∈ frontier (Metric.closedBall c_s r), ‖(g⁻¹) z‖ ≤ δ⁻¹ := by
    intro z hz
    rw [frontier_closedBall c_s (ne_of_gt hr)] at hz
    rw [Pi.inv_apply, norm_inv]
    exact inv_anti₀ hδ (hgb z hz)
  have hcc : c_s ∈ Metric.closedBall c_s r := Metric.mem_closedBall_self (le_of_lt hr)
  have hcc' : c_s ∈ closure (Metric.closedBall c_s r) := by
    rw [Metric.closure_closedBall]; exact hcc
  -- maximum modulus principle for `g⁻¹`
  have hkey : ‖(g⁻¹) c_s‖ ≤ δ⁻¹ :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hginv hbound hcc'
  -- but the value at the centre is large: `δ ≤ ‖g c_s‖ < δ / 2`, absurd.
  have hgnz : g c_s ≠ 0 := hcon c_s hcc
  have hpos : 0 < ‖g c_s‖ := norm_pos_iff.mpr hgnz
  rw [Pi.inv_apply, norm_inv] at hkey
  have hle : δ ≤ ‖g c_s‖ := (inv_le_inv₀ hpos hδ).mp hkey
  linarith

end Work.Transfer
