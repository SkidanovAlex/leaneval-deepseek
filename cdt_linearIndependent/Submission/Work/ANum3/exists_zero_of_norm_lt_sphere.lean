import Mathlib

namespace Work.ANum3

/-- **Minimum modulus principle (contrapositive form).** If `f` is analytic on the closed disc
`‖z‖ ≤ ρ`, has no zero there, satisfies `‖f 0‖ < c`, and `c ≤ ‖f z‖` on the circle `‖z‖ = ρ`,
then we reach a contradiction: `‖f 0‖` is dominated by the boundary values.

Proof: apply the maximum modulus principle to `g = f⁻¹`, which is holomorphic on the open disc
and continuous on its closure; on the circle `‖z‖ = ρ` we have `‖g z‖ = ‖f z‖⁻¹ ≤ c⁻¹`, hence
`‖f 0‖⁻¹ = ‖g 0‖ ≤ c⁻¹`, i.e. `c ≤ ‖f 0‖`, contradicting `‖f 0‖ < c`. -/
theorem exists_zero_of_norm_lt_sphere {f : ℂ → ℂ} {ρ c : ℝ} (hρ : 0 < ρ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, AnalyticAt ℂ f z)
    (hne : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, f z ≠ 0)
    (hc : ‖f 0‖ < c) (hsph : ∀ z : ℂ, ‖z‖ = ρ → c ≤ ‖f z‖) : False := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hcpos : 0 < c := lt_of_le_of_lt (norm_nonneg _) hc
  -- `f` is holomorphic on the open disc
  have hfd : DifferentiableOn ℂ f (Metric.ball 0 ρ) :=
    fun z hz => (hf z (Metric.ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt
  -- so is `g = f⁻¹`, `f` being zero-free there
  have hgd : DifferentiableOn ℂ (fun z => (f z)⁻¹) (Metric.ball 0 ρ) :=
    hfd.inv (fun z hz => hne z (Metric.ball_subset_closedBall hz))
  -- `f` is continuous on the closed disc, hence so is `g`
  have hfc : ContinuousOn f (Metric.closedBall (0 : ℂ) ρ) :=
    fun z hz => (hf z hz).continuousAt.continuousWithinAt
  have hgc : ContinuousOn (fun z => (f z)⁻¹) (closure (Metric.ball 0 ρ)) := by
    rw [closure_ball 0 hρne]
    exact hfc.inv₀ hne
  have hdc : DiffContOnCl ℂ (fun z => (f z)⁻¹) (Metric.ball 0 ρ) := DiffContOnCl.mk hgd hgc
  -- the boundary bound `‖g‖ ≤ c⁻¹` on the circle
  have hC : ∀ w ∈ frontier (Metric.ball 0 ρ), ‖(f w)⁻¹‖ ≤ c⁻¹ := by
    intro w hw
    rw [frontier_ball 0 hρne, Metric.mem_sphere] at hw
    have hwn : ‖w‖ = ρ := by rw [dist_eq_norm, sub_zero] at hw; exact hw
    have hfw : c ≤ ‖f w‖ := hsph w hwn
    have hfwpos : 0 < ‖f w‖ := lt_of_lt_of_le hcpos hfw
    rw [norm_inv]
    exact (inv_le_inv₀ hfwpos hcpos).mpr hfw
  -- maximum modulus principle applied to `g` at the centre `0`
  have hzcl : (0 : ℂ) ∈ closure (Metric.ball 0 ρ) := by
    rw [closure_ball 0 hρne, Metric.mem_closedBall]
    simpa using hρ.le
  have h0bd := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc hC hzcl
  -- translate back to a lower bound for `‖f 0‖`
  have hf0ne : f 0 ≠ 0 := hne 0 (by rw [Metric.mem_closedBall]; simpa using hρ.le)
  have hf0pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0ne
  rw [norm_inv] at h0bd
  have : c ≤ ‖f 0‖ := (inv_le_inv₀ hf0pos hcpos).mp h0bd
  exact absurd this (not_le.mpr hc)

end Work.ANum3
