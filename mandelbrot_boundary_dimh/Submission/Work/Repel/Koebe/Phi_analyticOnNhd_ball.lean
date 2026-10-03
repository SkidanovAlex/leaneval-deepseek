import Mathlib
import Submission.Work.Repel.Koebe.ExteriorWindingDefs

/-!
# Analyticity of `Φ` on the unit disc from a bound at infinity

For `g : ℂ → ℂ` the auxiliary function

`Phi g ζ v = v * phi g v + 1 - v * ζ`,   `phi g v = g v⁻¹ - v⁻¹` (and `phi g 0 = 0`),

equals `v * (g v⁻¹ - ζ)` for `v ≠ 0`.  We show that `Phi g ζ` is analytic on the open unit disc
whenever `g` is analytic on the exterior `{1 < ‖z‖}` of the unit disc and satisfies the bound
`‖g z - z‖ ≤ 1/2` for all large `‖z‖`.

The point is that the bound at infinity says precisely that `phi g` is *bounded* near the origin
(`‖phi g u‖ = ‖g u⁻¹ - u⁻¹‖ ≤ 1/2` for `u` close to `0`), so `v ↦ v * phi g v` has a removable
singularity at `0` — no hypothesis on the limit of `phi g u / u` is needed.  Away from the origin
`Phi g ζ` is `v * (g v⁻¹ - ζ)` and analyticity follows from the analyticity of `g` on the exterior.
-/

open Filter Topology
open scoped Topology

namespace Work.Repel.Koebe

/-- If `‖g z - z‖ ≤ 1/2` for all large `‖z‖`, then `phi g` is bounded by `1/2` in a neighbourhood
of the origin. -/
lemma phi_norm_le_half_of_bound {g : ℂ → ℂ}
    (hbound : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, ‖w‖ < ε → ‖phi g w‖ ≤ 1 / 2 := by
  obtain ⟨R, hR⟩ := hbound
  refine ⟨1 / (|R| + 1), by positivity, fun w hw => ?_⟩
  by_cases hw0 : w = 0
  · simp [hw0, phi_zero]
  · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hbig : |R| + 1 < ‖w‖⁻¹ := by
      have h := one_div_lt_one_div_of_lt hpos hw
      rwa [one_div_one_div, one_div] at h
    have hRw : R ≤ ‖w⁻¹‖ := by
      rw [norm_inv]; linarith [le_abs_self R]
    have := hR w⁻¹ hRw
    rwa [phi_apply hw0]

/-- The function `v ↦ v * phi g v` is continuous at the origin (with value `0`) under the same
bound at infinity: it is the product of `v → 0` with a bounded quantity. -/
lemma continuousAt_mul_phi_of_bound {g : ℂ → ℂ}
    (hbound : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2) :
    ContinuousAt (fun w : ℂ => w * phi g w) 0 := by
  obtain ⟨ε, hε0, hε⟩ := phi_norm_le_half_of_bound hbound
  rw [Metric.continuousAt_iff]
  intro δ hδ
  refine ⟨min ε (2 * δ), by positivity, fun w hw => ?_⟩
  have hwε : ‖w‖ < ε :=
    lt_of_lt_of_le (by simpa [dist_zero_right] using hw) (min_le_left _ _)
  have hwδ : ‖w‖ < 2 * δ :=
    lt_of_lt_of_le (by simpa [dist_zero_right] using hw) (min_le_right _ _)
  have hphi := hε w hwε
  rw [zero_mul, dist_zero_right, norm_mul]
  have h2 : ‖w‖ * ‖phi g w‖ ≤ ‖w‖ * (1 / 2) :=
    mul_le_mul_of_nonneg_left hphi (norm_nonneg _)
  have h3 : ‖w‖ * (1 / 2) < δ := by nlinarith [norm_nonneg w]
  linarith

/-- `Phi g ζ` is analytic at every nonzero point of the open unit disc, whenever `g` is analytic on
the exterior of the unit disc. -/
lemma analyticAt_Phi_of_ne {g : ℂ → ℂ} {ζ : ℂ}
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z) {v : ℂ} (hv0 : v ≠ 0) (hv1 : ‖v‖ < 1) :
    AnalyticAt ℂ (Phi g ζ) v := by
  have hphi : AnalyticAt ℂ (phi g) v := analyticAt_phi_of_ne hg hv0 hv1
  have h : AnalyticAt ℂ (fun w : ℂ => (w * phi g w + 1) - w * ζ) v :=
    ((analyticAt_id.mul hphi).add analyticAt_const).sub (analyticAt_id.mul analyticAt_const)
  exact h

/-- **Main lemma.** If `g` is analytic on the exterior `{1 < ‖z‖}` of the unit disc with
`‖g z - z‖ ≤ 1/2` for all large `‖z‖`, then `Φ g ζ` is analytic on the open unit disc. -/
theorem Phi_analyticOnNhd_ball {g : ℂ → ℂ} {ζ : ℂ}
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    (hbound : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2) :
    AnalyticOnNhd ℂ (Work.Repel.Koebe.Phi g ζ) (Metric.ball (0 : ℂ) 1) := by
  intro v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  rcases eq_or_ne v 0 with rfl | hv0
  · -- at the origin: removable singularity for `v ↦ v * phi g v` and `1 - v * ζ` is entire
    have hcont : ContinuousAt (Phi g ζ) 0 := by
      have h1 : ContinuousAt (fun w : ℂ => w * phi g w + 1) 0 :=
        (continuousAt_mul_phi_of_bound hbound).add continuousAt_const
      have h2 : ContinuousAt (fun w : ℂ => w * ζ) 0 := by fun_prop
      exact h1.sub h2
    have hdiff : ∀ᶠ w in nhdsWithin (0 : ℂ) ({0}ᶜ), DifferentiableAt ℂ (Phi g ζ) w := by
      have hball : Metric.ball (0 : ℂ) 1 ∈ nhdsWithin (0 : ℂ) ({0}ᶜ) :=
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))
      filter_upwards [self_mem_nhdsWithin, hball] with w hw0 hw1
      exact (analyticAt_Phi_of_ne hg hw0
        (by simpa [Metric.mem_ball, dist_zero_right] using hw1)).differentiableAt
    exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hcont
  · exact analyticAt_Phi_of_ne hg hv0 hv

end Work.Repel.Koebe
