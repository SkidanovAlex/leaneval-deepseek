import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter
open scoped Topology

/-- Near a point where an analytic function has derivative of norm bigger than `1`,
`g` expands distances by a uniform factor `c > 1`. -/
theorem expansion_of_one_lt_norm_deriv {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : AnalyticAt ℂ g z₀) (hlarge : 1 < ‖deriv g z₀‖) :
    ∃ ε > 0, ∃ c > 1, ∀ z : ℂ, ‖z - z₀‖ < ε → c * ‖z - z₀‖ ≤ ‖g z - g z₀‖ := by
  -- `g` is differentiable at `z₀`, with the difference quotient tending to `deriv g z₀`.
  have hderiv : HasDerivAt g (deriv g z₀) z₀ := hg.differentiableAt.hasDerivAt
  have hslope : Tendsto (slope g z₀) (𝓝[{z₀}ᶜ] z₀) (𝓝 (deriv g z₀)) := hderiv.tendsto_slope
  have hnorm : Tendsto (fun z => ‖slope g z₀ z‖) (𝓝[{z₀}ᶜ] z₀) (𝓝 ‖deriv g z₀‖) := hslope.norm
  -- The candidate expansion factor, strictly between `1` and `‖deriv g z₀‖`.
  set c : ℝ := (1 + ‖deriv g z₀‖) / 2 with hcdef
  have hc_gt : 1 < c := by rw [hcdef]; linarith
  have hc_lt : c < ‖deriv g z₀‖ := by rw [hcdef]; linarith
  -- Eventually (away from `z₀`) the difference quotient has norm bigger than `c`.
  have hev : ∀ᶠ z in 𝓝[{z₀}ᶜ] z₀, c < ‖slope g z₀ z‖ :=
    hnorm.eventually (isOpen_Ioi.mem_nhds hc_lt)
  -- Hence the expansion inequality holds on a punctured neighbourhood.
  have hineq : ∀ᶠ z in 𝓝[{z₀}ᶜ] z₀, c * ‖z - z₀‖ ≤ ‖g z - g z₀‖ := by
    filter_upwards [hev, self_mem_nhdsWithin] with z hz hzne
    have hzne' : z ≠ z₀ := by simpa [Set.mem_compl_singleton_iff] using hzne
    have hrpos : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne')
    have hrne : ‖z - z₀‖ ≠ 0 := ne_of_gt hrpos
    have hval : ‖slope g z₀ z‖ = ‖z - z₀‖⁻¹ * ‖g z - g z₀‖ := by
      rw [show slope g z₀ z = (z - z₀)⁻¹ • (g z - g z₀) from rfl, norm_smul, norm_inv]
    rw [hval] at hz
    have hlt : c * ‖z - z₀‖ < ‖g z - g z₀‖ := by
      have h2 := mul_lt_mul_of_pos_right hz hrpos
      rwa [mul_assoc, mul_comm ‖g z - g z₀‖ ‖z - z₀‖, ← mul_assoc,
        inv_mul_cancel₀ hrne, one_mul] at h2
    exact le_of_lt hlt
  -- Extract a metric radius from the punctured-neighbourhood statement.
  rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hineq
  obtain ⟨ε, hεpos, hε⟩ := hineq
  refine ⟨ε, hεpos, c, hc_gt, fun z hz => ?_⟩
  by_cases h : z = z₀
  · subst h; simp
  · refine hε ⟨?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using hz
    · simpa [Set.mem_compl_singleton_iff] using h

end Work.LandLeaves
