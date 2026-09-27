import Mathlib

namespace Work.Drive

open Filter Set
open scoped Topology

/-- **Diagonal slope limit.** The secant slope of a `C¹` curve tends to the tangent at the
diagonal: `(c t' - c s) / (t' - s) → c'(t)` as `s < t'` tend to `t`.

Proof route: set `g u := c u - u • deriv c t`, so `deriv g t = 0`. For `ε > 0` use continuity of
`deriv c` at `t` and `Convex.norm_image_sub_le_of_norm_deriv_le` on `Set.Icc q.1 q.2` to get
`‖g q.2 - g q.1‖ ≤ ε * (q.2 - q.1)`, then
`(c q.2 - c q.1)/(q.2 - q.1) = deriv c t + (g q.2 - g q.1)/(q.2 - q.1)`. -/
theorem tendsto_slope_diag (c : ℝ → ℝ × ℝ) (hc : ContDiff ℝ 1 c) (t : ℝ) :
    Filter.Tendsto (fun q : ℝ × ℝ => (q.2 - q.1)⁻¹ • (c q.2 - c q.1))
      (nhdsWithin (t, t) {q : ℝ × ℝ | q.1 < q.2}) (nhds (deriv c t)) := by
  set g : ℝ → ℝ × ℝ := fun u => c u - u • deriv c t with hg
  have hg' : g = c - (fun y : ℝ => y • deriv c t) := hg
  have hc_diff : Differentiable ℝ c := hc.differentiable (by norm_num)
  have hsmul_diff : ∀ u : ℝ, DifferentiableAt ℝ (fun y : ℝ => y • deriv c t) u :=
    fun u => (differentiableAt_id (x := u)).smul_const (deriv c t)
  have hderiv_smul : ∀ u : ℝ, deriv (fun y : ℝ => y • deriv c t) u = deriv c t := by
    intro u
    simpa using (deriv_smul_const (x := u) differentiableAt_id (deriv c t))
  have hderiv_g : ∀ u : ℝ, deriv g u = deriv c u - deriv c t := by
    intro u
    rw [hg', deriv_sub (hc_diff u) (hsmul_diff u), hderiv_smul u]
  have hg_diff : ∀ u : ℝ, DifferentiableAt ℝ g u := by
    intro u
    rw [hg']
    exact (hc_diff u).sub (hsmul_diff u)
  have hg_cont : Continuous (deriv g) := by
    rw [funext hderiv_g]
    exact hc.continuous_deriv_one.sub continuous_const
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0:ℝ) < ε/2 := by linarith
  have hlt : deriv g t = 0 := by rw [hderiv_g t, sub_self]
  have hev : ∀ᶠ u in nhds t, ‖deriv g u‖ < ε/2 := by
    have htend : Filter.Tendsto (deriv g) (nhds t) (nhds 0) := by
      rw [← hlt]
      exact hg_cont.continuousAt (x := t)
    have := (Metric.tendsto_nhds.mp htend) (ε/2) hε2
    simpa using this
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨δ, hδpos, ?_⟩
  intro q hq hlt2
  have hlt2' : q.1 < q.2 := hlt2
  have hq1 : |q.1 - t| < δ := by
    have h := hq
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
    exact lt_of_le_of_lt (le_max_left _ _) h
  have hq2 : |q.2 - t| < δ := by
    have h := hq
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
    exact lt_of_le_of_lt (le_max_right _ _) h
  have hq1a : t - δ < q.1 := by have := (abs_lt.mp hq1).1; linarith
  have hq2b : q.2 < t + δ := by have := (abs_lt.mp hq2).2; linarith
  have hq21 : 0 < q.2 - q.1 := by linarith
  have hinner : g q.2 - g q.1 = (c q.2 - c q.1) - (q.2 - q.1) • deriv c t := by
    rw [hg]
    simp only
    rw [sub_smul]
    abel
  have hkey : (q.2 - q.1)⁻¹ • (g q.2 - g q.1) =
      (q.2 - q.1)⁻¹ • (c q.2 - c q.1) - deriv c t := by
    rw [hinner, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hq21), one_smul]
  have hmvt : ‖g q.2 - g q.1‖ ≤ (ε/2) * ‖q.2 - q.1‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc q.1 q.2) (C := ε/2)
      ?_ ?_ (convex_Icc _ _) ?_ ?_
    · intro x _
      exact hg_diff x
    · intro x hx
      rw [Set.mem_Icc] at hx
      have hxδ : dist x t < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hq1a, hq2b, hx.1, hx.2]
      exact le_of_lt (hδ hxδ)
    · exact Set.left_mem_Icc.mpr (le_of_lt hlt2')
    · exact Set.right_mem_Icc.mpr (le_of_lt hlt2')
  rw [dist_eq_norm, ← hkey, norm_smul]
  have h1 : ‖(q.2 - q.1)⁻¹‖ = (q.2 - q.1)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq21)]
  rw [h1]
  have h2 : ‖q.2 - q.1‖ = q.2 - q.1 := Real.norm_of_nonneg (le_of_lt hq21)
  calc (q.2 - q.1)⁻¹ * ‖g q.2 - g q.1‖
      ≤ (q.2 - q.1)⁻¹ * ((ε/2) * ‖q.2 - q.1‖) :=
        mul_le_mul_of_nonneg_left hmvt (inv_nonneg.mpr (le_of_lt hq21))
    _ = (q.2 - q.1)⁻¹ * ((ε/2) * (q.2 - q.1)) := by rw [h2]
    _ = ε/2 := by
        rw [← mul_assoc, mul_comm ((q.2 - q.1)⁻¹) (ε/2), mul_assoc,
          inv_mul_cancel₀ (ne_of_gt hq21), mul_one]
    _ < ε := by linarith

end Work.Drive
