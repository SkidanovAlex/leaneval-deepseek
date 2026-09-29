import Mathlib
set_option linter.unusedVariables false

namespace Work.TMContract.Gluing

/-- **Auxiliary lemma (a neighbourhood on which `deriv N` stays positive).**

If `deriv N` is continuous at an interior point `x₀ ∈ Ioo a b` and `deriv N x₀ > 0`, then
there is a nondegenerate closed interval `[c,d] ⊆ Ioo a b` (indeed a neighbourhood of `x₀`
inside the ball of the continuity modulus) on which `deriv N ≥ deriv N x₀ / 2 > 0`. -/
theorem deriv_ge_half_on_neighborhood {N : ℝ → ℝ} {a b x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo a b) (hpos : 0 < deriv N x₀)
    (hcont : ContinuousAt (deriv N) x₀) :
    ∃ c d : ℝ, a < c ∧ c < d ∧ d < b ∧
      ∀ x ∈ Set.Ioo c d, deriv N x₀ / 2 ≤ deriv N x := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousAt_iff.mp hcont (deriv N x₀ / 2) (by linarith)
  have hxa : 0 < x₀ - a := by linarith [hx₀.1]
  have hbx : 0 < b - x₀ := by linarith [hx₀.2]
  refine ⟨x₀ - min δ (x₀ - a) / 2, x₀ + min δ (b - x₀) / 2, ?_, ?_, ?_, ?_⟩
  · have h1 : 0 < min δ (x₀ - a) := lt_min hδpos hxa
    have h2 : min δ (x₀ - a) ≤ x₀ - a := min_le_right _ _
    linarith
  · have h1 : 0 < min δ (x₀ - a) := lt_min hδpos hxa
    have h2 : 0 < min δ (b - x₀) := lt_min hδpos hbx
    linarith
  · have h1 : 0 < min δ (b - x₀) := lt_min hδpos hbx
    have h2 : min δ (b - x₀) ≤ b - x₀ := min_le_right _ _
    linarith
  · intro x hx
    have hp : min δ (x₀ - a) ≤ δ := min_le_left _ _
    have hq : min δ (b - x₀) ≤ δ := min_le_left _ _
    have hdist : dist x x₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have h2 := hδ hdist
    rw [Real.dist_eq, abs_lt] at h2
    linarith [h2.1]

/-- **Auxiliary lemma (mean value theorem, uniform slope form).**

If `N` is continuous on `[c,d]`, differentiable on its interior `(c,d)`, and `deriv N ≥ c₀`
on `(c,d)`, then `N` grows at least linearly with rate `c₀` on `[c,d]`:
`c₀ * (y - x) ≤ N y - N x` for `x < y` in `[c,d]`.

This is the `≤`-form of `Convex.mul_sub_le_image_sub_of_le_deriv` applied to the convex set
`Icc c d` (whose interior is `Ioo c d`). -/
theorem le_slope_on_Icc_of_deriv_ge {N : ℝ → ℝ} {c d c₀ : ℝ}
    (hcontN : ContinuousOn N (Set.Icc c d))
    (hdiffN : DifferentiableOn ℝ N (Set.Icc c d))
    (hge : ∀ x ∈ Set.Ioo c d, c₀ ≤ deriv N x) :
    ∀ x ∈ Set.Icc c d, ∀ y ∈ Set.Icc c d, x < y → c₀ * (y - x) ≤ N y - N x := by
  intro x hx y hy hxy
  have hd : DifferentiableOn ℝ N (interior (Set.Icc c d)) := by
    rw [interior_Icc]; exact hdiffN.mono Set.Ioo_subset_Icc_self
  refine Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc c d) hcontN hd ?_ x hx y hy hxy.le
  intro z hz
  rw [interior_Icc] at hz
  exact hge z hz

theorem slope_bound_of_deriv_pos_at_point {N : ℝ → ℝ} {a b x₀ : ℝ} (hab : a < b)
    (hx₀ : x₀ ∈ Set.Ioo a b) (hpos : 0 < deriv N x₀)
    (hcont : ContinuousAt (deriv N) x₀)
    (hcontN : ContinuousOn N (Set.Ioo a b)) (hdiffN : DifferentiableOn ℝ N (Set.Ioo a b)) :
    ∃ c d c₀ : ℝ, a < c ∧ c < d ∧ d < b ∧ 0 < c₀ ∧
      ∀ x ∈ Set.Icc c d, ∀ y ∈ Set.Icc c d, x < y → c₀ * (y - x) ≤ N y - N x := by
  obtain ⟨c, d, hac, hcd, hdb, hge⟩ := deriv_ge_half_on_neighborhood hx₀ hpos hcont
  refine ⟨c, d, deriv N x₀ / 2, hac, hcd, hdb, by linarith, ?_⟩
  refine le_slope_on_Icc_of_deriv_ge ?_ ?_ hge
  · exact hcontN.mono fun x hx => ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩
  · exact hdiffN.mono fun x hx => ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩

end Work.TMContract.Gluing
