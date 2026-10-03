import Mathlib

namespace Work.Horn

open Filter Metric

/-- Local biholomorphism at a point where the derivative does not vanish: there is a ball around
`x` on which `f` is injective and whose image contains a ball around `f x`.

This follows from the inverse function theorem (through `HasStrictDerivAt.hasStrictFDerivAt_equiv`
and the associated `OpenPartialHomeomorph`). -/
theorem exists_ball_injOn_and_mapsTo {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : DifferentiableOn ℂ f D) {x : ℂ} (hx : x ∈ D) (hne : deriv f x ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < ε ∧ ∃ δ : ℝ, 0 < δ ∧ Metric.ball x ρ ⊆ D ∧
      Set.InjOn f (Metric.ball x ρ) ∧
      ∀ w : ℂ, ‖w - f x‖ < δ → ∃ u ∈ Metric.ball x ρ, f u = w := by
  -- `f` is analytic at `x`, hence strictly differentiable there, with derivative `deriv f x`.
  have hxa : AnalyticAt ℂ f x := hf.analyticAt (hD.mem_nhds hx)
  have hsd : HasStrictDerivAt f (deriv f x) x := hxa.hasStrictDerivAt
  -- The inverse function theorem produces an open partial homeomorphism which agrees with `f`.
  let e : OpenPartialHomeomorph ℂ ℂ :=
    (hsd.hasStrictFDerivAt_equiv hne).toOpenPartialHomeomorph f
  have hxe : x ∈ e.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have hcoe : (e : ℂ → ℂ) = f := rfl
  -- A small ball around `x` sits inside `D ∩ e.source`.
  have hmem : D ∩ e.source ∈ nhds x :=
    Filter.inter_mem (hD.mem_nhds hx) (e.open_source.mem_nhds hxe)
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub⟩ := Metric.mem_nhds_iff.mp hmem
  have hρpos : 0 < min ρ₀ (ε / 2) := lt_min hρ₀pos (half_pos hε)
  have hρlt : min ρ₀ (ε / 2) < ε :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsub : Metric.ball x (min ρ₀ (ε / 2)) ⊆ D ∩ e.source :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hρ₀sub
  have hDsub : Metric.ball x (min ρ₀ (ε / 2)) ⊆ D := hsub.trans Set.inter_subset_left
  -- Injectivity on that ball, transported from the homeomorphism `e`.
  have hinj : Set.InjOn f (Metric.ball x (min ρ₀ (ε / 2))) := by
    have h1 : Set.InjOn (e : ℂ → ℂ) (Metric.ball x (min ρ₀ (ε / 2))) :=
      e.injOn.mono (hsub.trans Set.inter_subset_right)
    simpa [hcoe] using h1
  -- `f` is open at `x`, so the image of the ball is a neighbourhood of `f x`.
  have hmap : Filter.map f (nhds x) = nhds (f x) := hsd.map_nhds_eq hne
  have hmem' : f '' Metric.ball x (min ρ₀ (ε / 2)) ∈ nhds (f x) := by
    rw [← hmap]
    exact Filter.image_mem_map (Metric.ball_mem_nhds x hρpos)
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hmem'
  exact ⟨min ρ₀ (ε / 2), hρpos, hρlt, δ, hδpos, hDsub, hinj, fun w hw => by
    obtain ⟨u, hu, hfu⟩ := hδsub (by rw [Metric.mem_ball, dist_eq_norm]; exact hw)
    exact ⟨u, hu, hfu⟩⟩

end Work.Horn
