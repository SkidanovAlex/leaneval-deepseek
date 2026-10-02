import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE.Segment

/-- The point `y + μ·(p - y)` of the segment from `y` to `p` (at parameter `μ`) is at
distance `|1 - μ| · dist y p` from `p`. -/
private lemma dist_segment (y p : ℂ) (μ : ℝ) :
    dist (y + ((μ : ℝ) : ℂ) * (p - y)) p = |1 - μ| * dist y p := by
  rw [dist_eq_norm]
  have hsub : y + ((μ : ℝ) : ℂ) * (p - y) - p = (((μ - 1 : ℝ)) : ℂ) * (p - y) := by
    push_cast
    ring
  rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, dist_comm, dist_eq_norm]

/-- If the real part of `trans` blows up to `-∞` as `c → p` along `Nm`, and the segment
`y +(0,1)·(p - y)` lies in `Nm`, then some point of that segment (with parameter in `[0,1)`)
already satisfies `(trans ·).re < M`. -/
theorem blowup_at_endpoint {y p : ℂ} {trans : ℂ → ℂ} {Nm : Set ℂ} {M : ℝ}
    (hblow : Filter.Tendsto (fun c => (trans c).re) (nhdsWithin p Nm) Filter.atBot)
    (hseg : ∀ μ ∈ Set.Ico (0 : ℝ) 1, y + ((μ : ℝ) : ℂ) * (p - y) ∈ Nm) :
    ∃ μ₀ ∈ Set.Ico (0 : ℝ) 1, (trans (y + ((μ₀ : ℝ) : ℂ) * (p - y))).re < M := by
  -- `trans.re < M` eventually near `p` within `Nm`.
  have hev : ∀ᶠ c in nhdsWithin p Nm, (trans c).re < M :=
    hblow.eventually (Filter.Iio_mem_atBot M)
  rw [Filter.eventually_iff, mem_nhdsWithin_iff_exists_mem_nhds_inter] at hev
  obtain ⟨u, hu_nhds, hu_sub⟩ := hev
  -- a ball about `p` contained in `u`
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp hu_nhds
  by_cases h : y = p
  · -- degenerate segment: take `μ₀ = 0`
    refine ⟨0, by norm_num [Set.mem_Ico], ?_⟩
    have hypt : y + ((0:ℝ):ℂ) * (p - y) = p := by rw [← h]; simp
    have hp_u : p ∈ u := hball (by rw [Metric.mem_ball, dist_self]; exact hεpos)
    have hp_Nm : p ∈ Nm := by
      have h0 := hseg 0 (by norm_num [Set.mem_Ico])
      rwa [hypt] at h0
    have hfin := hu_sub ⟨hp_u, hp_Nm⟩
    rwa [hypt]
  · -- take `μ₀ = 1 - δ` with `δ` small
    have hdpos : 0 < dist y p := dist_pos.mpr h
    set δ : ℝ := min (1/2) (ε / (2 * dist y p)) with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by norm_num) (by positivity)
    have hδle_half : δ ≤ 1/2 := by rw [hδdef]; exact min_le_left _ _
    have hδle : δ ≤ ε / (2 * dist y p) := by rw [hδdef]; exact min_le_right _ _
    refine ⟨1 - δ, ⟨by linarith, by linarith⟩, ?_⟩
    have hdist : dist (y + (((1 - δ) : ℝ) : ℂ) * (p - y)) p = δ * dist y p := by
      rw [dist_segment, show (1:ℝ) - (1 - δ) = δ by ring, abs_of_pos hδpos]
    have hmem_ball : y + (((1 - δ) : ℝ) : ℂ) * (p - y) ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, hdist]
      have h1 : δ * dist y p ≤ (ε / (2 * dist y p)) * dist y p :=
        mul_le_mul_of_nonneg_right hδle (le_of_lt hdpos)
      have h2 : (ε / (2 * dist y p)) * dist y p = ε / 2 := by
        field_simp
      rw [h2] at h1
      linarith
    have hmem_Nm : y + (((1 - δ) : ℝ) : ℂ) * (p - y) ∈ Nm :=
      hseg (1 - δ) ⟨by linarith, by linarith⟩
    exact hu_sub ⟨hball hmem_ball, hmem_Nm⟩

end Work.GATE.Segment
