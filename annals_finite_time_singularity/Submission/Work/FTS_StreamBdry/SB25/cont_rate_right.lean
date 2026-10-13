import Mathlib.Analysis.Normed.Order.Lattice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25

theorem cont_rate_right {f : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {a b K : ℝ} (hab : a < b) (hK : 0 ≤ K)
    (hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo a b))
    (hrate : ∀ z θ, 0 < z → θ ∈ Set.Ioo a b → |f z θ - g z| ≤ K * (b - θ)) :
    ContinuousOn g (Set.Ioi 0) := by
  -- `g` is the uniform (in `z`) limit of the slices `θ ↦ f z θ` as `θ → b⁻`, by `hrate`;
  -- joint continuity of `f` turns that into continuity of `g`.
  intro z₀ hz₀
  have hz0 : (0:ℝ) < z₀ := hz₀
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- pick `θ := b - δt` close enough to `b` that the rate estimate is `< ε/3`
  set δt : ℝ := min ((b - a) / 2) (ε / (3 * (K + 1))) with hδtdef
  have hδtpos : 0 < δt := by
    rw [hδtdef]
    exact lt_min (by linarith) (div_pos hε (by linarith))
  have hθa : a < b - δt := by
    have hle : δt ≤ (b - a) / 2 := by rw [hδtdef]; exact min_le_left _ _
    linarith
  have hθb : b - δt < b := by linarith
  have hθmem : b - δt ∈ Set.Ioo a b := ⟨hθa, hθb⟩
  have hKδ : K * δt < ε / 3 := by
    have hle : δt ≤ ε / (3 * (K + 1)) := by rw [hδtdef]; exact min_le_right _ _
    have h1 : K * δt ≤ K * (ε / (3 * (K + 1))) := mul_le_mul_of_nonneg_left hle hK
    have h2 : K * (ε / (3 * (K + 1))) < ε / 3 := by
      have h3 : (0:ℝ) < 3 * (K + 1) := by linarith
      rw [← mul_div_assoc, div_lt_div_iff₀ h3 (by norm_num : (0:ℝ) < 3)]
      ring_nf
      nlinarith
    linarith
  -- joint continuity of `f` at `(z₀, b - δt)`
  have hnhds : Set.Ioi (0:ℝ) ×ˢ Set.Ioo a b ∈ nhds (z₀, b - δt) :=
    (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz0, hθmem⟩
  have hcat : ContinuousAt (Function.uncurry f) (z₀, b - δt) := hcont.continuousAt hnhds
  rw [Metric.continuousAt_iff] at hcat
  obtain ⟨δ', hδ'pos, hδ'⟩ := hcat (ε / 3) (by linarith)
  refine ⟨min δ' (z₀ / 2), lt_min hδ'pos (by linarith), ?_⟩
  intro y hy
  have hyδ' : dist y z₀ < δ' := lt_of_lt_of_le hy (min_le_left _ _)
  have hyz : dist y z₀ < z₀ / 2 := lt_of_lt_of_le hy (min_le_right _ _)
  -- staying within `z₀/2` keeps `y > 0`, so that `hrate` applies at `y`
  have hypos : 0 < y := by
    rw [Real.dist_eq] at hyz
    have h1 : -(z₀ / 2) < y - z₀ := (abs_lt.mp hyz).1
    linarith
  have hmid : dist (f y (b - δt)) (f z₀ (b - δt)) < ε / 3 := by
    have h := hδ' (show dist (y, b - δt) (z₀, b - δt) < δ' from by
      rw [dist_prod_same_right]; exact hyδ')
    simpa using h
  have hy1 : |g y - f y (b - δt)| < ε / 3 := by
    rw [abs_sub_comm]
    exact lt_of_le_of_lt (show |f y (b - δt) - g y| ≤ K * (b - (b - δt)) from
      hrate y (b - δt) hypos hθmem) (by linarith)
  have hy2 : |f z₀ (b - δt) - g z₀| < ε / 3 := by
    exact lt_of_le_of_lt (hrate z₀ (b - δt) hz0 hθmem) (by linarith)
  rw [Real.dist_eq]
  calc |g y - g z₀|
      = |(g y - f y (b - δt)) + (f y (b - δt) - f z₀ (b - δt)) + (f z₀ (b - δt) - g z₀)| := by
        ring_nf
    _ ≤ |g y - f y (b - δt)| + |f y (b - δt) - f z₀ (b - δt)| + |f z₀ (b - δt) - g z₀| := by
        have h1 := abs_add_le ((g y - f y (b - δt)) + (f y (b - δt) - f z₀ (b - δt)))
          (f z₀ (b - δt) - g z₀)
        have h2 := abs_add_le (g y - f y (b - δt)) (f y (b - δt) - f z₀ (b - δt))
        linarith
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [Real.dist_eq] at hmid
        linarith
    _ = ε := by ring

end Work.FTS_StreamBdry.SB25
