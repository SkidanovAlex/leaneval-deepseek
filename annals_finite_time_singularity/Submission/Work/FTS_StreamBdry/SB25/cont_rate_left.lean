import Mathlib.Topology.MetricSpace.Pseudo.Constructions

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25

theorem cont_rate_left {f : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {a b K : ℝ} (hab : a < b) (hK : 0 ≤ K)
    (hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo a b))
    (hrate : ∀ z θ, 0 < z → θ ∈ Set.Ioo a b → |f z θ - g z| ≤ K * (θ - a)) :
    ContinuousOn g (Set.Ioi 0) := by
  rw [Metric.continuousOn_iff]
  intro z₀ hz₀ ε hε
  -- a small offset into the interval `(a, b)`, controlled by `ε / 4`
  set m : ℝ := min ((b - a) / 2) (ε / (4 * (K + 1))) with hm
  have hm_pos : 0 < m := by
    rw [hm]
    exact lt_min (by linarith) (div_pos hε (by linarith))
  set θ : ℝ := a + m with hθ
  have haθ : a < θ := by rw [hθ]; linarith
  have hθb : θ < b := by
    rw [hθ]
    have : m ≤ (b - a) / 2 := by rw [hm]; exact min_le_left _ _
    linarith
  have hθmem : θ ∈ Set.Ioo a b := ⟨haθ, hθb⟩
  have hKm_aux : K * (ε / (4 * (K + 1))) < ε / 4 := by
    rw [← mul_div_assoc]
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 4 * (K + 1))]
    nlinarith
  have hKm : K * m < ε / 4 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by rw [hm]; exact min_le_right _ _) hK) hKm_aux
  have hθa_eq : θ - a = m := by rw [hθ]; ring
  have hKmθ : K * (θ - a) < ε / 4 := by rw [hθa_eq]; exact hKm
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.continuousOn_iff.mp hcont) (z₀, θ) ⟨hz₀, hθmem⟩ (ε / 2) (by linarith)
  refine ⟨δ, hδpos, ?_⟩
  intro z hz hdz
  have hdist : dist (z, θ) (z₀, θ) < δ := by
    rw [Prod.dist_eq, dist_self]
    exact max_lt hdz hδpos
  have h2raw : dist (Function.uncurry f (z, θ)) (Function.uncurry f (z₀, θ)) < ε / 2 :=
    hδ (a := (z, θ)) ⟨hz, hθmem⟩ hdist
  have h2 : |f z θ - f z₀ θ| < ε / 2 := by
    simpa [Function.uncurry, Real.dist_eq] using h2raw
  have h1 : |g z - f z θ| ≤ K * (θ - a) := by
    rw [abs_sub_comm]; exact hrate z θ hz hθmem
  have h3 : |f z₀ θ - g z₀| ≤ K * (θ - a) := hrate z₀ θ hz₀ hθmem
  have htri : |g z - g z₀| ≤ |g z - f z θ| + |f z θ - f z₀ θ| + |f z₀ θ - g z₀| := by
    have heq : g z - g z₀ = (g z - f z θ) + (f z θ - f z₀ θ) + (f z₀ θ - g z₀) := by ring
    rw [heq]
    exact abs_add_three _ _ _
  rw [Real.dist_eq]
  linarith

end Work.FTS_StreamBdry.SB25
