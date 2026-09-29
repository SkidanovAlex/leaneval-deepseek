import Mathlib

namespace Work.TMComp.Kotani

/-- Joint continuity in `(z, x)` of `g z x` on `U × ℝ`, given a locally uniform
Lipschitz bound in the first variable `z` and continuity in the second variable `x`
for each fixed `z ∈ U`. -/
theorem continuousAt_prod_of_lipschitz_fst {U : Set ℂ} {g : ℂ → ℝ → ℂ}
    (hL : ∀ z₀ ∈ U, ∃ s : ℝ, 0 < s ∧ ∃ L : ℝ, 0 < L ∧
      ∀ x : ℝ, ∀ z ∈ Metric.ball z₀ s, ∀ w ∈ Metric.ball z₀ s,
        ‖g z x - g w x‖ ≤ L * ‖z - w‖)
    (hx : ∀ z ∈ U, ∀ x₀ : ℝ, ContinuousAt (fun x : ℝ => g z x) x₀) :
    ∀ z₀ ∈ U, ∀ x₀ : ℝ,
      ContinuousAt (fun p : ℂ × ℝ => g p.1 p.2) (z₀, x₀) := by
  intro z₀ hz₀ x₀
  obtain ⟨s, hs, L, hLpos, hLip⟩ := hL z₀ hz₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hcont : ContinuousAt (fun x : ℝ => g z₀ x) x₀ := hx z₀ hz₀ x₀
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ₂, _hδ₂pos, hδ₂⟩ := hcont (ε/2) (by linarith)
  refine ⟨min s (min δ₂ (ε/(2*L))), by positivity, ?_⟩
  intro p hp
  rw [Prod.dist_eq] at hp
  have hp1 : dist p.1 z₀ < s :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hp) (min_le_left _ _)
  have hp2 : dist p.2 x₀ < δ₂ :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hp)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hp1e : dist p.1 z₀ < ε/(2*L) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hp)
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have h1 : ‖g p.1 p.2 - g z₀ p.2‖ ≤ L * ‖p.1 - z₀‖ :=
    hLip p.2 p.1 (Metric.mem_ball.mpr hp1) z₀ (Metric.mem_ball_self hs)
  have h1lt : dist (g p.1 p.2) (g z₀ p.2) < ε/2 := by
    rw [dist_eq_norm]
    calc ‖g p.1 p.2 - g z₀ p.2‖ ≤ L * ‖p.1 - z₀‖ := h1
      _ = L * dist p.1 z₀ := by rw [dist_eq_norm]
      _ < L * (ε/(2*L)) := mul_lt_mul_of_pos_left hp1e hLpos
      _ = ε/2 := by field_simp
  have h2 : dist (g z₀ p.2) (g z₀ x₀) < ε/2 := hδ₂ hp2
  calc dist (g p.1 p.2) (g z₀ x₀)
      ≤ dist (g p.1 p.2) (g z₀ p.2) + dist (g z₀ p.2) (g z₀ x₀) := dist_triangle _ _ _
    _ < ε/2 + ε/2 := add_lt_add h1lt h2
    _ = ε := by ring

end Work.TMComp.Kotani
