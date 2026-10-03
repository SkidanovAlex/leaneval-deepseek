import Mathlib

namespace Work.PertCrux

/-- If `g z = u z - hF z` is continuous at `0` and is bounded by `η` on the punctured
ball `B(0,ρ) \ {0}`, then the same bound holds at `0` itself. -/
theorem norm_sub_zero_le_of_punctured {u hF : ℂ → ℂ} {η ρ : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousAt (fun z => u z - hF z) 0)
    (hb : ∀ z ∈ Metric.ball 0 ρ, z ≠ 0 → ‖u z - hF z‖ ≤ η) :
    ‖u 0 - hF 0‖ ≤ η := by
  have hnorm : ContinuousAt (fun z : ℂ => ‖u z - hF z‖) 0 := hcont.norm
  -- it suffices to prove the bound with an arbitrarily small positive slack `ε`
  apply le_of_forall_pos_le_add
  intro ε hε
  rw [Metric.continuousAt_iff] at hnorm
  obtain ⟨δ, hδpos, hδ⟩ := hnorm ε hε
  -- a punctured test point inside both the δ-ball and the ρ-ball
  set r : ℝ := min δ ρ / 2 with hrdef
  have hmin : 0 < min δ ρ := lt_min hδpos hρ
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrδ : r < δ := by
    rw [hrdef]; have := min_le_left δ ρ; linarith
  have hrρ : r < ρ := by
    rw [hrdef]; have := min_le_right δ ρ; linarith
  have hz0 : (r : ℂ) ≠ 0 := by simp [hrpos.ne']
  have hnormr : ‖(r : ℂ)‖ = r := by
    have := RCLike.norm_ofReal (K := ℂ) r
    rw [abs_of_pos hrpos] at this
    exact this
  have hmem : (r : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right, hnormr]; exact hrρ
  have hdist : dist (r : ℂ) 0 < δ := by
    rw [dist_zero_right, hnormr]; exact hrδ
  have hbd : ‖u (r : ℂ) - hF (r : ℂ)‖ ≤ η := hb _ hmem hz0
  have hcl : dist (‖u (r : ℂ) - hF (r : ℂ)‖) (‖u 0 - hF 0‖) < ε := hδ hdist
  rw [Real.dist_eq] at hcl
  have h2 := (abs_lt.mp hcl).1
  linarith

end Work.PertCrux
