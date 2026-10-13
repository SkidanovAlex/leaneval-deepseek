import Mathlib

namespace Work.WilE9G.Sard

theorem chartDiffBound {d t : ℕ} {γ : (Fin t → ℝ) → (Fin d → ℝ)} {base : Fin t → ℝ} {rad : ℝ}
    (hγOn : ContDiffOn ℝ 1 γ (Metric.closedBall base rad)) (hrad : 0 < rad)
    {u : Fin t → ℝ} (hu : u ∈ Metric.ball base rad) :
    ∃ L ρ : ℝ, 0 ≤ L ∧ 0 < ρ ∧ (∀ z, ‖z - u‖ ≤ ρ → DifferentiableAt ℝ γ z) ∧
      (∀ z, ‖z - u‖ ≤ ρ → ‖fderiv ℝ γ z‖ ≤ L) := by
  -- `u` lies in the open ball, so there is room to move.
  have hu' : ‖u - base‖ < rad := by
    rw [Metric.mem_ball, dist_eq_norm] at hu
    exact hu
  -- a small radius around `u` still stays inside the open ball
  set ρ : ℝ := (rad - ‖u - base‖) / 2 with hρ
  have hρpos : 0 < ρ := by
    rw [hρ]; linarith
  have hsub : Metric.closedBall u ρ ⊆ Metric.ball base rad := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_eq_norm]
    have hsplit : z - base = (z - u) + (u - base) := by abel
    calc ‖z - base‖ = ‖(z - u) + (u - base)‖ := by rw [hsplit]
      _ ≤ ‖z - u‖ + ‖u - base‖ := norm_add_le _ _
      _ ≤ ρ + ‖u - base‖ := by linarith
      _ < rad := by rw [hρ] at *; linarith
  -- γ is C¹ on the open ball as well
  have hγball : ContDiffOn ℝ 1 γ (Metric.ball base rad) := hγOn.mono Metric.ball_subset_closedBall
  have hdiffOn : DifferentiableOn ℝ γ (Metric.ball base rad) := hγball.differentiableOn_one
  have hdiff : ∀ z, ‖z - u‖ ≤ ρ → DifferentiableAt ℝ γ z := by
    intro z hz
    refine hdiffOn.differentiableAt (Metric.isOpen_ball.mem_nhds ?_)
    refine hsub ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hz
  -- the derivative is continuous on the compact ball, hence bounded there
  have hcont : ContinuousOn (fun z => ‖fderiv ℝ γ z‖) (Metric.closedBall u ρ) :=
    ((hγball.continuousOn_fderiv_of_isOpen Metric.isOpen_ball
      (le_refl (1 : WithTop ℕ∞))).mono hsub).norm
  have hbdd : Bornology.IsBounded ((fun z => ‖fderiv ℝ γ z‖) '' Metric.closedBall u ρ) :=
    (isCompact_closedBall u ρ).image_of_continuousOn hcont |>.isBounded
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hbdd
  refine ⟨max r 0, ρ, le_max_right _ _, hρpos, hdiff, ?_⟩
  intro z hz
  have hzK : z ∈ Metric.closedBall u ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hz
  have hmem := hr (Set.mem_image_of_mem (fun z => ‖fderiv ℝ γ z‖) hzK)
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs] at hmem
  exact le_trans (abs_le.mp hmem).2 (le_max_left r 0)

end Work.WilE9G.Sard
