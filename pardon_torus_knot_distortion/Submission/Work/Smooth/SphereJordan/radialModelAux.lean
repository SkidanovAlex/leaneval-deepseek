import Mathlib

/-!
# Local radial model (local copy)

The local radial model of a finite union of equal closed discs at a frontier point: a *copy* of
`Work.Smooth.SphereJordan.localRadialModel` from
`Submission/Work/Smooth/SphereJordan/locallyArcFrontierUnboundedComponent.lean`, renamed
(`localRadialModelAux`) so that this module and everything below it builds without depending on
that file.

At `x ∈ frontier (⋃ w ∈ Q, closedBall w r)` there is `ε > 0` such that for `0 < ρ < ε` and
`‖u‖ = 1`, the point `x + ρ * u` lies in the union of the closed balls iff some centre `w ∈ Q`
with `dist x w = r` satisfies `ρ ≤ 2 * (star u * (w - x)).re`.
-/

namespace Work.Smooth.SphereJordan

open Set Metric

noncomputable section

theorem isClosed_ballUAux (Q : Finset ℂ) (r : ℝ) :
    IsClosed (⋃ w ∈ Q, Metric.closedBall w r) :=
  isClosed_biUnion_finset fun w _ => Metric.isClosed_closedBall

/-- **The local radial model of a finite union of equal closed discs at a frontier point.** -/
theorem localRadialModelAux {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {x : ℂ}
    (hx : x ∈ frontier (⋃ w ∈ Q, Metric.closedBall w r)) :
    ∃ ε > 0, ∀ (u : ℂ) (ρ : ℝ), ‖u‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔
        ∃ w ∈ Q, dist x w = r ∧ ρ ≤ 2 * (star u * (w - x)).re) := by
  have hSclosed : IsClosed (⋃ w ∈ Q, Metric.closedBall w r) := isClosed_ballUAux Q r
  have hxS : x ∈ ⋃ w ∈ Q, Metric.closedBall w r := hSclosed.closure_eq ▸ hx.1
  have hxint : x ∉ interior (⋃ w ∈ Q, Metric.closedBall w r) := hx.2
  have hge : ∀ w ∈ Q, r ≤ dist x w := by
    intro w hw
    by_contra hlt
    rw [not_le] at hlt
    have hxball : x ∈ Metric.ball w r := by rw [Metric.mem_ball]; exact hlt
    exact hxint (interior_mono (fun y hy => Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩)
      (Metric.ball_subset_interior_closedBall hxball))
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ w ∈ Q, r < dist x w → r + δ ≤ dist x w := by
    rcases (Q.filter fun w => r < dist x w).eq_empty_or_nonempty with h | hne
    · exact ⟨1, one_pos, fun w hw hlt =>
        absurd (h ▸ Finset.mem_filter.mpr ⟨hw, hlt⟩) (by simp)⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := Finset.exists_min_image (Q.filter fun w => r < dist x w)
        (fun w => dist x w) hne
      have hlt₀ : r < dist x w₀ := (Finset.mem_filter.mp hw₀).2
      refine ⟨dist x w₀ - r, by linarith, fun w hw hlt => ?_⟩
      have : w ∈ Q.filter (fun w => r < dist x w) := Finset.mem_filter.mpr ⟨hw, hlt⟩
      have := hmin w this
      linarith
  refine ⟨δ, hδpos, fun u ρ hu hρ hρδ => ?_⟩
  have hquad : ∀ w ∈ Q, dist x w = r →
      ‖x + ρ * u - w‖ ^ 2 = r ^ 2 - 2 * ρ * (star u * (w - x)).re + ρ ^ 2 := by
    intro w hw hwx
    have hnorm : ‖x - w‖ = r := by rw [← dist_eq_norm]; exact hwx
    have hinner : inner ℝ (x - w) u = - (star u * (w - x)).re := by
      rw [real_inner_comm, Complex.inner]
      simp only [starRingEnd_apply]
      have h2 : (x - w) * star u = -(star u * (w - x)) := by ring
      rw [h2]; simp
    have hu1 : ‖(((ρ:ℝ):ℂ) * u)‖ = ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, hu, mul_one]
    have h1 : x + ρ * u - w = (x - w) + ρ * u := by ring
    rw [h1, norm_add_sq_real, hnorm, hu1,
        show inner ℝ (x - w) (((ρ:ℝ):ℂ) * u) = ρ * inner ℝ (x - w) u from by
          rw [show ((ρ:ℝ):ℂ) * u = ρ • u from rfl, real_inner_smul_right],
        hinner]
    ring
  have hdist : dist x (x + ρ * u) = ρ := by
    rw [dist_eq_norm]
    rw [show x - (x + ρ * u) = -(((ρ:ℝ):ℂ) * u) by ring]
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, hu, mul_one]
  constructor
  · intro hmem
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hmem
    have hwle : dist x w ≤ r := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : r + δ ≤ dist x w := hδ w hw hcon
      have h2 : dist (x + ρ * u) w ≤ r := Metric.mem_closedBall.mp hxw
      have h3 : dist x w ≤ dist x (x + ρ * u) + dist (x + ρ * u) w := dist_triangle _ _ _
      rw [hdist] at h3
      linarith
    have hwx : dist x w = r := le_antisymm hwle (hge w hw)
    exact ⟨w, hw, hwx, by
      have hle : dist (x + ρ * u) w ≤ r := Metric.mem_closedBall.mp hxw
      rw [dist_eq_norm] at hle
      have hq := hquad w hw hwx
      have h2 : ‖x + ρ * u - w‖ ^ 2 ≤ r ^ 2 := by
        nlinarith [hle, norm_nonneg (x + ρ * u - w), hr.le]
      nlinarith [hq, h2, hρ]⟩
  · rintro ⟨w, hw, hwx, hineq⟩
    refine Set.mem_iUnion₂.mpr ⟨w, hw, Metric.mem_closedBall.mpr ?_⟩
    rw [dist_eq_norm]
    have hq := hquad w hw hwx
    nlinarith [hq, hρ, hineq, norm_nonneg (x + ρ * u - w)]

end

end Work.Smooth.SphereJordan
