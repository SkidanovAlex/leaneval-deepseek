import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Horn

open MandelDim

/-- If `E` is constant (`= c`) on a set `C` whose imaginary parts are unbounded below,
then `E w - w` cannot converge along the lower end `im → -∞`.

Mechanism: convergence of `E w - w` along `lowerEnd` gives a half-plane `{im w ≤ R}` on which
`dist (E w - w) cl < 1`; on `C` this reads `dist w (c - cl) < 1`, and two points of `C` deep in
that half-plane with imaginary parts differing by more than `4` would thus be at distance `< 2`,
contradiction. -/
theorem false_of_const_on_lower_unbounded {E : ℂ → ℂ} {C : Set ℂ} {c : ℂ}
    (hC : ∀ M : ℝ, ∃ w ∈ C, w.im < M)
    (hconst : ∀ w ∈ C, E w = c)
    (hE : ∃ cl : ℂ, Filter.Tendsto (fun w : ℂ => E w - w) MandelDim.lowerEnd (nhds cl)) : False := by
  obtain ⟨cl, hcl⟩ := hE
  -- Convergence along the lower end is uniform on a deep half-plane.
  have hmem : ∀ᶠ w : ℂ in MandelDim.lowerEnd, dist (E w - w) cl < 1 :=
    hcl.eventually (Metric.ball_mem_nhds cl one_pos)
  rw [MandelDim.lowerEnd, Filter.eventually_iff, Filter.mem_comap] at hmem
  obtain ⟨t, ht, hts⟩ := hmem
  rw [Filter.mem_atBot_sets] at ht
  obtain ⟨R, hR⟩ := ht
  -- On `C ∩ {im ≤ R}` the map is `w ↦ c - w`, so all these points lie in a ball of radius `1`.
  have key : ∀ w ∈ C, w.im ≤ R → dist w (c - cl) < 1 := by
    intro w hwC hwim
    have h1 : w.im ∈ t := hR w.im hwim
    have h2 : dist (E w - w) cl < 1 := hts h1
    rw [hconst w hwC] at h2
    have heq : dist (c - w) cl = dist w (c - cl) := by
      rw [dist_eq_norm, dist_eq_norm]
      have h3 : (c - w) - cl = -(w - (c - cl)) := by ring
      rw [h3, norm_neg]
    rwa [heq] at h2
  obtain ⟨w₁, hw₁C, hw₁im⟩ := hC R
  have hw₁le : w₁.im ≤ R := le_of_lt hw₁im
  obtain ⟨w₂, hw₂C, hw₂im⟩ := hC (w₁.im - 4)
  have hw₂le : w₂.im ≤ R := by linarith
  have d₁ := key w₁ hw₁C hw₁le
  have d₂ := key w₂ hw₂C hw₂le
  have hupper : dist w₁ w₂ < 2 := by
    have h := dist_triangle w₁ (c - cl) w₂
    have h' : dist (c - cl) w₂ < 1 := by rw [dist_comm]; exact d₂
    linarith
  have hlower : 4 < dist w₁ w₂ := by
    have h1 : |w₁.im - w₂.im| ≤ dist w₁ w₂ := by
      rw [dist_eq_norm, ← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    have h2 : (4 : ℝ) < |w₁.im - w₂.im| := by
      rw [abs_of_pos (by linarith : (0 : ℝ) < w₁.im - w₂.im)]
      linarith
    linarith
  linarith

end Work.Horn
