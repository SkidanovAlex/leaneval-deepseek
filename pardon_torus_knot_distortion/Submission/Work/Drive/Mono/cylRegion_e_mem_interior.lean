import Mathlib
import Submission.Work.Drive.Mono.CylRegionDefs

namespace Work.Drive.Mono

open Set

/-- The unit circle of `ℂ`, transported to the closed unit disc, is exactly the set of points
of the closed disc at distance `1` from the origin. -/
theorem mem_range_circlePoint_iff {z : Metric.closedBall (0 : ℂ) 1} :
    z ∈ Set.range (Work.CoreTopology.circlePoint) ↔ ‖(z : ℂ)‖ = 1 := by
  constructor
  · rintro ⟨θ, rfl⟩
    simp [Work.CoreTopology.circlePoint_coe]
  · intro hz
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (z : ℂ)).mp hz
    exact ⟨θ, Subtype.ext (by simpa [Work.CoreTopology.circlePoint_coe] using hθ)⟩

open Work.Drive.Mono in
theorem cylRegion_e_mem_interior {S : Set (EuclideanSpace ℝ (Fin 2))}
    {e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2))}
    (he_inj : Function.Injective e) (he_range : Set.range e = S)
    (he_bdry : Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier S)
    (z : Metric.closedBall (0 : ℂ) 1) :
    e z ∈ interior S ↔ ‖(z : ℂ)‖ < 1 := by
  -- `e z` always lies in `S`, and it is on the boundary of `S` exactly when `z` is on the
  -- unit circle; the rest is the elementary description of the interior of a set
  -- (`s \ frontier s = interior s`).
  have hzS : e z ∈ S := by
    rw [← he_range]
    exact Set.mem_range_self z
  have hbdry : e z ∈ frontier S ↔ ‖(z : ℂ)‖ = 1 := by
    have h1 : e z ∈ frontier S ↔ z ∈ Set.range (Work.CoreTopology.circlePoint) := by
      rw [← he_bdry, Set.mem_range]
      constructor
      · rintro ⟨θ, hθ⟩
        exact ⟨θ, he_inj hθ⟩
      · rintro ⟨θ, hθ⟩
        exact ⟨θ, congrArg e hθ⟩
    rw [h1, mem_range_circlePoint_iff]
  have hzle : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  rw [mem_interior_iff_notMem_frontier hzS, hbdry]
  exact ⟨fun hne => lt_of_le_of_ne hzle hne, fun hlt => ne_of_lt hlt⟩

end Work.Drive.Mono
