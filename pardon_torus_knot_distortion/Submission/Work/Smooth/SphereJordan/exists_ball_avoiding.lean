import Mathlib
import Submission.Work.Smooth.Jordan.Defs

namespace Work.Smooth.SphereJordan

open Set

/-- **A compact subset of the disc avoiding the closed ball of radius `1/2` stays away from some
strictly larger closed ball.**  The quantity `‖·‖` is continuous, so on a nonempty compact `K` it
attains its minimum, and that minimum is `> 1/2` because `K` misses the closed ball of radius
`1/2`; the closed ball of the intermediate radius `(min + 1/2)/2` is then disjoint from `K`.
The empty case is trivial. -/
theorem exists_radius_of_isCompact (K : Set Work.Smooth.Jordan.Disc) (hK : IsCompact K)
    (hdisj : Disjoint K {x : Work.Smooth.Jordan.Disc | ‖((x : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤ 1 / 2}) :
    ∃ r : ℝ, 1 / 2 < r ∧ r < 1 ∧
      Disjoint K {x : Work.Smooth.Jordan.Disc | ‖((x : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤ r} := by
  rcases eq_empty_or_nonempty K with hK0 | hne
  · refine ⟨3 / 4, by norm_num, by norm_num, ?_⟩
    rw [hK0]
    exact disjoint_bot_left
  · have hcont : ContinuousOn (fun x : Work.Smooth.Jordan.Disc =>
        ‖((x : Work.Smooth.Jordan.Disc) : ℂ)‖) K :=
      (continuous_norm.comp continuous_subtype_val).continuousOn
    obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hne hcont
    have hx₀gt : 1 / 2 < ‖((x₀ : Work.Smooth.Jordan.Disc) : ℂ)‖ :=
      not_le.mp ((Set.disjoint_left.mp hdisj) hx₀K)
    have hx₀le : ‖((x₀ : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤ 1 := by
      have h := x₀.2
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h
    refine ⟨(‖((x₀ : Work.Smooth.Jordan.Disc) : ℂ)‖ + 1 / 2) / 2, by linarith, by linarith, ?_⟩
    rw [Set.disjoint_left]
    intro x hxK hxball
    have hxball' : ‖((x : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤
        (‖((x₀ : Work.Smooth.Jordan.Disc) : ℂ)‖ + 1 / 2) / 2 := hxball
    have hge : ‖((x₀ : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤
        ‖((x : Work.Smooth.Jordan.Disc) : ℂ)‖ := hmin hxK
    linarith

/-- **Finitely many compact pieces of the disc, each avoiding the closed ball of radius `1/2`,
avoid one common closed ball of some radius `1/2 < r₀ < 1`.**  Since the index type is finite the
union is again compact and avoids the closed ball of radius `1/2`, so it suffices to apply the
single-piece statement to the union. -/
theorem exists_ball_avoiding (ι : Type) [Fintype ι] (K : ι → Set Work.Smooth.Jordan.Disc) (hK : ∀ i, IsCompact (K i)) (hdisj : ∀ i, Disjoint (K i) {x : Work.Smooth.Jordan.Disc | ‖((x : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤ 1 / 2}) : ∃ r₀ : ℝ, 1 / 2 < r₀ ∧ r₀ < 1 ∧ ∀ i, Disjoint (K i) {x : Work.Smooth.Jordan.Disc | ‖((x : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤ r₀} := by
  have hUc : IsCompact (⋃ i, K i) := isCompact_iUnion hK
  have hUd : Disjoint (⋃ i, K i)
      {x : Work.Smooth.Jordan.Disc | ‖((x : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤ 1 / 2} := by
    rw [Set.disjoint_left]
    intro x hx hxball
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact (Set.disjoint_left.mp (hdisj i)) hxi hxball
  obtain ⟨r₀, h1, h2, h3⟩ := exists_radius_of_isCompact (⋃ i, K i) hUc hUd
  exact ⟨r₀, h1, h2, fun i => h3.mono_left (fun x hx => Set.mem_iUnion.mpr ⟨i, hx⟩)⟩

end Work.Smooth.SphereJordan
