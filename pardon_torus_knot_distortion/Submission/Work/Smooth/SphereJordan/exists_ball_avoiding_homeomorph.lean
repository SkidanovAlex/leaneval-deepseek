import Mathlib
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.exists_ball_avoiding

namespace Work.Smooth.SphereJordan

open Set

/-- **Finitely many compact pieces of the disc, each avoiding the *pull-back* under a
homeomorphism `Θ` of the closed ball of radius `1/2`, avoid one common pull-back of a closed ball of
some radius `1/2 < r₀ < 1`.**  The point is that a homeomorphism of the disc cannot
collapse the complement of the ball of radius `1/2` onto its boundary: pushing the pieces forward
by `Θ` turns the hypothesis into "compact pieces avoiding the closed ball of radius `1/2`", to
which `exists_ball_avoiding` applies, and pulling the resulting radius back along `Θ` gives the
claim. -/
theorem exists_ball_avoiding_homeomorph (Θ : Work.Smooth.Jordan.Disc ≃ₜ Work.Smooth.Jordan.Disc) (ι : Type) [Fintype ι] (K : ι → Set Work.Smooth.Jordan.Disc) (hK : ∀ i, IsCompact (K i)) (hdisj : ∀ i, Disjoint (K i) (Θ ⁻¹' {x : Work.Smooth.Jordan.Disc | ‖((x : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤ 1 / 2})) : ∃ r₀ : ℝ, 1 / 2 < r₀ ∧ r₀ < 1 ∧ ∀ i, Disjoint (K i) (Θ ⁻¹' {x : Work.Smooth.Jordan.Disc | ‖((x : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤ r₀}) := by
  have hcmp : ∀ i, IsCompact (Θ '' K i) := fun i => (hK i).image Θ.continuous
  have hdisj' : ∀ i, Disjoint (Θ '' K i) {x : Work.Smooth.Jordan.Disc | ‖((x : Work.Smooth.Jordan.Disc) : ℂ)‖ ≤ 1 / 2} := by
    intro i
    rw [Set.disjoint_left]
    intro y hyK hyball
    obtain ⟨x, hxK, rfl⟩ := hyK
    exact (Set.disjoint_left.mp (hdisj i)) hxK hyball
  obtain ⟨r₀, h1, h2, h3⟩ := exists_ball_avoiding ι (fun i => Θ '' K i) hcmp hdisj'
  refine ⟨r₀, h1, h2, fun i => ?_⟩
  rw [Set.disjoint_left]
  intro x hxK hxball
  exact (Set.disjoint_left.mp (h3 i)) ⟨x, hxK, rfl⟩ hxball

end Work.Smooth.SphereJordan
