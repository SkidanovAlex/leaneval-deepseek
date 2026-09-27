import Mathlib

namespace Work.EKLComp

/-- The topological Besicovitch covering theorem in one dimension, in the form needed for the
Einsiedler–Katok–Lindenstrauss argument: there is a fixed number `N` of families so that, from any
family of (open) balls with centers ranging over a set `A ⊆ ℝ` and with bounded radii, one can
select `N` subfamilies of pairwise disjoint **closed** balls whose open balls cover `A`.

This is a direct instance of Mathlib's `Besicovitch.exist_disjoint_covering_families` (the
topological Besicovitch covering theorem), together with the fact that finite-dimensional real
normed spaces carry the Besicovitch covering property (`HasBesicovitchCovering`). -/
theorem besicovitch_intervals : ∃ N : ℕ, 0 < N ∧ ∀ (A : Set ℝ) (r : A → ℝ),
    (∀ a, 0 < r a) → (∃ ρ : ℝ, ∀ a, r a ≤ ρ) →
    ∃ s : Fin N → Set A,
      (∀ i, (s i).PairwiseDisjoint fun a => Metric.closedBall (a : ℝ) (r a)) ∧
      A ⊆ ⋃ i, ⋃ a ∈ s i, Metric.ball (a : ℝ) (r a) := by
  classical
  -- `ℝ`, being a finite-dimensional real normed space, has the Besicovitch covering property.
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := ℝ)
  -- The constant `N` witnessing the property is positive: for `N = 0` the (inhabited) type of
  -- satellite configurations with a single point would be nonempty.
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      exact (hN.false (default : Besicovitch.SatelliteConfig ℝ 0 τ)).elim
    · exact h
  refine ⟨N, hNpos, ?_⟩
  intro A r hr hb
  obtain ⟨ρ, hρ⟩ := hb
  -- Package the given balls as a `BallPackage` over the index type `A`.
  let q : Besicovitch.BallPackage A ℝ :=
    { c := fun a => (a : ℝ), r := r, rpos := hr, r_bound := ρ, r_le := hρ }
  obtain ⟨s, hs, hcov⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  refine ⟨s, hs, ?_⟩
  have hrange : Set.range q.c = A := Subtype.range_coe
  rw [hrange] at hcov
  simpa only [q] using hcov

end Work.EKLComp
