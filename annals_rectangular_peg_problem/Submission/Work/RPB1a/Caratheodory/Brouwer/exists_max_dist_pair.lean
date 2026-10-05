import Mathlib

namespace Work.RPB1a.Caratheodory.Brouwer

open Set

/-- For a continuous injective `γ : Circle → ℂ` there are two **distinct** points `p`, `q` of
`range γ` at maximum distance: every pair of points of `range γ` is at distance at most `‖p - q‖`.
Compactness of `Circle` gives the maximum; injectivity of `γ` together with the fact that `Circle`
has at least two elements gives `p ≠ q`. -/
theorem exists_max_dist_pair (γ : Circle → ℂ) (hγ : Continuous γ)
    (hinj : Function.Injective γ) :
    ∃ p ∈ Set.range γ, ∃ q ∈ Set.range γ, p ≠ q ∧
      ∀ z ∈ Set.range γ, ∀ w ∈ Set.range γ, ‖z - w‖ ≤ ‖p - q‖ := by
  -- The distance function on `Circle × Circle` is continuous and the domain is compact, so it
  -- attains a maximum at some pair `(a, b)`.
  have hcont : Continuous fun x : Circle × Circle => ‖γ x.1 - γ x.2‖ :=
    ((hγ.comp continuous_fst).sub (hγ.comp continuous_snd)).norm
  obtain ⟨⟨a, b⟩, -, hmax⟩ :=
    isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hcont.continuousOn
  have hmax' : ∀ y : Circle × Circle, ‖γ y.1 - γ y.2‖ ≤ ‖γ a - γ b‖ := fun y => hmax trivial
  refine ⟨γ a, ⟨a, rfl⟩, γ b, ⟨b, rfl⟩, ?_, ?_⟩
  · -- `1` and `-1` are distinct points of `Circle`, so their images under the injective `γ`
    -- are at positive distance; a maximising pair therefore cannot have distance `0`.
    intro hpq
    have h0 : ‖γ a - γ b‖ = 0 := by rw [hpq, sub_self, norm_zero]
    have hne : γ ((1 : Circle)) ≠ γ ((-1 : Circle)) := fun h =>
      Circle.neg_ne_self (1 : Circle) (hinj h).symm
    have hle : ‖γ ((1 : Circle)) - γ ((-1 : Circle))‖ ≤ ‖γ a - γ b‖ :=
      hmax' ((1 : Circle), (-1 : Circle))
    rw [h0] at hle
    refine hne (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))))
  · rintro z ⟨u, rfl⟩ w ⟨v, rfl⟩
    exact hmax' (u, v)

end Work.RPB1a.Caratheodory.Brouwer
