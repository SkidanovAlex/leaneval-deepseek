import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- A finite set is `R₀`-independent if no two of its distinct elements are
`R₀`-related. -/
private def IsIndep {ι : Type*} (R₀ : ι → ι → Prop) (A : Finset ι) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ¬ R₀ i j

/-- Given that every set of size at least `K` contains a pair of distinct elements
related by `R₀`, and that `R` contains both orientations of `R₀` (and is reflexive),
there is a set of size at most `K` that `R`-covers every element. -/
theorem cover_of_max_unrelated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R₀ R : ι → ι → Prop) (K : ℕ)
    (hmono : ∀ i j, R₀ i j → R i j)
    (hsymm : ∀ i j, R₀ j i → R i j)
    (hrefl : ∀ i, R i i)
    (hpair : ∀ A : Finset ι, K ≤ A.card → ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ R₀ i j) :
    ∃ A : Finset ι, A.card ≤ K ∧ ∀ i, ∃ j ∈ A, R i j := by
  classical
  -- The collection of independent subsets of the whole type is nonempty and finite;
  -- pick one of maximum cardinality.
  have hne : (Finset.univ.powerset.filter (IsIndep R₀)).Nonempty :=
    ⟨∅, by simp [IsIndep]⟩
  obtain ⟨A, hAmem, hAmax⟩ :=
    Finset.exists_max_image (Finset.univ.powerset.filter (IsIndep R₀)) Finset.card hne
  have hAind : IsIndep R₀ A := (Finset.mem_filter.mp hAmem).2
  -- `hpair` makes `A` small.
  have hcard_le : A.card ≤ K := by
    by_contra h
    have hK : K ≤ A.card := by omega
    obtain ⟨i, hiA, j, hjA, hij, hR0⟩ := hpair A hK
    exact hAind i hiA j hjA hij hR0
  refine ⟨A, hcard_le, fun i => ?_⟩
  by_cases hi : i ∈ A
  · exact ⟨i, hi, hrefl i⟩
  · -- Maximality of `A`: if `i` were not `R`-covered by `A`, then `A ∪ {i}` would
    -- be a larger independent set.
    by_contra hcon
    have hforall : ∀ j ∈ A, ¬ R i j := fun j hjA hR => hcon ⟨j, hjA, hR⟩
    have hind : IsIndep R₀ (A ∪ {i}) := by
      intro p hp q hq hpq hR0
      simp only [Finset.mem_union, Finset.mem_singleton] at hp hq
      rcases hp with hpA | hpi
      · rcases hq with hqA | hqi
        · exact hAind p hpA q hqA hpq hR0
        · rw [hqi] at hR0
          exact hforall p hpA (hsymm i p hR0)
      · rcases hq with hqA | hqi
        · rw [hpi] at hR0
          exact hforall q hqA (hmono i q hR0)
        · exact absurd (hpi.trans hqi.symm) hpq
    have hmem' : A ∪ {i} ∈ Finset.univ.powerset.filter (IsIndep R₀) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ _, hind⟩
    have hle := hAmax (A ∪ {i}) hmem'
    have hcard : (A ∪ {i}).card = A.card + 1 := by
      rw [Finset.union_singleton, Finset.card_insert_of_notMem hi]
    omega

end Work.BMF.SD
