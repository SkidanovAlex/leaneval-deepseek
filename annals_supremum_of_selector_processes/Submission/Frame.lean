import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps

/-!
# Framework: p-small families, monotone families, basic facts
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Frame

/-- Upward closure of a set of subsets -/
def up {X : Type*} (𝓕 : Set (Set X)) : Set (Set X) := {t | ∃ s ∈ 𝓕, s ⊆ t}

@[simp] lemma mem_up {X : Type*} {𝓕 : Set (Set X)} {t : Set X} :
    t ∈ up 𝓕 ↔ ∃ s ∈ 𝓕, s ⊆ t := Iff.rfl

lemma subset_up {X : Type*} {𝓕 : Set (Set X)} : 𝓕 ⊆ up 𝓕 := by
  intro s hs; exact ⟨s, hs, rfl.subset⟩

@[simp] lemma up_up {X : Type*} {𝓕 : Set (Set X)} : up (up 𝓕) = up 𝓕 := by
  ext t; constructor
  · rintro ⟨s, ⟨s', hs', h1⟩, h2⟩; exact ⟨s', hs', h1.trans h2⟩
  · intro h; exact ⟨t, h, rfl.subset⟩

lemma subset_up_of_subset {X : Type*} {𝓕 𝓖 : Set (Set X)} (h : 𝓕 ⊆ 𝓖) : up 𝓕 ⊆ up 𝓖 := by
  rintro t ⟨s, hs, hst⟩; exact ⟨s, h hs, hst⟩

/-- Upward closed (monotone) families -/
def MonotoneFamily {X : Type*} (𝓕 : Set (Set X)) : Prop := ∀ ⦃s t⦄, s ∈ 𝓕 → s ⊆ t → t ∈ 𝓕

lemma MonotoneFamily.self_subset_up {X : Type*} {𝓕 : Set (Set X)} (h𝓕 : MonotoneFamily 𝓕) :
    up 𝓕 ⊆ 𝓕 := by
  rintro t ⟨s, hs, hst⟩; exact h𝓕 hs hst

lemma MonotoneFamily.up_eq_self {X : Type*} {𝓕 : Set (Set X)} (h𝓕 : MonotoneFamily 𝓕) :
    up 𝓕 = 𝓕 :=
  le_antisymm h𝓕.self_subset_up subset_up

lemma IsSmall.mono_family {X : Type*} [Fintype X] (p : I) {𝓕 𝓖 : Set (Set X)}
    (h𝓕𝓖 : 𝓕 ⊆ 𝓖) (h𝓖 : IsSmall p 𝓖) : IsSmall p 𝓕 := by
  rcases h𝓖 with ⟨𝓒, hcov, hcost⟩
  exact ⟨𝓒, h𝓕𝓖.trans hcov, hcost⟩

lemma IsSmall.empty {X : Type*} [Fintype X] (p : I) : IsSmall p (∅ : Set (Set X)) := by
  refine ⟨∅, ?_, ?_⟩
  · intro s hs; simp at hs
  · simp

end Frame
end Submission
