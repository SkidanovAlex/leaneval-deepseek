import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Minimals

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval
open FractionalExpectationThresholds

attribute [local instance] Classical.propDecidable

namespace Submission
namespace FET

universe u
variable {X : Type u} [Fintype X]

/-- Inclusion-minimal members of an increasing family. -/
def IsMinimalElem (𝓕 : Set (Set X)) (M : Set X) : Prop :=
  M ∈ 𝓕 ∧ ∀ ⦃S : Set X⦄, S ∈ 𝓕 → S ⊆ M → S = M

/-- A minimal member of `𝓕` (in the subtype order of `𝓕`) is minimal as a set. -/
private lemma minimalElem_of_isMin {𝓕 : Set (Set X)} {A : 𝓕} (hA : IsMin A) :
    IsMinimalElem 𝓕 (A : Set X) := by
  constructor
  · exact A.property
  · intro S hS₁ hS₂
    have hle : (⟨S, hS₁⟩ : 𝓕) ≤ A := hS₂
    have hge : A ≤ (⟨S, hS₁⟩ : 𝓕) := hA hle
    apply subset_antisymm
    · exact hS₂
    · change (A : Set X) ⊆ S
      exact hge

/-- A set-minimal member of `𝓕` is minimal in the subtype order of `𝓕`. -/
private lemma isMin_of_minimalElem {𝓕 : Set (Set X)} {M : Set X} (hM : IsMinimalElem 𝓕 M) :
    IsMin (⟨M, hM.1⟩ : 𝓕) := by
  intro B hBle
  have hBM : (B : Set X) ⊆ M := hBle
  have hEq : (B : Set X) = M := hM.2 B.property hBM
  change M ⊆ (B : Set X)
  rw [hEq]

/-- For a minimal member `A`, the inner supremum in `l` equals its cardinality. -/
private lemma inner_eq_of_isMin {𝓕 : Set (Set X)} {A : 𝓕} (hA : IsMin A) :
    (⨆ (_ : IsMin A), (A : Set X).ncard) = (A : Set X).ncard := by
  simp [hA]

/-- For a non-minimal member `A`, the inner supremum in `l` is `0`. -/
private lemma inner_eq_zero {𝓕 : Set (Set X)} {A : 𝓕} (hA : ¬ IsMin A) :
    (⨆ (_ : IsMin A), (A : Set X).ncard) = 0 := by
  simp [hA]

/-- A minimal member has size at most `l 𝓕`. -/
lemma ncard_le_l_of_minimal_elem {𝓕 : Set (Set X)} {M : Set X} (hM : IsMinimalElem 𝓕 M) :
    M.ncard ≤ l 𝓕 := by
  classical
  unfold l
  change M.ncard ≤ sSup (Set.range (fun A : 𝓕 => (⨆ (_ : IsMin A), (A : Set X).ncard)))
  have hbdd : BddAbove (Set.range (fun A : 𝓕 => (⨆ (_ : IsMin A), (A : Set X).ncard))) := by
    refine ⟨Nat.card X, ?_⟩
    rintro y hy
    rcases hy with ⟨A, rfl⟩
    have hle : (⨆ (_ : IsMin A), (A : Set X).ncard) ≤ (A : Set X).ncard := by
      by_cases hA : IsMin A
      · rw [inner_eq_of_isMin hA]
      · rw [inner_eq_zero hA]
        exact Nat.zero_le _
    exact le_trans hle (Set.ncard_le_card (s := (A : Set X)))
  have hmem : M.ncard ∈ Set.range (fun A : 𝓕 => (⨆ (_ : IsMin A), (A : Set X).ncard)) := by
    refine ⟨(⟨M, hM.1⟩ : 𝓕), ?_⟩
    have hIsMin : IsMin (⟨M, hM.1⟩ : 𝓕) := isMin_of_minimalElem hM
    change (⨆ (_ : IsMin (⟨M, hM.1⟩ : 𝓕)), ((⟨M, hM.1⟩ : 𝓕) : Set X).ncard) = M.ncard
    exact inner_eq_of_isMin hIsMin
  exact le_csSup hbdd hmem

/-- If every minimal member has size at most `1`, then `l 𝓕 ≤ 1`. -/
private lemma l_le_one_of_all_minimal_small {𝓕 : Set (Set X)}
    (hsmall : ∀ M : Set X, IsMinimalElem 𝓕 M → M.ncard ≤ 1) : l 𝓕 ≤ 1 := by
  classical
  by_cases h𝓕ne : 𝓕.Nonempty
  · unfold l
    change sSup (Set.range (fun A : 𝓕 => (⨆ (_ : IsMin A), (A : Set X).ncard))) ≤ 1
    apply csSup_le
    · rcases h𝓕ne with ⟨A₀, hA₀⟩
      refine ⟨(⨆ (_ : IsMin (⟨A₀, hA₀⟩ : 𝓕)), ((⟨A₀, hA₀⟩ : 𝓕) : Set X).ncard), ⟨(⟨A₀, hA₀⟩ : 𝓕), rfl⟩⟩
    · rintro n hn
      rcases hn with ⟨A, rfl⟩
      by_cases hA : IsMin A
      · have hMinEl : IsMinimalElem 𝓕 (A : Set X) := minimalElem_of_isMin hA
        have hncard : (A : Set X).ncard ≤ 1 := hsmall (A : Set X) hMinEl
        change (⨆ (_ : IsMin A), (A : Set X).ncard) ≤ 1
        rw [inner_eq_of_isMin hA]
        exact hncard
      · change (⨆ (_ : IsMin A), (A : Set X).ncard) ≤ 1
        rw [inner_eq_zero hA]
        norm_num
  · have h𝓕empty : 𝓕 = ∅ := Set.not_nonempty_iff_eq_empty.mp h𝓕ne
    rw [h𝓕empty]
    unfold l
    simp

/-- From `2 ≤ l 𝓕`, an increasing family is nonempty and contains a minimal element of size ≥ 2. -/
lemma exists_minimal_elem_ge_two {𝓕 : Set (Set X)} (h𝓕 : IsUpperSet 𝓕) (hl : 2 ≤ l 𝓕) :
    ∃ M : Set X, IsMinimalElem 𝓕 M ∧ 2 ≤ M.ncard := by
  classical
  by_cases h : ∃ M : Set X, IsMinimalElem 𝓕 M ∧ 2 ≤ M.ncard
  · rcases h with ⟨M, hM⟩
    exact ⟨M, hM⟩
  · have hsmall : ∀ M : Set X, IsMinimalElem 𝓕 M → M.ncard ≤ 1 := by
      intro M hM
      have hnot : ¬ 2 ≤ M.ncard := by
        intro h2
        exact h ⟨M, hM, h2⟩
      omega
    have hl1 : l 𝓕 ≤ 1 := l_le_one_of_all_minimal_small hsmall
    omega

end FET
end Submission
