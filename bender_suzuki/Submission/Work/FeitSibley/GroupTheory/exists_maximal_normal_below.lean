import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Subgroup

namespace Work.FeitSibley.GroupTheory

theorem exists_maximal_normal_below {G : Type*} [Group G] [Fintype G] (H Q : Subgroup G)
    (hH : H ≤ Subgroup.normalizer (Q : Set G)) (hne : Q ≠ ⊥) :
    ∃ Q3 : Subgroup G, Q3 ≤ Q ∧ Q3 ≠ Q ∧ H ≤ Subgroup.normalizer (Q3 : Set G) ∧
      ∀ A : Subgroup G, Q3 ≤ A → A ≤ Q → H ≤ Subgroup.normalizer (A : Set G) →
        A = Q3 ∨ A = Q := by
  classical
  -- The collection of `H`-invariant subgroups of `Q`.
  let S : Set (Subgroup G) := {A | A ≤ Q ∧ H ≤ Subgroup.normalizer (A : Set G)}
  -- `⊥` is a proper `H`-invariant subgroup of `Q`, so `S \ {Q}` is nonempty.
  have hbot : (⊥ : Subgroup G) ∈ S := by
    simp only [S, Set.mem_ofPred_eq]
    refine ⟨bot_le, ?_⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr (by infer_instance)]
    exact le_top
  have hbot_ne : (⊥ : Subgroup G) ≠ Q := hne.symm
  have hneS : (S \ {Q}).Nonempty := ⟨⊥, hbot, by simpa using hbot_ne⟩
  -- A maximal element of `S \ {Q}` w.r.t. inclusion.
  obtain ⟨M, hM⟩ := (Set.finite_univ.subset (Set.subset_univ (S \ {Q}))).exists_maximal hneS
  have hMin : M ∈ S \ {Q} := hM.1
  have hMmax : ∀ ⦃y⦄, y ∈ S \ {Q} → M ≤ y → y ≤ M := hM.2
  rw [Set.mem_sdiff] at hMin
  have hMne : M ≠ Q := by simpa using hMin.2
  have hMS : M ∈ S := hMin.1
  simp only [S, Set.mem_ofPred_eq] at hMS
  obtain ⟨hMQ, hMN⟩ := hMS
  refine ⟨M, hMQ, hMne, hMN, ?_⟩
  intro A hMA hAQ hHA
  by_cases hAeq : A = Q
  · exact Or.inr hAeq
  · left
    have hA : A ∈ S \ {Q} := by
      refine ⟨?_, ?_⟩
      · simp only [S, Set.mem_ofPred_eq]; exact ⟨hAQ, hHA⟩
      · simpa using hAeq
    exact le_antisymm (hMmax hA hMA) hMA

end Work.FeitSibley.GroupTheory
