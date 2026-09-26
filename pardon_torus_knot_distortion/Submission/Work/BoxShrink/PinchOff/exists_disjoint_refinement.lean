import Mathlib

/-!
# Existence of a disjoint refinement for a family of nested/overlapping sets

This file proves the purely combinatorial lemma
`Work.BoxShrink.PinchOff.exists_disjoint_refinement`.

Given a finite family `{c a}` of sets together with "inner" sets `i a ⊆ c a`,
such that for every pair `a ≠ b` of the family either `c a` and `c b` are
disjoint, or one of the `c`'s is contained in the other's inner set, or the two
inner sets coincide, there is a subfamily `L'` whose `c`'s are pairwise disjoint
and whose inner sets `i` still cover all the original inner sets.

The construction: take the `i`-values that are maximal (under inclusion) among
the family, and keep one representative per distinct maximal value.  Distinct
maximal values are incomparable, and incomparable `i`-values force the
corresponding `c`'s to be disjoint; every `i`-value is contained in some maximal
one, which gives the covering property.
-/

namespace Work.BoxShrink.PinchOff

/-- Among the values of a finite family of sets there is an inclusion-maximal one. -/
theorem finset_exists_maximal_value {α X : Type*} (S : Finset α) (i : α → Set X)
    (hS : S.Nonempty) :
    ∃ t ∈ S, ∀ b ∈ S, i t ⊆ i b → i b ⊆ i t := by
  classical
  obtain ⟨t, htS, htmin⟩ :=
    Finset.exists_min_image S
      (fun a => (S.filter (fun c => i a ⊆ i c ∧ ¬ i c ⊆ i a)).card) hS
  refine ⟨t, htS, ?_⟩
  intro b hbS htb
  by_contra hnot
  have hssub : (S.filter (fun c => i b ⊆ i c ∧ ¬ i c ⊆ i b)) ⊂
      (S.filter (fun c => i t ⊆ i c ∧ ¬ i c ⊆ i t)) := by
    rw [Finset.ssubset_def]
    constructor
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      obtain ⟨hcS, hbc, hncb⟩ := hc
      exact ⟨hcS, htb.trans hbc, fun hct => hncb (hct.trans htb)⟩
    · intro hsub
      have hb : b ∈ S.filter (fun c => i t ⊆ i c ∧ ¬ i c ⊆ i t) := by
        rw [Finset.mem_filter]; exact ⟨hbS, htb, hnot⟩
      have hmem := (Finset.mem_filter.mp (hsub hb)).2
      exact hmem.2 Set.Subset.rfl
  have hlt := Finset.card_lt_card hssub
  have hle := htmin b hbS
  omega

/-- Every member of a finite family is contained in a member whose value is maximal. -/
theorem finset_exists_maximal_above {α X : Type*} (S : Finset α) (i : α → Set X)
    {a : α} (ha : a ∈ S) :
    ∃ t ∈ S, i a ⊆ i t ∧ ∀ b ∈ S, i t ⊆ i b → i b ⊆ i t := by
  classical
  have hU : (S.filter (fun b => i a ⊆ i b)).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha, Set.Subset.rfl⟩⟩
  obtain ⟨t, htU, htmax⟩ := finset_exists_maximal_value (S.filter (fun b => i a ⊆ i b)) i hU
  rw [Finset.mem_filter] at htU
  obtain ⟨htS, hat⟩ := htU
  refine ⟨t, htS, hat, ?_⟩
  intro b hbS hitb
  exact htmax b (Finset.mem_filter.mpr ⟨hbS, hat.trans hitb⟩) hitb

/-- Finset version of the combinatorial refinement lemma. -/
theorem exists_disjoint_refinement_finset {α X : Type*} (S : Finset α) (c i : α → Set X)
    (hci : ∀ a ∈ S, i a ⊆ c a)
    (hl : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      Disjoint (c a) (c b) ∨ c a ⊆ i b ∨ c b ⊆ i a ∨ i a = i b) :
    ∃ T : Finset α, T ⊆ S ∧ (∀ a ∈ T, ∀ b ∈ T, a ≠ b → Disjoint (c a) (c b)) ∧
      (∀ a ∈ S, ∃ b ∈ T, i a ⊆ i b) := by
  classical
  -- Two members with incomparable inner sets must have disjoint outer sets.
  have incomparable : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ (i a ⊆ i b) → ¬ (i b ⊆ i a) →
      Disjoint (c a) (c b) := by
    intro a ha b hb hab h1 h2
    rcases hl a ha b hb hab with hd | hsub | hsub | heq
    · exact hd
    · exact absurd ((hci a ha).trans hsub) h1
    · exact absurd ((hci b hb).trans hsub) h2
    · exact absurd (le_of_eq heq) h1
  by_cases hSne : S.Nonempty
  · -- The interesting case: `S` is nonempty.
    set M : Finset α := S.filter (fun a => ∀ b ∈ S, i a ⊆ i b → i b ⊆ i a) with hM
    have M_sub : M ⊆ S := by rw [hM]; exact Finset.filter_subset _ _
    have M_spec : ∀ a ∈ M, ∀ b ∈ S, i a ⊆ i b → i b ⊆ i a := by
      intro a ha b hb h
      rw [hM] at ha
      exact (Finset.mem_filter.mp ha).2 b hb h
    have exists_max : ∀ a ∈ S, ∃ t ∈ M, i a ⊆ i t := by
      intro a ha
      obtain ⟨t, htS, hat, htmax⟩ := finset_exists_maximal_above S i ha
      exact ⟨t, by rw [hM, Finset.mem_filter]; exact ⟨htS, htmax⟩, hat⟩
    let x0 : α := Classical.choose hSne
    set rep : Set X → α :=
      fun v => if h : ∃ b ∈ M, i b = v then Classical.choose h else x0 with hrep
    have rep_spec : ∀ v ∈ M.image i, rep v ∈ M ∧ i (rep v) = v := by
      intro v hv
      have h : ∃ b ∈ M, i b = v := Finset.mem_image.mp hv
      have hrepv : rep v = Classical.choose h := by
        rw [hrep]; exact dif_pos h
      rw [hrepv]; exact Classical.choose_spec h
    set T : Finset α := (M.image i).image rep with hT
    have T_mem : ∀ a, a ∈ T ↔ ∃ v ∈ M.image i, rep v = a := by
      intro a; rw [hT, Finset.mem_image]
    have T_sub_S : T ⊆ S := by
      intro a ha
      rw [T_mem] at ha
      obtain ⟨v, hv, rfl⟩ := ha
      exact M_sub (rep_spec v hv).1
    have T_in_M : ∀ a ∈ T, a ∈ M := by
      intro a ha
      rw [T_mem] at ha
      obtain ⟨v, hv, rfl⟩ := ha
      exact (rep_spec v hv).1
    have T_rep : ∀ a ∈ T, a = rep (i a) := by
      intro a ha
      rw [T_mem] at ha
      obtain ⟨v, hv, rfl⟩ := ha
      rw [(rep_spec v hv).2]
    have T_disj : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Disjoint (c a) (c b) := by
      intro a ha b hb hab
      have haM := T_in_M a ha
      have hbM := T_in_M b hb
      have haS := M_sub haM
      have hbS := M_sub hbM
      have hne : i a ≠ i b := by
        intro heq
        exact hab (by rw [T_rep a ha, T_rep b hb, heq])
      have h1 : ¬ (i a ⊆ i b) :=
        fun h => hne (Set.Subset.antisymm h (M_spec a haM b hbS h))
      have h2 : ¬ (i b ⊆ i a) :=
        fun h => hne (Set.Subset.antisymm (M_spec b hbM a haS h) h)
      exact incomparable a haS b hbS hab h1 h2
    have T_cover : ∀ a ∈ S, ∃ b ∈ T, i a ⊆ i b := by
      intro a ha
      obtain ⟨t, htM, hat⟩ := exists_max a ha
      have hvt : i t ∈ M.image i := Finset.mem_image.mpr ⟨t, htM, rfl⟩
      refine ⟨rep (i t), ?_, ?_⟩
      · rw [T_mem]; exact ⟨i t, hvt, rfl⟩
      · rw [(rep_spec (i t) hvt).2]; exact hat
    exact ⟨T, T_sub_S, T_disj, T_cover⟩
  · -- Empty case.
    rw [Finset.not_nonempty_iff_eq_empty] at hSne
    refine ⟨∅, Finset.empty_subset S, ?_, ?_⟩
    · intro a ha
      exact absurd ha (by simp)
    · intro a ha
      rw [hSne] at ha
      exact absurd ha (by simp)

theorem exists_disjoint_refinement {α X : Type*} (L : List α) (c : α → Set X) (i : α → Set X)
    (hci : ∀ a ∈ L, i a ⊆ c a)
    (hl : ∀ a ∈ L, ∀ b ∈ L, a ≠ b →
      Disjoint (c a) (c b) ∨ c a ⊆ i b ∨ c b ⊆ i a ∨ i a = i b) :
    ∃ L' : List α, L'.Nodup ∧ (∀ a ∈ L', a ∈ L) ∧
      (∀ a ∈ L', ∀ b ∈ L', a ≠ b → Disjoint (c a) (c b)) ∧
      (∀ a ∈ L, ∃ b ∈ L', i a ⊆ i b) := by
  classical
  have hci' : ∀ a ∈ L.toFinset, i a ⊆ c a := by
    intro a ha; exact hci a (List.mem_toFinset.mp ha)
  have hl' : ∀ a ∈ L.toFinset, ∀ b ∈ L.toFinset, a ≠ b →
      Disjoint (c a) (c b) ∨ c a ⊆ i b ∨ c b ⊆ i a ∨ i a = i b := by
    intro a ha b hb hab
    exact hl a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb) hab
  obtain ⟨T, hTS, hTdisj, hTcov⟩ := exists_disjoint_refinement_finset L.toFinset c i hci' hl'
  refine ⟨T.toList, T.nodup_toList, ?_, ?_, ?_⟩
  · intro a ha
    exact List.mem_toFinset.mp (hTS (Finset.mem_toList.mp ha))
  · intro a ha b hb hab
    exact hTdisj a (Finset.mem_toList.mp ha) b (Finset.mem_toList.mp hb) hab
  · intro a ha
    obtain ⟨b, hbT, hb⟩ := hTcov a (List.mem_toFinset.mpr ha)
    exact ⟨b, Finset.mem_toList.mpr hbT, hb⟩

end Work.BoxShrink.PinchOff
