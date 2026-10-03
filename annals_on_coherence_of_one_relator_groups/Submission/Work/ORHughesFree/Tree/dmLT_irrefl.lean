import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs

namespace Work.ORHughesFree.Tree

/-- A finite set carrying a transitive, irreflexive relation has a maximal element: an element `m`
with `¬ r m b` for every `b` in the set. -/
private lemma exists_maximal_of_finset {α : Type*} (r : α → α → Prop) :
    ∀ s : Finset α, (∀ a ∈ s, ¬ r a a) →
      (∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, r a b → r b c → r a c) →
      s.Nonempty → ∃ m ∈ s, ∀ b ∈ s, ¬ r m b := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro _ _ hne; exact absurd hne Finset.not_nonempty_empty
  | insert a s ha ih =>
    intro hirr htr hne
    rcases Finset.eq_empty_or_nonempty s with hs | hsne
    · subst hs
      refine ⟨a, Finset.mem_insert_self a ∅, ?_⟩
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with hba | hb
      · rw [hba]; exact hirr a (Finset.mem_insert_self a ∅)
      · exact absurd hb (Finset.notMem_empty b)
    · obtain ⟨m, hm, hmax⟩ := ih
        (fun x hx => hirr x (Finset.mem_insert_of_mem hx))
        (fun x hx y hy z hz => htr x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
          z (Finset.mem_insert_of_mem hz)) hsne
      by_cases hma : r m a
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with hba | hb
        · rw [hba]; exact hirr a (Finset.mem_insert_self a s)
        · intro hab
          exact hmax b hb (htr m (Finset.mem_insert_of_mem hm) a (Finset.mem_insert_self a s)
            b (Finset.mem_insert_of_mem hb) hma hab)
      · refine ⟨m, Finset.mem_insert_of_mem hm, ?_⟩
        intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with hba | hb
        · rw [hba]; exact hma
        · exact hmax b hb

set_option linter.unusedVariables false in
theorem dmLT_irrefl {M : Multiset Tree}
    (htri : ∀ a ∈ M, ∀ b ∈ M, lt a b ∨ a = b ∨ lt b a)
    (htr : ∀ a ∈ M, ∀ b ∈ M, ∀ c ∈ M, lt a b → lt b c → lt a c)
    (hirr : ∀ a ∈ M, ¬ lt a a) : ¬ dmLT lt M M := by
  classical
  rintro ⟨X, Y, Z, hZ, hM, hMZ, hstep⟩
  have hYZ : Y = Z := Multiset.add_right_inj.mp (hM.symm.trans hMZ)
  rw [hYZ] at hstep
  have hmem : ∀ a ∈ Z, a ∈ M := by
    intro a ha
    rw [hMZ]
    exact Multiset.mem_add.mpr (Or.inr ha)
  obtain ⟨m, hm, hmax⟩ := exists_maximal_of_finset lt Z.toFinset
    (fun a ha => hirr a (hmem a (Multiset.mem_toFinset.mp ha)))
    (fun a ha b hb c hc => htr a (hmem a (Multiset.mem_toFinset.mp ha))
      b (hmem b (Multiset.mem_toFinset.mp hb)) c (hmem c (Multiset.mem_toFinset.mp hc)))
    (Multiset.toFinset_nonempty.mpr hZ)
  obtain ⟨b, hbZ, hmb⟩ := hstep m (Multiset.mem_toFinset.mp hm)
  exact hmax b (Multiset.mem_toFinset.mpr hbZ) hmb

end Work.ORHughesFree.Tree
