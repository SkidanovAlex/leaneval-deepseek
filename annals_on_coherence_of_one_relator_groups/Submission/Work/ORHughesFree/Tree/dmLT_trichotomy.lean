import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs

namespace Work.ORHughesFree.Tree

/-- A nonempty multiset of trees whose elements are totally, transitively and irreflexively
ordered by `lt` has a maximal element. -/
theorem exists_max_mem (S : Multiset Tree)
    (htri : ∀ a ∈ S, ∀ b ∈ S, lt a b ∨ a = b ∨ lt b a)
    (htr : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, lt a b → lt b c → lt a c)
    (hirr : ∀ a ∈ S, ¬ lt a a) (hS : S ≠ 0) :
    ∃ c ∈ S, ∀ x ∈ S, ¬ lt c x := by
  revert htri htr hirr hS
  refine Multiset.induction_on S ?_ ?_
  · intro _ _ _ hS
    exact absurd rfl hS
  · intro a s ih htri htr hirr hS
    by_cases hs : s = 0
    · subst hs
      refine ⟨a, Multiset.mem_cons_self a 0, ?_⟩
      intro x hx
      rcases Multiset.mem_cons.mp hx with h | hx0
      · rw [h]; exact hirr a (Multiset.mem_cons_self a 0)
      · simp at hx0
    · obtain ⟨c, hcs, hcmax⟩ := ih
        (fun a' ha' b hb => htri a' (Multiset.mem_cons.mpr (Or.inr ha'))
          b (Multiset.mem_cons.mpr (Or.inr hb)))
        (fun a' ha' b hb c' hc' h1 h2 =>
          htr a' (Multiset.mem_cons.mpr (Or.inr ha')) b (Multiset.mem_cons.mpr (Or.inr hb))
            c' (Multiset.mem_cons.mpr (Or.inr hc')) h1 h2)
        (fun a' ha' => hirr a' (Multiset.mem_cons.mpr (Or.inr ha')))
        hs
      have hac : a ∈ a ::ₘ s := Multiset.mem_cons_self a s
      have hcc : c ∈ a ::ₘ s := Multiset.mem_cons.mpr (Or.inr hcs)
      rcases htri a hac c hcc with hlt | heq | hlt
      · refine ⟨c, hcc, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.mp hx with h | hxs
        · rw [h]
          intro hca
          exact hirr c hcc (htr c hcc a hac c hcc hca hlt)
        · exact hcmax x hxs
      · refine ⟨c, hcc, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.mp hx with h | hxs
        · rw [h, heq]; exact hirr c hcc
        · exact hcmax x hxs
      · refine ⟨a, hac, ?_⟩
        intro x hx
        rcases Multiset.mem_cons.mp hx with h | hxs
        · rw [h]; exact hirr a hac
        · intro hax
          have hxc : x ∈ a ::ₘ s := Multiset.mem_cons.mpr (Or.inr hxs)
          rcases htri c hcc x hxc with h | h | h
          · exact hcmax x hxs h
          · exact hirr a hac (htr a hac c hcc a hac (h.symm ▸ hax) hlt)
          · exact hirr a hac (htr a hac c hcc a hac
              (htr a hac x hxc c hcc hax h) hlt)

theorem dmLT_trichotomy {M N : Multiset Tree}
    (htri : ∀ a ∈ M + N, ∀ b ∈ M + N, lt a b ∨ a = b ∨ lt b a)
    (htr : ∀ a ∈ M + N, ∀ b ∈ M + N, ∀ c ∈ M + N, lt a b → lt b c → lt a c)
    (hirr : ∀ a ∈ M + N, ¬ lt a a) : dmLT lt M N ∨ M = N ∨ dmLT lt N M := by
  have main : ∀ n : ℕ, ∀ M N : Multiset Tree, M.card + N.card = n →
      (∀ a ∈ M + N, ∀ b ∈ M + N, lt a b ∨ a = b ∨ lt b a) →
      (∀ a ∈ M + N, ∀ b ∈ M + N, ∀ c ∈ M + N, lt a b → lt b c → lt a c) →
      (∀ a ∈ M + N, ¬ lt a a) →
      dmLT lt M N ∨ M = N ∨ dmLT lt N M := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro M N hcard htri htr hirr
      by_cases hM : M = 0
      · rw [hM]
        by_cases hN : N = 0
        · rw [hN]; exact Or.inr (Or.inl rfl)
        · left
          refine ⟨0, 0, N, hN, ?_, ?_, ?_⟩
          · simp
          · simp
          · intro a ha; simp at ha
      · by_cases hN : N = 0
        · rw [hN]
          right; right
          refine ⟨0, 0, M, hM, ?_, ?_, ?_⟩
          · simp
          · simp
          · intro a ha; simp at ha
        · obtain ⟨a₀, ha₀⟩ := Multiset.exists_mem_of_ne_zero hM
          have hSne : M + N ≠ 0 := by
            intro h
            have h0 : a₀ ∈ (0 : Multiset Tree) := by
              rw [← h]; exact Multiset.mem_add.mpr (Or.inl ha₀)
            simp at h0
          obtain ⟨c, hc, hcmax⟩ := exists_max_mem (M + N) htri htr hirr hSne
          have hcMN : c ∈ M ∨ c ∈ N := Multiset.mem_add.mp hc
          by_cases hcM : c ∈ M
          · by_cases hcN : c ∈ N
            · obtain ⟨M', hMeq⟩ := Multiset.exists_cons_of_mem hcM
              obtain ⟨N', hNeq⟩ := Multiset.exists_cons_of_mem hcN
              have hlt_card : M'.card + N'.card < n := by
                have h1 : M.card = M'.card + 1 := by
                  rw [hMeq]; exact Multiset.card_cons c M'
                have h2 : N.card = N'.card + 1 := by
                  rw [hNeq]; exact Multiset.card_cons c N'
                omega
              have hsub : ∀ a ∈ M' + N', a ∈ M + N := by
                intro a ha
                rcases Multiset.mem_add.mp ha with h | h
                · rw [hMeq]
                  exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons.mpr (Or.inr h)))
                · rw [hNeq]
                  exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_cons.mpr (Or.inr h)))
              have h' := ih (M'.card + N'.card) hlt_card M' N' rfl
                (fun a ha b hb => htri a (hsub a ha) b (hsub b hb))
                (fun a ha b hb c' hc' h1 h2 =>
                  htr a (hsub a ha) b (hsub b hb) c' (hsub c' hc') h1 h2)
                (fun a ha => hirr a (hsub a ha))
              rcases h' with ⟨X, Y, Z, hZ, hMY, hNZ, hcond⟩ | heq | ⟨X, Y, Z, hZ, hMY, hNZ, hcond⟩
              · left
                refine ⟨c ::ₘ X, Y, Z, hZ, ?_, ?_, hcond⟩
                · rw [hMeq, hMY, Multiset.cons_add]
                · rw [hNeq, hNZ, Multiset.cons_add]
              · right; left
                rw [hMeq, heq, hNeq]
              · right; right
                refine ⟨c ::ₘ X, Y, Z, hZ, ?_, ?_, hcond⟩
                · rw [hNeq, hMY, Multiset.cons_add]
                · rw [hMeq, hNZ, Multiset.cons_add]
            · right; right
              refine ⟨0, N, M, hM, ?_, ?_, ?_⟩
              · simp
              · simp
              · intro a ha
                refine ⟨c, hcM, ?_⟩
                have haS : a ∈ M + N := Multiset.mem_add.mpr (Or.inr ha)
                rcases htri a haS c hc with h | h | h
                · exact h
                · exact absurd (h ▸ ha) hcN
                · exact absurd h (hcmax a haS)
          · by_cases hcN : c ∈ N
            · left
              refine ⟨0, M, N, hN, ?_, ?_, ?_⟩
              · simp
              · simp
              · intro a ha
                refine ⟨c, hcN, ?_⟩
                have haS : a ∈ M + N := Multiset.mem_add.mpr (Or.inl ha)
                rcases htri a haS c hc with h | h | h
                · exact h
                · exact absurd (h ▸ ha) hcM
                · exact absurd h (hcmax a haS)
            · rcases hcMN with h | h
              · exact absurd h hcM
              · exact absurd h hcN
  exact main (M.card + N.card) M N rfl htri htr hirr

end Work.ORHughesFree.Tree
