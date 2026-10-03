import Mathlib
import Submission.Work.Peluse.SwapC.cgenSlotDefs

namespace Work.Peluse.SwapC

open Classical

/-- If a list has no duplicates, contains `i`, has `f i = some c`, and every other element is
mapped by `f` to `none`, then filtering-mapping `f` over the list yields the singleton `[c]`. -/
lemma filterMap_eq_singleton_of_nodup {α β : Type*} :
    ∀ (l : List α) (f : α → Option β) (i : α) (c : β),
      l.Nodup → i ∈ l → f i = some c → (∀ j ∈ l, j ≠ i → f j = none) →
      l.filterMap f = [c]
  | [], f, i, c, _, hi, _, _ => absurd hi (by simp)
  | j :: t, f, i, c, hnd, hi, hfi, huniq => by
      obtain ⟨hjnt, hndt⟩ := List.nodup_cons.mp hnd
      by_cases hji : j = i
      · have hfj : f j = some c := by rw [hji]; exact hfi
        rw [List.filterMap_cons_some hfj]
        have ht : t.filterMap f = [] := by
          rw [List.filterMap_eq_nil_iff]
          intro k hk
          have hki : k ≠ i := by
            intro hkii
            have hkj : k = j := by rw [hkii, hji]
            exact hjnt (hkj ▸ hk)
          exact huniq k (by simp [hk]) hki
        rw [ht]
      · have hfj : f j = none := huniq j (by simp) hji
        rw [List.filterMap_cons_none hfj]
        exact filterMap_eq_singleton_of_nodup t f i c hndt
          (by rcases List.mem_cons.mp hi with h | h
              · exact (hji h.symm).elim
              · exact h)
          hfi (fun k hk hki => huniq k (by simp [hk]) hki)

/-- The slots contributed by a pair of strings (`pairSlots a b`) are exactly the single optional slot
`slotOfF a b`. -/
theorem pairSlots_perm_slotOfF {s : ℕ} (a b : Fin s → Bool) :
    (Work.Peluse.SwapC.pairSlots a b).Perm (Work.Peluse.SwapC.slotOfF a b).toList := by
  unfold pairSlots slotOfF
  by_cases h : ∃ j : Fin s, slotCond j a b
  · rw [dif_pos h, Option.toList_some]
    have hspec : slotCond (Classical.choose h) a b := Classical.choose_spec h
    have key : (List.finRange s).filterMap
        (fun j : Fin s => if slotCond j a b then some (CC.dff j a b) else none)
        = [CC.dff (Classical.choose h) a b] := by
      refine filterMap_eq_singleton_of_nodup (List.finRange s)
        (fun j : Fin s => if slotCond j a b then some (CC.dff j a b) else none)
        (Classical.choose h) (CC.dff (Classical.choose h) a b)
        (List.nodup_finRange s) (List.mem_finRange _) ?_ ?_
      · rw [if_pos hspec]
      · intro j _ hji
        rw [if_neg]
        intro hjc
        exact hji (slotCond_unique hjc hspec)
    rw [key]
  · rw [dif_neg h, Option.toList_none]
    have hnil : (List.finRange s).filterMap
        (fun j : Fin s => if slotCond j a b then some (CC.dff j a b) else none) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro j _
      rw [if_neg]
      intro hjc
      exact h ⟨j, hjc⟩
    rw [hnil]

end Work.Peluse.SwapC
