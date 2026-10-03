import Mathlib

namespace Work.OROneRel

/-- If `A` is a reduced word (a list of letters `α × Bool`) and all its first components are
equal to a fixed `t`, then all its letters are equal: there is a single `b : Bool` with
`p = (t, b)` for every `p ∈ A`. This is because `IsReduced` forces consecutive letters with the
same first component to have the same second component. -/
lemma exists_eq_of_isReduced {α : Type*} {t : α} (A : List (α × Bool))
    (h : FreeGroup.IsReduced A) (hA : ∀ p ∈ A, p.1 = t) :
    ∃ b : Bool, ∀ p ∈ A, p = (t, b) := by
  induction A with
  | nil => exact ⟨true, by simp⟩
  | cons p l ih =>
    cases l with
    | nil =>
      exact ⟨p.2, by
        intro q hq
        rw [List.mem_singleton] at hq
        rw [hq]
        exact Prod.ext (hA p (by simp)) rfl⟩
    | cons q l' =>
      have hrc := FreeGroup.isReduced_cons_cons.mp h
      have hrel : p.2 = q.2 := hrc.1 (by rw [hA p (by simp), hA q (by simp)])
      have hA' : ∀ r ∈ q :: l', r.1 = t := fun r hr => hA r (List.mem_cons_of_mem p hr)
      obtain ⟨b, hb⟩ := ih hrc.2 hA'
      refine ⟨b, ?_⟩
      intro r hr
      rcases List.mem_cons.mp hr with h1 | h1
      · rw [h1]
        exact Prod.ext (hA p (by simp)) (hrel.trans (congrArg Prod.snd (hb q (by simp))))
      · exact hb r h1

theorem isReduced_replicate_of_fst_eq {α : Type*} {t : α} {A : List (α × Bool)}
    (h : FreeGroup.IsReduced A) (hA : ∀ p ∈ A, p.1 = t) :
    ∃ c : α × Bool, A = List.replicate A.length c := by
  obtain ⟨b, hb⟩ := exists_eq_of_isReduced A h hA
  exact ⟨(t, b), List.eq_replicate_length.mpr hb⟩

end Work.OROneRel
