import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic

/-!
# `Work.PL.Shell.flagEnum_mem`

`flagEnum vs` enumerates exactly the flags on the vertex list `vs`, i.e. membership in
`flagEnum vs` is equivalent to being a permutation of `vs`.

The enumeration is defined recursively by the *last* vertex of the flag
(`flagEnum vs = vs.flatMap fun m => (flagEnum (vs.erase m)).map (· ++ [m])`), so the natural
induction is on the length of `vs`: erasing one element shortens the list by one.  Both
directions are then read off the recursive description, the only (elementary) list fact needed
being that erasing one occurrence of `a` and appending `a` at the end is a permutation.
-/

namespace Work.PL.Shell

variable {N : ℕ}

/-- Erasing one occurrence of `a` from `vs` and appending `a` at the end gives a permutation
of `vs`, whenever `a ∈ vs`. -/
theorem erase_append_singleton_perm {a : PL.E N} {vs : List (PL.E N)} (h : a ∈ vs) :
    List.Perm (vs.erase a ++ [a]) vs := by
  apply Multiset.coe_eq_coe.mp
  rw [← Multiset.coe_add, Multiset.coe_singleton, ← Multiset.coe_erase]
  have hmem : a ∈ (vs : Multiset (PL.E N)) := Multiset.mem_coe.mpr h
  rw [Multiset.add_comm]
  exact Multiset.cons_erase hmem

theorem flagEnum_mem {vs l : List (PL.E N)} : l ∈ Work.PL.Shell.flagEnum vs ↔ l.Perm vs := by
  suffices key : ∀ n, ∀ vs : List (PL.E N), vs.length ≤ n →
      ∀ l : List (PL.E N), l ∈ Work.PL.Shell.flagEnum vs ↔ l.Perm vs from
    key vs.length vs le_rfl l
  intro n
  induction n with
  | zero =>
    intro vs hvs l
    have h : vs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hvs)
    subst h
    simp [Work.PL.Shell.flagEnum]
  | succ n ih =>
    intro vs hvs l
    rcases vs with _ | ⟨m, rest⟩
    · simp [Work.PL.Shell.flagEnum]
    · have hne : (m :: rest) ≠ [] := List.cons_ne_nil m rest
      constructor
      · intro h
        rw [Work.PL.Shell.flagEnum.eq_2 _ hne, List.mem_flatMap] at h
        obtain ⟨a, ha, h⟩ := h
        rw [List.mem_map] at h
        obtain ⟨t, ht, htl⟩ := h
        have hlt : ((m :: rest).erase a).length ≤ n := by
          rw [List.length_erase_of_mem ha]
          have h1 : 1 ≤ (m :: rest).length := by simp
          omega
        have htperm : t.Perm ((m :: rest).erase a) := (ih _ hlt t).mp ht
        rw [← htl]
        exact (htperm.append_right [a]).trans (erase_append_singleton_perm ha)
      · intro hl
        have hlne : l ≠ [] := by
          rintro rfl
          have h2 := hl.length_eq
          simp at h2
        set a : PL.E N := l.getLast hlne with ha
        have hdrop : l.dropLast ++ [a] = l := by
          rw [ha]
          exact List.dropLast_append_getLast hlne
        have hms : (l.dropLast : Multiset (PL.E N)) + {a} =
            ((m :: rest : List (PL.E N)) : Multiset (PL.E N)) := by
          have e1 : ((l.dropLast ++ [a] : List (PL.E N)) : Multiset (PL.E N)) =
              (l : Multiset (PL.E N)) := by rw [hdrop]
          have e2 : ((l.dropLast : Multiset (PL.E N)) + {a}) =
              ((l.dropLast ++ [a] : List (PL.E N)) : Multiset (PL.E N)) := by
            rw [← Multiset.coe_singleton a, ← Multiset.coe_add]
          rw [e2, e1, Multiset.coe_eq_coe.mpr hl]
        obtain ⟨hamem, hterase⟩ := Multiset.add_singleton_eq_iff.mp hms
        have halist : a ∈ (m :: rest : List (PL.E N)) := Multiset.mem_coe.mp hamem
        have hlt : ((m :: rest).erase a).length ≤ n := by
          rw [List.length_erase_of_mem halist]
          have h1 : 1 ≤ (m :: rest).length := by simp
          omega
        have hperm : l.dropLast.Perm ((m :: rest).erase a) := by
          apply Multiset.coe_eq_coe.mp
          rw [hterase, Multiset.coe_erase]
        have ht : l.dropLast ∈ Work.PL.Shell.flagEnum ((m :: rest).erase a) :=
          (ih _ hlt _).mpr hperm
        rw [Work.PL.Shell.flagEnum.eq_2 _ hne, List.mem_flatMap]
        refine ⟨a, halist, ?_⟩
        rw [List.mem_map]
        exact ⟨l.dropLast, ht, hdrop⟩

end Work.PL.Shell
