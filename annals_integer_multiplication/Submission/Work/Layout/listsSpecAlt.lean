import Mathlib
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.SortSpecs
import Submission.Work.Layout.Pass2Aux
import Submission.Work.Layout.Pass2Aux.Pure
import Submission.Work.Layout.Pass2Aux.Facts

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# `Work.Layout.Sk.ListsSpec`, from the pass-2 helper lemmas

This file reproves the pure list facts `ListsSpec` using the `passGo`/`passR` lemmas of
`Submission/Work/Layout/Pass2Aux/Pure.lean` and the `merge2` lemmas of `Pass2Aux/Facts.lean`.  The
facts not already available there are the exact length of one / two `pass`es (needing
`(n + n + 1) / 2 = n`) and the `altSplit` facts, whose permutation statement is proved via the
accumulator-shift equality `altGo_flat₁/₂`.
-/

namespace Work.Layout

open HvdH
open scoped List

/-! ## arithmetic -/

theorem two_mul_add_one_div_two (n : ℕ) : (2 * n + 1) / 2 = n := by
  have h : 1 / 2 = 0 := Nat.div_eq_of_lt (by norm_num)
  have h2 : (2 * n + 1) / 2 = n + 1 / 2 := Nat.mul_add_div (m := 2) (by norm_num) n 1
  rw [h2, h]
  exact Nat.add_zero n

theorem two_mul_add_two_div_two (n : ℕ) : (2 * n + 2) / 2 = n + 1 := by
  have h : (2 * n + 2) / 2 = n + 2 / 2 := Nat.mul_add_div (m := 2) (by norm_num) n 2
  rw [h]

theorem div_two_self_add_one (n : ℕ) : (n + n + 1) / 2 = n := by
  have h : n + n + 1 = 2 * n + 1 := by ring
  rw [h]
  exact two_mul_add_one_div_two n

theorem div_two_self_add_two (n : ℕ) : (n + n + 2) / 2 = n + 1 := by
  have h : n + n + 2 = 2 * n + 2 := by ring
  rw [h]
  exact two_mul_add_two_div_two n

/-! ## the length of one and of two passes -/

theorem passR_len_sum (ps qs : List (List Val))
    (hlen : ps.length = qs.length ∨ ps.length = qs.length + 1) :
    (Sk.passR ps qs).1.length + (Sk.passR ps qs).2.length = (ps.length + qs.length + 1) / 2 := by
  have h := passGo_len_eq ps qs ([] : List (List Val)) ([] : List (List Val)) hlen true
  simp only [List.length_nil, Nat.zero_add, Nat.add_zero] at h
  show (Sk.passGo true ps qs [] []).1.length + (Sk.passGo true ps qs [] []).2.length
      = (ps.length + qs.length + 1) / 2
  rw [h]
  rcases hlen with hh | hh
  · rw [if_pos hh, hh]
    simp only [Nat.add_zero]
    exact (div_two_self_add_one qs.length).symm
  · rw [hh, if_neg (by omega : ¬ (qs.length + 1 = qs.length))]
    have h2 : qs.length + 1 + qs.length + 1 = qs.length + qs.length + 2 := by ring
    rw [h2]
    exact (div_two_self_add_two qs.length).symm

theorem pass2R_len_sum (ps qs : List (List Val))
    (hlen : ps.length = qs.length ∨ ps.length = qs.length + 1) :
    (Sk.pass2R ps qs).1.length + (Sk.pass2R ps qs).2.length =
      ((ps.length + qs.length + 1) / 2 + 1) / 2 := by
  have h1 := passR_len_sum ps qs hlen
  have h2 := passR_len_inv ps qs hlen
  have h3 := passR_len_sum (Sk.passR ps qs).1 (Sk.passR ps qs).2 h2
  show (Sk.passR (Sk.passR ps qs).1 (Sk.passR ps qs).2).1.length +
      (Sk.passR (Sk.passR ps qs).1 (Sk.passR ps qs).2).2.length = _
  rw [h3, h1]

/-! ## `altSplit` -/

theorem altGo_len : ∀ (xs : List Val) (ax ay : List (List Val)),
    (Sk.altGo xs ax ay).1.length + (Sk.altGo xs ax ay).2.length
      = ax.length + ay.length + xs.length
  | [], ax, ay => by simp [Sk.altGo]
  | [a], ax, ay => by simp [Sk.altGo]; omega
  | a :: b :: rest, ax, ay => by
      show (Sk.altGo rest ([a] :: ax) ([b] :: ay)).1.length +
          (Sk.altGo rest ([a] :: ax) ([b] :: ay)).2.length
        = ax.length + ay.length + (a :: b :: rest).length
      rw [altGo_len rest ([a] :: ax) ([b] :: ay)]
      simp only [List.length_cons]
      omega

theorem altGo_flat₁ : ∀ (xs : List Val) (ax ay : List (List Val)),
    (Sk.altGo xs ax ay).1.flatten = (Sk.altGo xs [] []).1.flatten ++ ax.flatten
  | [], ax, ay => by simp [Sk.altGo]
  | [a], ax, ay => by simp [Sk.altGo]
  | a :: b :: rest, ax, ay => by
      show (Sk.altGo rest ([a] :: ax) ([b] :: ay)).1.flatten
          = (Sk.altGo rest ([a] :: ([] : List (List Val))) ([b] :: [])).1.flatten ++ ax.flatten
      rw [altGo_flat₁ rest ([a] :: ax) ([b] :: ay),
        altGo_flat₁ rest ([a] :: ([] : List (List Val))) ([b] :: [])]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

theorem altGo_flat₂ : ∀ (xs : List Val) (ax ay : List (List Val)),
    (Sk.altGo xs ax ay).2.flatten = (Sk.altGo xs [] []).2.flatten ++ ay.flatten
  | [], ax, ay => by simp [Sk.altGo]
  | [a], ax, ay => by simp [Sk.altGo]
  | a :: b :: rest, ax, ay => by
      show (Sk.altGo rest ([a] :: ax) ([b] :: ay)).2.flatten
          = (Sk.altGo rest ([a] :: ([] : List (List Val))) ([b] :: [])).2.flatten ++ ay.flatten
      rw [altGo_flat₂ rest ([a] :: ax) ([b] :: ay),
        altGo_flat₂ rest ([a] :: ([] : List (List Val))) ([b] :: [])]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

theorem altGo_perm : ∀ xs : List Val,
    ((Sk.altGo xs [] []).1.flatten ++ (Sk.altGo xs [] []).2.flatten).Perm xs
  | [] => by simp [Sk.altGo]
  | [a] => by simp [Sk.altGo]
  | a :: b :: rest => by
      have h1 := altGo_flat₁ rest ([a] :: ([] : List (List Val))) ([b] :: [])
      have h2 := altGo_flat₂ rest ([a] :: ([] : List (List Val))) ([b] :: [])
      have ih := altGo_perm rest
      show (((Sk.altGo rest ([a] :: ([] : List (List Val))) ([b] :: [])).1.flatten ++
          (Sk.altGo rest ([a] :: ([] : List (List Val))) ([b] :: [])).2.flatten)).Perm
            (a :: b :: rest)
      rw [h1, h2]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      set A1 := (Sk.altGo rest [] []).1.flatten with hA1
      set A2 := (Sk.altGo rest [] []).2.flatten with hA2
      calc ((A1 ++ [a]) ++ (A2 ++ [b]))
          ~ (A1 ++ [a]) ++ (b :: A2) :=
            (List.perm_append_singleton b A2).append_left (A1 ++ [a])
        _ ~ A1 ++ (a :: (b :: A2)) := List.Perm.of_eq (by
              simp only [List.append_assoc, List.singleton_append, List.nil_append])
        _ ~ a :: (A1 ++ (b :: A2)) := (List.perm_middle (l₁ := A1) (a := a) (l₂ := b :: A2))
        _ ~ a :: (b :: (A1 ++ A2)) :=
            ((List.perm_middle (l₁ := A1) (a := b) (l₂ := A2))).cons a
        _ ~ a :: (b :: rest) := (ih.cons b).cons a

theorem altGo_len_inv : ∀ (xs : List Val) (ax ay : List (List Val)),
    ax.length = ay.length →
    (Sk.altGo xs ax ay).1.length = (Sk.altGo xs ax ay).2.length ∨
      (Sk.altGo xs ax ay).1.length = (Sk.altGo xs ax ay).2.length + 1
  | [], ax, ay, h => by simpa [Sk.altGo] using Or.inl h
  | [a], ax, ay, h => by
      show ([a] :: ax).length = ay.length ∨ ([a] :: ax).length = ay.length + 1
      simp only [List.length_cons]
      right; omega
  | a :: b :: rest, ax, ay, h => by
      have h' : ([a] :: ax).length = ([b] :: ay).length := by
        simp only [List.length_cons]; omega
      exact altGo_len_inv rest ([a] :: ax) ([b] :: ay) h'

theorem altGo_runs : ∀ (xs : List Val) (ax ay : List (List Val)),
    (∀ r ∈ ax, r.length = 1) → (∀ r ∈ ay, r.length = 1) →
    (∀ r ∈ (Sk.altGo xs ax ay).1, r.length = 1) ∧
      (∀ r ∈ (Sk.altGo xs ax ay).2, r.length = 1)
  | [], ax, ay, hx, hy => by simpa [Sk.altGo] using ⟨hx, hy⟩
  | [a], ax, ay, hx, hy => by
      have hx' : ∀ r ∈ ([a] :: ax : List (List Val)), r.length = 1 := by
        intro r hr
        rcases List.mem_cons.mp hr with h | h
        · rw [h]; simp
        · exact hx r h
      have h' := altGo_runs [] ([a] :: ax) ay hx' hy
      simpa [Sk.altGo] using h'
  | a :: b :: rest, ax, ay, hx, hy => by
      have hx' : ∀ r ∈ ([a] :: ax : List (List Val)), r.length = 1 := by
        intro r hr
        rcases List.mem_cons.mp hr with h | h
        · rw [h]; simp
        · exact hx r h
      have hy' : ∀ r ∈ ([b] :: ay : List (List Val)), r.length = 1 := by
        intro r hr
        rcases List.mem_cons.mp hr with h | h
        · rw [h]; simp
        · exact hy r h
      exact altGo_runs rest ([a] :: ax) ([b] :: ay) hx' hy'

/-! ## `ListsSpec` -/

theorem listsSpecAlt : Sk.ListsSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact merge2_perm
  · exact merge2_length
  · exact merge2_sorted
  · intro r rs
    show ((encs r ++ [gMark]) ++ (rs.map (fun r => encs r ++ [gMark])).flatten)
        = encs r ++ gMark :: (rs.map (fun r => encs r ++ [gMark])).flatten
    simp only [List.append_assoc, List.singleton_append, List.nil_append]
  · intro rs rs'
    simp only [Sk.runEnc, List.map_append, List.flatten_append]
  · rfl
  · rfl
  · intro r rs
    exact runEncB_cons r rs
  · intro ps qs hlen
    exact passR_len_sum ps qs hlen
  · intro ps qs hlen
    exact passR_len_inv ps qs hlen
  · intro ps qs hlen
    exact passR_perm ps qs hlen
  · intro ps qs hlen hsort hnd
    exact passR_sorted ps qs hsort (PairKeys.of_flat_nodup hnd)
  · intro ps qs hlen
    exact pass2R_len_sum ps qs hlen
  · intro ps qs hlen
    have h1 := passR_len_inv ps qs hlen
    have h2 := passR_len_inv (Sk.passR ps qs).1 (Sk.passR ps qs).2 h1
    show (Sk.passR (Sk.passR ps qs).1 (Sk.passR ps qs).2).1.length
        = (Sk.passR (Sk.passR ps qs).1 (Sk.passR ps qs).2).2.length ∨
      (Sk.passR (Sk.passR ps qs).1 (Sk.passR ps qs).2).1.length
        = (Sk.passR (Sk.passR ps qs).1 (Sk.passR ps qs).2).2.length + 1
    exact h2
  · intro ps qs hlen
    have h1 := passR_perm ps qs hlen
    have h2 := passR_len_inv ps qs hlen
    have h3 := passR_perm (Sk.passR ps qs).1 (Sk.passR ps qs).2 h2
    show (((Sk.passR (Sk.passR ps qs).1 (Sk.passR ps qs).2).1 ++
        (Sk.passR (Sk.passR ps qs).1 (Sk.passR ps qs).2).2).flatten).Perm ((ps ++ qs).flatten)
    exact h3.trans h1
  · intro ps qs hlen hsort hnd
    have h1 := passR_len_inv ps qs hlen
    have hs1 : RunsSort (ps ++ qs) := hsort
    have hk1 : PairKeys ps qs := PairKeys.of_flat_nodup hnd
    have hs2 : RunsSort ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2) := passR_sorted ps qs hs1 hk1
    have hperm := passR_perm ps qs hlen
    have hnd2 : ((((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2).flatten).map pairKey).Nodup :=
      (hperm.map pairKey).nodup_iff.mpr hnd
    have hk2 : PairKeys (Sk.passR ps qs).1 (Sk.passR ps qs).2 := PairKeys.of_flat_nodup hnd2
    have hs3 : RunsSort ((Sk.passR (Sk.passR ps qs).1 (Sk.passR ps qs).2).1 ++
        (Sk.passR (Sk.passR ps qs).1 (Sk.passR ps qs).2).2) :=
      passR_sorted (Sk.passR ps qs).1 (Sk.passR ps qs).2 hs2 hk2
    intro r hr
    exact hs3 r hr
  · intro xs
    have h := altGo_len xs ([] : List (List Val)) ([] : List (List Val))
    simpa [Sk.altSplit] using h
  · intro xs
    have h := altGo_len_inv xs ([] : List (List Val)) ([] : List (List Val)) rfl
    simpa [Sk.altSplit] using h
  · intro xs
    have h := altGo_perm xs
    simpa [Sk.altSplit] using h
  · intro xs r hr
    have h := altGo_runs xs ([] : List (List Val)) ([] : List (List Val)) (by simp) (by simp)
    simp only [Sk.altSplit] at hr
    rcases List.mem_append.mp hr with h1 | h1
    · exact h.1 r h1
    · exact h.2 r h1

end Work.Layout
