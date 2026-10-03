/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Alternating lists in a free product, with possibly trivial end entries

`Work.ORBassSerre.CoprodTree.altList_prod_ne_one` says that a non-empty alternating list of
non-trivial elements of the factors of `A ∗ B` has non-trivial product.  The present file removes
the restriction that the *end* entries are non-trivial: an alternating list of length `≥ 3` whose
*interior* entries are non-trivial still cannot have product `1`, because the at most two trivial
end entries may simply be deleted (the product is unchanged, and what remains is a shorter
alternating list of non-trivial elements, to which `altList_prod_ne_one` applies).

This is the combinatorial heart of the fact that the Bass--Serre quiver of `A ∗ B` has no
non-trivial reduced closed path (`Work.ORBassSerre.CoprodTree.no_reduced_closed`).
-/
import Mathlib
import Submission.Work.ORBassSerre.CoprodTree.AltList
import Submission.Work.ORBassSerre.CoprodTree.altList_prod_ne_one

namespace Work.ORBassSerre.CoprodTree

universe u v

/-- The entries of the tail of an alternating list are alternating for the shifted side sequence:
if `x :: t` is alternating starting from the side `s`, then `t` is alternating starting from the
side `!s`. -/
theorem mem_side_of_cons_tail {A : Type u} {B : Type v} [Group A] [Group B]
    (x : Monoid.Coprod A B) (t : List (Monoid.Coprod A B)) (s : Bool)
    (hmem : ∀ j (hj : j < (x :: t).length),
      (x :: t)[j] ∈ sideFactor A B (sideAfter s j)) :
    ∀ j (hj : j < t.length), t[j] ∈ sideFactor A B (sideAfter (!s) j) := by
  intro j hj
  have hj' : j + 1 < (x :: t).length := by simpa using hj
  have h := hmem (j + 1) hj'
  simpa [List.getElem_cons_succ, sideAfter_shift] using h

theorem false_of_alternating {A : Type u} {B : Type v} [Group A] [Group B] (s : Bool) (l : List (Monoid.Coprod A B)) (hlen : 3 ≤ l.length) (hprod : l.prod = 1) (hmem : ∀ j (hj : j < l.length), l[j] ∈ Work.ORBassSerre.CoprodTree.sideFactor A B (Work.ORBassSerre.CoprodTree.sideAfter s j)) (hmid : ∀ j (hj : j < l.length), 0 < j → j + 1 < l.length → l[j] ≠ 1) : False := by
  -- Write `l = x :: (t' ++ [y])`, so that `x` is the first and `y` the last entry.
  have hne : l ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  obtain ⟨x, t, rfl⟩ : ∃ x t, l = x :: t := ⟨l.head hne, l.tail, (List.cons_head_tail hne).symm⟩
  have ht_ne : t ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  obtain ⟨t', y, ht⟩ : ∃ t' y, t = t' ++ [y] := by
    rcases List.eq_nil_or_concat t with h | ⟨t', y, h⟩
    · exact absurd h ht_ne
    · rw [List.concat_eq_append] at h; exact ⟨t', y, h⟩
  subst ht
  have ht'_ge1 : 1 ≤ t'.length := by
    simp only [List.length_cons, List.length_append, List.length_nil] at hlen
    omega
  -- All entries of `t'` are interior entries of `l`, hence non-trivial.
  have hmid_t' : ∀ z ∈ t', z ≠ 1 := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hz
    have hj' : j + 1 < (x :: (t' ++ [y])).length := by
      simp only [List.length_cons, List.length_append, List.length_nil] at *
      omega
    have h := hmid (j + 1) hj' (by omega) (by
      simp only [List.length_cons, List.length_append, List.length_nil]; omega)
    have h1 : (x :: (t' ++ [y]))[j + 1] = t'[j] := by
      rw [List.getElem_cons_succ]
      exact List.getElem_append_left hj
    intro hz1
    exact h (by rw [h1]; exact hz1)
  by_cases hx : x = 1
  · by_cases hy : y = 1
    · -- both end entries trivial: strip both, leaving `t'` (all entries interior).
      have hne_m : t' ≠ [] := List.length_pos_iff.mp (by omega)
      have hmem_m : ∀ j (hj : j < t'.length), t'[j] ∈ sideFactor A B (sideAfter (!s) j) := by
        intro j hj
        have h2 := mem_side_of_cons_tail x (t' ++ [y]) s hmem j (by
          simp only [List.length_append]; omega)
        rw [← List.getElem_append_left hj]
        exact h2
      have hprod_m : t'.prod = 1 := by
        have h := hprod
        simp only [List.prod_cons, List.prod_append, List.prod_nil, hx, hy, one_mul, mul_one] at h
        exact h
      exact absurd hprod_m (altList_prod_ne_one (!s) t' hne_m hmem_m hmid_t')
    · -- only the first entry trivial: strip it, leaving `t' ++ [y]`.
      have hne_m : t' ++ [y] ≠ [] := by simp
      have hmem_m : ∀ j (hj : j < (t' ++ [y]).length),
          (t' ++ [y])[j] ∈ sideFactor A B (sideAfter (!s) j) :=
        mem_side_of_cons_tail x (t' ++ [y]) s hmem
      have hone_m : ∀ z ∈ t' ++ [y], z ≠ 1 := by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hmid_t' z hz
        · rw [List.mem_singleton.mp hz]; exact hy
      have hprod_m : (t' ++ [y]).prod = 1 := by
        have h := hprod
        simp only [List.prod_cons, hx, one_mul] at h
        exact h
      exact absurd hprod_m (altList_prod_ne_one (!s) (t' ++ [y]) hne_m hmem_m hone_m)
  · by_cases hy : y = 1
    · -- only the last entry trivial: strip it, leaving `x :: t'`.
      have hne_m : x :: t' ≠ [] := by simp
      have hmem_m : ∀ j (hj : j < (x :: t').length),
          (x :: t')[j] ∈ sideFactor A B (sideAfter s j) := by
        intro j hj
        have hj' : j < (x :: (t' ++ [y])).length := by
          simp only [List.length_cons, List.length_append, List.length_nil] at *
          omega
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0
          simpa using hmem 0 (by
            simp only [List.length_cons, List.length_append, List.length_nil]; omega)
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
          have h1 : (x :: t')[i + 1] = (x :: (t' ++ [y]))[i + 1] := by
            rw [List.getElem_cons_succ, List.getElem_cons_succ]
            exact (List.getElem_append_left (as := t') (bs := [y]) (i := i)
              (by simp only [List.length_cons] at hj; omega)).symm
          rw [h1]
          exact hmem (i + 1) hj'
      have hone_m : ∀ z ∈ x :: t', z ≠ 1 := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact hmid_t' z hz
      have hprod_m : (x :: t').prod = 1 := by
        have h1 : (x :: (t' ++ [y])) = (x :: t').concat y := by simp [List.concat_eq_append]
        rw [h1, List.prod_concat, hy, mul_one] at hprod
        exact hprod
      exact absurd hprod_m (altList_prod_ne_one s (x :: t') hne_m hmem_m hone_m)
    · -- no trivial end entry: `l` itself is alternating with all entries non-trivial.
      have hone : ∀ z ∈ x :: (t' ++ [y]), z ≠ 1 := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        rcases List.mem_append.mp hz with hz | hz
        · exact hmid_t' z hz
        · rw [List.mem_singleton.mp hz]; exact hy
      exact absurd hprod (altList_prod_ne_one s (x :: (t' ++ [y])) hne hmem hone)

end Work.ORBassSerre.CoprodTree
