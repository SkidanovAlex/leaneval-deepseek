import Mathlib
import Submission.DirSet

/-!
# The cyclic order of the spike directions (the telescoping spine)

The E2b telescoping sum is a fold over the finite ordered list of the
hedgehog's spike directions.  This module provides that spine.

`dirList S` is the increasing list of the distinct directions of the hedgehog
over `S` (the `Finset.sort` of `dirSet S`).  Mathlib gives the key structure
for free: `Finset.sortedLT_sort` makes `dirList S` a `SortedLT` list (its
index map `i ↦ (dirList S).get i` is strictly monotone), and
`sort_nodup`/`mem_sort`/`length_sort` give the bijection between
`Fin (dirSet S).card` and `dirSet S`.

Main theorems:
  - `succ_after_get`: for `x := (dirList S).get i`, not last, the least
    direction strictly above `x` is the next entry `(dirList S).get (i+1)`;
  - `no_dir_between_get`: no direction lies strictly between consecutive
    entries (the angular gaps of the decomposition);
  - `last_get_no_above`: the last entry has no direction above it (the
    wrap-around to the minimum being handled separately, via
    `exp`-periodicity, in the assembly).
-/

noncomputable section

open scoped Complex Real
open Complex

namespace Submission.DirCycle

open Submission.DirSet

/-- The increasing list of the spike directions of the hedgehog over `S`. -/
def dirList (S : Finset ℂ) : List ℝ := (dirSet S).sort

/-- `dirList` is strictly increasing (its index map is strictly monotone). -/
lemma dirList_strict (S : Finset ℂ) : (dirList S).SortedLT := by
  simpa [dirList] using (Finset.sortedLT_sort (dirSet S))

/-- `dirList` has no repetitions. -/
lemma dirList_nodup (S : Finset ℂ) : (dirList S).Nodup := by
  simpa [dirList] using (Finset.sort_nodup (dirSet S) (· ≤ ·))

/-- The length of `dirList` is the number of directions. -/
lemma dirList_length (S : Finset ℂ) : (dirList S).length = (dirSet S).card := by
  simpa [dirList] using (Finset.length_sort (dirSet S) (· ≤ ·))

/-- The members of `dirList` are exactly the directions. -/
lemma dirList_mem_iff (S : Finset ℂ) (θ : ℝ) : θ ∈ dirList S ↔ θ ∈ dirSet S := by
  simpa [dirList] using (Finset.mem_sort (dirSet S) (· ≤ ·) (a := θ))

/-- Earlier list entries are `≤` later ones. -/
lemma dirList_get_mono (S : Finset ℂ) {i j : Fin (dirList S).length} (hij : i.val ≤ j.val) :
    (dirList S).get i ≤ (dirList S).get j := by
  dsimp [dirList]
  exact ((Finset.pairwise_sort (dirSet S) (· ≤ ·)).rel_get_of_le
    (a := ⟨i.val, by simpa [dirList] using i.isLt⟩)
    (b := ⟨j.val, by simpa [dirList] using j.isLt⟩)
    (by simpa [dirList] using hij))

/-- Earlier list entries are `<` later ones. -/
lemma dirList_get_strict (S : Finset ℂ) {i j : Fin (dirList S).length} (hij : i.val < j.val) :
    (dirList S).get i < (dirList S).get j := by
  exact (dirList_strict S) hij

/-- Strict monotonicity, contrapositive: if entry `i` is `<` entry `j` then
`i` is an earlier index. -/
lemma index_lt_of_get_lt (S : Finset ℂ) {i j : Fin (dirList S).length}
    (h : (dirList S).get i < (dirList S).get j) : i.val < j.val := by
  by_contra hnot
  have hji : j.val ≤ i.val := le_of_not_gt hnot
  have hm := dirList_get_mono S (i := j) (j := i) hji
  linarith

/-- The next list entry is a direction strictly above the current one. -/
lemma next_get_mem_above (S : Finset ℂ) (i : Fin (dirList S).length)
    (hi : i.val + 1 < (dirList S).length) :
    (dirList S).get ⟨i.val + 1, hi⟩ ∈
      (dirSet S).filter (fun ψ => (dirList S).get i < ψ) := by
  classical
  rw [Finset.mem_filter]
  constructor
  · exact (dirList_mem_iff S ((dirList S).get ⟨i.val + 1, hi⟩)).mp (List.get_mem _ _)
  · have hij' : i.val < (⟨i.val + 1, hi⟩ : Fin (dirList S).length).val := by
      exact Nat.lt_succ_self i.val
    exact dirList_get_strict S (i := i) (j := ⟨i.val + 1, hi⟩) hij'

/-- **Successor = next list entry.**  For a direction `x := (dirList S).get i`
that is not the last entry, the least direction strictly above `x` is the
next list entry `(dirList S).get (i + 1)`. -/
theorem succ_after_get (S : Finset ℂ) (i : Fin (dirList S).length)
    (hi : i.val + 1 < (dirList S).length) :
    ((dirSet S).filter (fun ψ => (dirList S).get i < ψ)).min'
        ⟨(dirList S).get ⟨i.val + 1, hi⟩, next_get_mem_above S i hi⟩
      = (dirList S).get ⟨i.val + 1, hi⟩ := by
  classical
  let f : Finset ℝ := (dirSet S).filter (fun ψ => (dirList S).get i < ψ)
  let y : ℝ := (dirList S).get ⟨i.val + 1, hi⟩
  have hyf : y ∈ f := next_get_mem_above S i hi
  let hne : f.Nonempty := ⟨y, hyf⟩
  have hmin : f.min' hne = y := by
    apply le_antisymm
    · exact Finset.min'_le f y hyf
    · exact Finset.le_min' f hne y (by
        intro θ hθ
        have hθf1 : θ ∈ dirSet S := (Finset.mem_filter.mp hθ).1
        have hθgt : (dirList S).get i < θ := (Finset.mem_filter.mp hθ).2
        rcases (List.mem_iff_get.mp ((dirList_mem_iff S θ).mpr hθf1)) with ⟨j, rfl⟩
        have hij : i.val < j.val := index_lt_of_get_lt S hθgt
        have hiy : i.val + 1 ≤ j.val := by omega
        exact dirList_get_mono S (i := ⟨i.val + 1, hi⟩) (j := j) hiy)
  dsimp [f, y, hne]
  exact hmin

/-- **No direction strictly between consecutive entries.**  If entry `i` is
not the last, no direction lies strictly between it and entry `i + 1`. -/
theorem no_dir_between_get (S : Finset ℂ) (i : Fin (dirList S).length)
    (hi : i.val + 1 < (dirList S).length) :
    ∀ θ ∈ dirSet S,
      ¬ ((dirList S).get i < θ ∧ θ < (dirList S).get ⟨i.val + 1, hi⟩) := by
  classical
  intro θ hθ hθmid
  rcases (List.mem_iff_get.mp ((dirList_mem_iff S θ).mpr hθ)) with ⟨j, rfl⟩
  have hij : i.val < j.val := index_lt_of_get_lt S hθmid.1
  have hji : j.val < i.val + 1 := by
    by_contra hnot
    have hge : i.val + 1 ≤ j.val := le_of_not_gt hnot
    have hm := dirList_get_mono S (i := ⟨i.val + 1, hi⟩) (j := j) hge
    linarith
  omega

/-- The last entry has no direction strictly above it.  (Needs at least one
direction, so the last entry exists.) -/
theorem last_get_no_above (S : Finset ℂ) (hne : (dirSet S).Nonempty) :
    ∀ θ ∈ dirSet S,
      ¬ ((dirList S).get ⟨(dirList S).length - 1, by
          have hl : 0 < (dirList S).length := by
            rw [dirList_length]
            exact Finset.card_pos.mpr hne
          omega⟩ < θ) := by
  classical
  intro θ hθ hθgt
  rcases (List.mem_iff_get.mp ((dirList_mem_iff S θ).mpr hθ)) with ⟨j, rfl⟩
  have hl : 0 < (dirList S).length := by
    rw [dirList_length]
    exact Finset.card_pos.mpr hne
  have hjj : (dirList S).length - 1 < j.val :=
    index_lt_of_get_lt S hθgt
  omega

end Submission.DirCycle

end
