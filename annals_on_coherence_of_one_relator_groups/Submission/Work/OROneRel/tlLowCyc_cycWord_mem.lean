/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The cycle word lies in the low window subgroup

The *low window* of the two-letter band `a^p b^q` (weight `tlW p q`: `a ↦ q`, `b ↦ -p`) is the
interval `[0, p+q-1]` of levels, and the *cycle word* `cycWord p q = a^p b^q` (the word of the full
cycle through the `p+q` levels) is the canonical generator of the window subgroup
`tlWin p q (p+q-1)`.

Here we prove the generator part: the cycle word lies in the window subgroup.  This is the
*generation* half of the identification `tlWin p q (p+q-1) = zpowers (cycWord p q)`; it needs no
coprimality hypothesis, only `p, q ≥ 1`.

The proof is a direct verification of the two conditions in the definition of `tlWin`
(closure of the set of words of weight `0` whose decorated walk stays in the window):

* the cycle word is spelled by `cycList p q = cycFwdList p q 0 (p+q)`, whose weight is
  `cycLevel p q (p+q) - cycLevel p q 0 = 0` (the cycle closes up), and
* the decorated walk of `cycList p q` visits exactly the levels `cycLevel p q j` (`0 ≤ j < p+q`),
  all of which lie in the window; at each of them the traversed letter is the (unique) outgoing
  window edge by `letter_pos_winE`.
-/
import Mathlib
import Submission.Work.OROneRel.tlLowCycStep
import Submission.Work.OROneRel.band_hnnConjMap_injective

namespace Work.OROneRel

/-! ## The edges of the cycle lie in the window -/

/-- **The edge of the cycle at index `j` is an edge of the low window.**  Its source level
`cycLevel p q j` lies in `[0, p+q-1]` by `cycLevel_bounds`, and at that level the letter
`cycLetter p q j = cycGen p q (cycLevel p q j)` is the unique outgoing window edge
(`letter_pos_winE`). -/
theorem cycLetter_level_mem_winE (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (j : ℤ) :
    (cycLetter p q j, cycLevel p q j) ∈
      winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1) := by
  have hb := cycLevel_bounds p q hp j
  have hb' : cycLevel p q j ≤ (p : ℤ) + (q : ℤ) - 1 := by
    have h2 := hb.2
    simp only [tlN] at h2
    linarith
  rw [letter_pos_winE p q hp hq hb.1 hb', cycGen_cycLevel]

/-! ## The cycle word as a forward cycle prefix -/

/-- The word of the cycle is the forward cycle prefix of length `p+q` starting at the index `0`. -/
theorem cycList_eq_cycFwdList (p q : ℕ) : cycList p q = cycFwdList p q 0 (p + q) := by
  rw [cycList, cycFwdList_zero_shift]

/-- **The weight of the cycle word vanishes**: the cycle closes up, i.e.
`cycLevel p q (p+q) = cycLevel p q 0 = 0`. -/
theorem lsig_cycList (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    lsig (tlW p q) (cycList p q) = 0 := by
  rw [cycList_eq_cycFwdList, lsig_cycFwdList p q hp hq 0 (p + q)]
  have h : cycLevel p q (0 + ((p + q : ℕ) : ℤ)) = 0 := by
    rw [← tlN_cast, cycLevel_periodic, cycLevel_zero]
  rw [h, cycLevel_zero]
  ring

/-! ## The decorated walk of the cycle -/

/-- **The decorated walk of the cycle word**: the `j`-th decorated letter is the cycle edge at the
index `j`, read at the level `cycLevel p q j`. -/
theorem decor_cycList (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    decor (tlW p q) 0 (cycList p q)
      = (List.range (p + q)).map
          (fun j : ℕ => ((cycLetter p q (j : ℤ), cycLevel p q (j : ℤ)), true)) := by
  have h := decor_cycFwdList p q hp hq 0 (p + q)
  simp only [cycLevel_zero, zero_add] at h
  rw [cycList_eq_cycFwdList]
  exact h

/-- **The decorated walk of the cycle word stays in the low window.**  Every decorated letter of
`cycList p q` is a cycle edge `(cycLetter p q j, cycLevel p q j)`, which lies in the window by
`cycLetter_level_mem_winE`. -/
theorem cycList_walk (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ e ∈ decor (tlW p q) 0 (cycList p q),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1) := by
  intro e he
  rw [decor_cycList p q hp hq] at he
  obtain ⟨j, -, hj⟩ := List.mem_map.mp he
  rw [← hj]
  exact cycLetter_level_mem_winE p q hp hq (j : ℤ)

/-! ## The cycle word is a window generator -/

/-- **The cycle word lies in the low window subgroup** `tlWin p q (p+q-1)`: the spelling word
`cycList p q` has weight `0` (`lsig_cycList`) and its decorated walk stays in the window
(`cycList_walk`), so `cycWord p q` belongs to the generating set of `tlWin p q (p+q-1)`. -/
theorem tlLowCyc_cycWord_mem (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Work.OROneRel.cycWord p q ∈ Work.OROneRel.tlWin p q ((p : ℤ) + (q : ℤ) - 1) := by
  rw [tlWin]
  exact Subgroup.subset_closure
    ⟨cycList p q, rfl, lsig_cycList p q hp hq, cycList_walk p q hp hq⟩

end Work.OROneRel
