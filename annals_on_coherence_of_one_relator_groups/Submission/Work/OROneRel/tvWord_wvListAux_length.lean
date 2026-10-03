import Mathlib
import Submission.Work.OROneRel.transvectionNielsenDefs

namespace Work.OROneRel

/-- The length of `wvListAux` is determined by `L` alone: it is the number of letters of `L`
whose first component differs from `t` (the `t`-letters are deleted).  In particular the running
index `i` is irrelevant for the length. -/
theorem wvListAux_length_eq_filter {α : Type*} [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ)
    (L : List (α × Bool)) :
    (Work.OROneRel.wvListAux c t i L).length
      = (L.filter (fun p => decide (p.1 ≠ t))).length := by
  induction L generalizing i with
  | nil => simp [Work.OROneRel.wvListAux]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [show Work.OROneRel.wvListAux c t i ((a, false) :: L) =
            (if h : a = t then [] else [((⟨a, h⟩, i - c a), false)])
              ++ Work.OROneRel.wvListAux c t (i - c a) L from rfl,
          List.length_append, ih (i - c a)]
      by_cases ha : a = t
      · subst ha; simp
      · rw [dif_neg ha, List.length_singleton, List.filter_cons_of_pos, List.length_cons]
        · omega
        · simp [ha]
    · rw [show Work.OROneRel.wvListAux c t i ((a, true) :: L) =
            (if h : a = t then [] else [((⟨a, h⟩, i), true)])
              ++ Work.OROneRel.wvListAux c t (i + c a) L from rfl,
          List.length_append, ih (i + c a)]
      by_cases ha : a = t
      · subst ha; simp
      · rw [dif_neg ha, List.length_singleton, List.filter_cons_of_pos, List.length_cons]
        · omega
        · simp [ha]

/-- Filtering `tvBlk m` (whose first letter is the deleted symbol `(0, true)`) leaves exactly the
`m.natAbs` letters `(1, false)`. -/
theorem tvBlk_filter (m : ℤ) :
    (Work.OROneRel.tvBlk m).filter (fun p => decide (p.1 ≠ (0 : Fin 2)))
      = List.replicate m.natAbs ((1 : Fin 2), false) := by
  simp [Work.OROneRel.tvBlk]

/-- The number of non-`0` letters of `tvWord p q m`, i.e. the length of its image under
`wvListAux c 0`. -/
theorem tvWord_filter_length (p q : ℕ) (m : ℤ) :
    ((Work.OROneRel.tvWord p q m).filter (fun x => decide (x.1 ≠ (0 : Fin 2)))).length
      = (p - 1) * m.natAbs + (m + (q : ℤ)).toNat := by
  rw [Work.OROneRel.tvWord, List.filter_append, List.length_append, List.filter_flatten,
      List.length_flatten, List.map_replicate, List.map_replicate, List.sum_replicate,
      nsmul_eq_mul, tvBlk_filter, List.length_replicate]
  simp

theorem tvWord_wvListAux_length (p q : ℕ) (m : ℤ) (c : Fin 2 → ℤ) :
    (Work.OROneRel.wvListAux c 0 0 (Work.OROneRel.tvWord p q m)).length
      = (p - 1) * m.natAbs + (m + (q : ℤ)).toNat := by
  rw [wvListAux_length_eq_filter c 0 0 (Work.OROneRel.tvWord p q m)]
  exact tvWord_filter_length p q m

end Work.OROneRel
