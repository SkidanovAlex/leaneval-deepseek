import Mathlib
import Submission.Work.OROneRel.wgtMMDefs

universe u

namespace Work.OROneRel

/-!
# The decorated word of a repetition

`wvListAux c t i L` is the decorated word of `L` with the `t`-symbols deleted: the symbol `(x, true)`
read at running weight `i` becomes `((x, i), true)`, and `(x, false)` becomes `((x, i - c x), false)`,
while `t`-symbols are dropped and do not change the running weight `i`.

The main point of this file: if `L` has total weight `lsig c L = 0`, then a concatenation of `l`
copies of `L` produces `l` identical blocks, i.e. the decorated word of `L ^ l` is the repetition of
the decorated word of `L`.  Everything is proved here from scratch (the append rule for `wvListAux`
included) so that the file is self-contained.
-/

variable {α : Type u}

/-! ## Elementary behaviour of `lsig` -/

private theorem wvRep_lsig_nil (c : α → ℤ) : lsig c ([] : List (α × Bool)) = 0 := by
  simp [lsig]

private theorem wvRep_lsig_cons_true (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, true) :: L) = c a + lsig c L := by
  simp [lsig]

private theorem wvRep_lsig_cons_false (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, false) :: L) = -c a + lsig c L := by
  simp [lsig]

/-! ## The recursion equations of `wvListAux` -/

private theorem wvRep_wvListAux_nil [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ) :
    wvListAux c t i ([] : List (α × Bool)) = [] := rfl

private theorem wvRep_wvListAux_cons_true [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    wvListAux c t i ((a, true) :: L) =
      (if h : a = t then [] else [((⟨a, h⟩, i), true)]) ++ wvListAux c t (i + c a) L := rfl

private theorem wvRep_wvListAux_cons_false [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ) (a : α)
    (L : List (α × Bool)) :
    wvListAux c t i ((a, false) :: L) =
      (if h : a = t then [] else [((⟨a, h⟩, i - c a), false)]) ++ wvListAux c t (i - c a) L := rfl

/-! ## The append rule -/

/-- Concatenation rule for the decorated word: the first block is decorated at the running weight
`i`, the second at the running weight `i + lsig c M`. -/
private theorem wvRep_wvListAux_append [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ)
    (M L : List (α × Bool)) :
    wvListAux c t i (M ++ L) = wvListAux c t i M ++ wvListAux c t (i + lsig c M) L := by
  induction M generalizing i with
  | nil =>
      simp only [List.nil_append, wvRep_wvListAux_nil, wvRep_lsig_nil, add_zero]
  | cons p M ih =>
      obtain ⟨a, b⟩ := p
      cases b
      · rw [List.cons_append, wvRep_wvListAux_cons_false, wvRep_wvListAux_cons_false, ih (i - c a),
          List.append_assoc, wvRep_lsig_cons_false]
        rw [show (i - c a) + lsig c M = i + (-c a + lsig c M) by ring]
      · rw [List.cons_append, wvRep_wvListAux_cons_true, wvRep_wvListAux_cons_true, ih (i + c a),
          List.append_assoc, wvRep_lsig_cons_true]
        rw [show (i + c a) + lsig c M = i + (c a + lsig c M) by ring]

/-! ## The main lemma -/

/-- **The decorated word of a repetition.**  If the total weight of `L` vanishes, then the
decorated word of `L` concatenated `l` times is the `l`-fold repetition of the decorated word of
`L`: every copy of `L` restarts at the same running weight `i`. -/
theorem wvListAuxFlattenReplicate {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ)
    (L : List (α × Bool)) (l : ℕ) (hL : Work.OROneRel.lsig c L = 0) :
    Work.OROneRel.wvListAux c t i (List.flatten (List.replicate l L))
      = List.flatten (List.replicate l (Work.OROneRel.wvListAux c t i L)) := by
  induction l with
  | zero =>
      simp only [List.replicate_zero, List.flatten_nil]
      exact wvRep_wvListAux_nil c t i
  | succ l ih =>
      rw [List.replicate_succ, List.flatten_cons, wvRep_wvListAux_append, hL, add_zero, ih,
        List.replicate_succ, List.flatten_cons]

end Work.OROneRel
