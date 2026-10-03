import Mathlib
import Submission.Work.OROneRel.wgtMMDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- `lsig` of a cons, in the `false` case. -/
private theorem lsig_cons_false' (c : α → ℤ) (a : α) (M : List (α × Bool)) :
    lsig c ((a, false) :: M) = -c a + lsig c M := rfl

/-- `lsig` of a cons, in the `true` case. -/
private theorem lsig_cons_true' (c : α → ℤ) (a : α) (M : List (α × Bool)) :
    lsig c ((a, true) :: M) = c a + lsig c M := rfl

theorem wvListAuxAppend {α : Type u} [DecidableEq α] (c : α → ℤ) (t : α) (i : ℤ)
    (M L : List (α × Bool)) :
    Work.OROneRel.wvListAux c t i (M ++ L)
      = Work.OROneRel.wvListAux c t i M
        ++ Work.OROneRel.wvListAux c t (i + Work.OROneRel.lsig c M) L := by
  induction M generalizing i with
  | nil => simp [wvListAux, lsig]
  | cons p M ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [List.cons_append,
        show wvListAux c t i ((a, false) :: (M ++ L)) =
          (if h : a = t then [] else [((⟨a, h⟩, i - c a), false)])
            ++ wvListAux c t (i - c a) (M ++ L) from rfl,
        show wvListAux c t i ((a, false) :: M) =
          (if h : a = t then [] else [((⟨a, h⟩, i - c a), false)])
            ++ wvListAux c t (i - c a) M from rfl,
        lsig_cons_false' c a M,
        ih (i - c a),
        show i + (-c a + lsig c M) = (i - c a) + lsig c M from by ring,
        List.append_assoc]
    · rw [List.cons_append,
        show wvListAux c t i ((a, true) :: (M ++ L)) =
          (if h : a = t then [] else [((⟨a, h⟩, i), true)])
            ++ wvListAux c t (i + c a) (M ++ L) from rfl,
        show wvListAux c t i ((a, true) :: M) =
          (if h : a = t then [] else [((⟨a, h⟩, i), true)])
            ++ wvListAux c t (i + c a) M from rfl,
        lsig_cons_true' c a M,
        ih (i + c a),
        show i + (c a + lsig c M) = (i + c a) + lsig c M from by ring,
        List.append_assoc]

end Work.OROneRel
