import Mathlib
import Submission.Work.Layout.MergeDefs

set_option autoImplicit false

/-!
# Shadow recursions for the merge cost

`mrgCost` accumulates, over the comparison steps of the greedy merge of two keyed runs `P` and `Q`,
the per-step charge

`mrgStep = cCmp * (comparison term) + cMov * (move term) + cExp * (exposure term) + cK`.

Isolating each summand as a recursion with the *same* shape as `mrgCost` lets each be estimated
separately: `mrgCmp` is (a multiple of) `cmpCost` of the key lists, `mrgMov` charges each moved
record exactly once, `mrgExp` charges the record exposed by a move, and `mrgTs` counts the steps.
-/

namespace Work.Layout

open HvdH

/-- size of the head of a list of values, with `vsz Val.nil` for the empty list -/
def vszHead (L : List Val) : ℕ := vsz (L.headD Val.nil)

@[simp] theorem vszHead_cons (v : Val) (vs : List Val) : vszHead (v :: vs) = vsz v := by
  simp [vszHead]

@[simp] theorem vszHead_nil : vszHead ([] : List Val) = vsz Val.nil := by
  simp [vszHead]

theorem vsz_nil : vsz Val.nil = 1 := by decide

theorem vszHead_le_sum (L : List Val) : vszHead L ≤ (L.map vsz).sum + 2 := by
  cases L with
  | nil => decide
  | cons v vs => simp only [vszHead_cons, List.map_cons, List.sum_cons]; omega

/-- the comparison part of `mrgCost` (one summand per comparison step) -/
def mrgCmp : List Val → List Val → ℕ
  | p :: ps, q :: qs => ((keyOf p).size).size + ((keyOf q).size).size + 4 +
      (if keyOf q < keyOf p then mrgCmp (p :: ps) qs else mrgCmp ps (q :: qs))
  | _, _ => 0

/-- the move part of `mrgCost` (the moved record plus one unit of step overhead) -/
def mrgMov : List Val → List Val → ℕ
  | p :: ps, q :: qs => (vsz (if keyOf q < keyOf p then q else p) + 1) +
      (if keyOf q < keyOf p then mrgMov (p :: ps) qs else mrgMov ps (q :: qs))
  | _, _ => 0

/-- the exposure part of `mrgCost` (the head exposed by the move, plus two units) -/
def mrgExp : List Val → List Val → ℕ
  | p :: ps, q :: qs =>
      (if keyOf q < keyOf p then vszHead qs + 2 else vszHead ps + 2) +
      (if keyOf q < keyOf p then mrgExp (p :: ps) qs else mrgExp ps (q :: qs))
  | _, _ => 0

/-- the number of comparison steps of `mrgCost` -/
def mrgTs : List Val → List Val → ℕ
  | p :: ps, q :: qs => 1 + (if keyOf q < keyOf p then mrgTs (p :: ps) qs else mrgTs ps (q :: qs))
  | _, _ => 0

@[simp] theorem mrgCmp_cons (p : Val) (ps : List Val) (q : Val) (qs : List Val) :
    mrgCmp (p :: ps) (q :: qs) =
      ((keyOf p).size).size + ((keyOf q).size).size + 4 +
        (if keyOf q < keyOf p then mrgCmp (p :: ps) qs else mrgCmp ps (q :: qs)) := by
  rw [mrgCmp.eq_def]

@[simp] theorem mrgCmp_nil_left (Q : List Val) : mrgCmp [] Q = 0 := by
  cases Q <;> rw [mrgCmp.eq_def]

@[simp] theorem mrgCmp_nil_right (P : List Val) : mrgCmp P [] = 0 := by
  cases P <;> rw [mrgCmp.eq_def]

@[simp] theorem mrgMov_cons (p : Val) (ps : List Val) (q : Val) (qs : List Val) :
    mrgMov (p :: ps) (q :: qs) =
      (vsz (if keyOf q < keyOf p then q else p) + 1) +
        (if keyOf q < keyOf p then mrgMov (p :: ps) qs else mrgMov ps (q :: qs)) := by
  rw [mrgMov.eq_def]

@[simp] theorem mrgMov_nil_left (Q : List Val) : mrgMov [] Q = 0 := by
  cases Q <;> rw [mrgMov.eq_def]

@[simp] theorem mrgMov_nil_right (P : List Val) : mrgMov P [] = 0 := by
  cases P <;> rw [mrgMov.eq_def]

@[simp] theorem mrgExp_cons (p : Val) (ps : List Val) (q : Val) (qs : List Val) :
    mrgExp (p :: ps) (q :: qs) =
      (if keyOf q < keyOf p then vszHead qs + 2 else vszHead ps + 2) +
        (if keyOf q < keyOf p then mrgExp (p :: ps) qs else mrgExp ps (q :: qs)) := by
  rw [mrgExp.eq_def]

@[simp] theorem mrgExp_nil_left (Q : List Val) : mrgExp [] Q = 0 := by
  cases Q <;> rw [mrgExp.eq_def]

@[simp] theorem mrgExp_nil_right (P : List Val) : mrgExp P [] = 0 := by
  cases P <;> rw [mrgExp.eq_def]

@[simp] theorem mrgTs_cons (p : Val) (ps : List Val) (q : Val) (qs : List Val) :
    mrgTs (p :: ps) (q :: qs) =
      1 + (if keyOf q < keyOf p then mrgTs (p :: ps) qs else mrgTs ps (q :: qs)) := by
  rw [mrgTs.eq_def]

@[simp] theorem mrgTs_nil_left (Q : List Val) : mrgTs [] Q = 0 := by
  cases Q <;> rw [mrgTs.eq_def]

@[simp] theorem mrgTs_nil_right (P : List Val) : mrgTs P [] = 0 := by
  cases P <;> rw [mrgTs.eq_def]

end Work.Layout
