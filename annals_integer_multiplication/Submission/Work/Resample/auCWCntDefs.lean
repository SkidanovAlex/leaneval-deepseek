import Mathlib
import Submission.Work.Resample.auCWDefs

/-!
# Definitions for the record-counting word `Work.Resample.auCWExtract`

The carry record of one round is `awRec zr zi = ofList ((if zr = 1 then [.int 1] else []) ++
(if zi = 1 then [.int 2] else []))` (`zr, zi ∈ {0,1}`), so a record has a marker `.int 1` exactly
when `zr = 1` and a marker `.int 2` exactly when `zi = 1`.

Counting the markers of one type in the chain `ofList (qs.map (awRec ·.1 ·.2))` is done by

* replacing every record `x` by the (small) value `awSub1 x = ofList (awF1 x)`, whose elements are
  exactly the `.int 1` markers of `x`,
* `flatten`-ing the resulting list of small lists, which gives a list of `awCnt1 qs` ones,
* reading off its length.

This file collects the definitions and their elementary (concrete-value) properties.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## The per-record maps -/

/-- The `.int 1` markers of a record, as a list of values. -/
def awF1 : Val → List Val := fun x => if x = awRec 1 0 ∨ x = awRec 1 1 then [Val.int 1] else []

/-- The `.int 2` markers of a record, as a list of values. -/
def awF2 : Val → List Val := fun x => if x = awRec 0 1 ∨ x = awRec 1 1 then [Val.int 2] else []

/-- The restriction of a record to its `.int 1` markers. -/
def awSub1 (x : Val) : Val := ofList (awF1 x)

/-- The restriction of a record to its `.int 2` markers. -/
def awSub2 (x : Val) : Val := ofList (awF2 x)

/-- The number of records of `qs` whose first coordinate is `1`. -/
def awCnt1 (qs : List (ℤ × ℤ)) : ℕ := (qs.map fun q => if q.1 = 1 then 1 else 0).sum

/-- The number of records of `qs` whose second coordinate is `1`. -/
def awCnt2 (qs : List (ℤ × ℤ)) : ℕ := (qs.map fun q => if q.2 = 1 then 1 else 0).sum

theorem awSub1_eq (x : Val) : awSub1 x = ofList (awF1 x) := rfl
theorem awSub2_eq (x : Val) : awSub2 x = ofList (awF2 x) := rfl

/-! ## The concrete values -/

theorem awRec_zero_zero : awRec 0 0 = Val.nil := rfl
theorem awRec_one_zero : awRec 1 0 = Val.cons (Val.int 1) Val.nil := rfl
theorem awRec_zero_one : awRec 0 1 = Val.cons (Val.int 2) Val.nil := rfl
theorem awRec_one_one : awRec 1 1 = Val.cons (Val.int 1) (Val.cons (Val.int 2) Val.nil) := rfl

theorem awF1_awRec {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    awF1 (awRec zr zi) = if zr = 1 then [Val.int 1] else [] := by
  unfold awF1
  rcases hzr with h | h <;> rcases hzi with h2 | h2 <;>
    · subst h; subst h2; decide +kernel

theorem awF2_awRec {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    awF2 (awRec zr zi) = if zi = 1 then [Val.int 2] else [] := by
  unfold awF2
  rcases hzr with h | h <;> rcases hzi with h2 | h2 <;>
    · subst h; subst h2; decide +kernel

theorem awSub1_awRec {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    awSub1 (awRec zr zi) = ofList (if zr = 1 then [Val.int 1] else []) := by
  rw [awSub1_eq, awF1_awRec hzr hzi]

theorem awSub2_awRec {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    awSub2 (awRec zr zi) = ofList (if zi = 1 then [Val.int 2] else []) := by
  rw [awSub2_eq, awF2_awRec hzr hzi]

theorem awF1_length_awRec {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    (awF1 (awRec zr zi)).length = if zr = 1 then 1 else 0 := by
  rw [awF1_awRec hzr hzi]
  split <;> simp

theorem awF2_length_awRec {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    (awF2 (awRec zr zi)).length = if zi = 1 then 1 else 0 := by
  rw [awF2_awRec hzr hzi]
  split <;> simp

theorem vsz_awRec_le {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    vsz (awRec zr zi) ≤ 12 := by
  rcases hzr with h | h <;> rcases hzi with h2 | h2 <;>
    · subst h; subst h2; decide +kernel

theorem vsz_awSub1_le {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    vsz (awSub1 (awRec zr zi)) ≤ 12 := by
  rcases hzr with h | h <;> rcases hzi with h2 | h2 <;>
    · subst h; subst h2; decide +kernel

theorem vsz_awSub2_le {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    vsz (awSub2 (awRec zr zi)) ≤ 12 := by
  rcases hzr with h | h <;> rcases hzi with h2 | h2 <;>
    · subst h; subst h2; decide +kernel

/-! ## The sums -/

/-- The natural-number count of `.1 = 1` casts to the integer sum used in the statement. -/
theorem awCnt1_cast (qs : List (ℤ × ℤ)) :
    ((awCnt1 qs : ℕ) : ℤ) = (qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum := by
  unfold awCnt1
  induction qs with
  | nil => simp
  | cons q t ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    split <;> push_cast <;> ring

/-- The natural-number count of `.2 = 1` casts to the integer sum used in the statement. -/
theorem awCnt2_cast (qs : List (ℤ × ℤ)) :
    ((awCnt2 qs : ℕ) : ℤ) = (qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum := by
  unfold awCnt2
  induction qs with
  | nil => simp
  | cons q t ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    split <;> push_cast <;> ring

end Work.Resample
