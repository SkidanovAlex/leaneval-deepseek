import Mathlib
import Submission.Work.ConvR.basic
import Submission.Work.Kernel.Raw

/-!
# `listProdB`: shared definitions

Vocabulary for the word computing the product of a list of natural numbers (encoded as
`HvdH.intList ts`), the lemma `Work.ConvR.listProdB`.

## The program

The list sits on top of the value stack as the `cons`-chain `ofList (intVals ts)`; the running
product is the value just below it.  One iteration of the walk

* peeks the head glyph of stack 0 — this is `Glyph.cons` exactly when the list is nonempty and
  `Glyph.nil` exactly when it is empty, because `Val.enc` remembers the constructor;
* if it is `Glyph.nil`, pops it (the value stack becomes `int P :: rest`) and sets the loop
  register to `gStop`;
* otherwise pops the `cons` glyph, exposing `int t :: ofList (intVals rem) :: int P :: rest`,
  rolls the accumulator `int P` above `int t`, multiplies (`mulS`), swaps the result back below
  the remaining list and sets the loop register to `gCont`.

The loop is `Cmd.loop rLoop gCont`, so it terminates precisely when the list is exhausted, and its
cost is the *sum* of the (non-uniform) per-iteration costs — see `loopCost`.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-! ## Registers and glyphs -/

/-- register holding the head glyph of stack 0 -/
abbrev rHead : Reg := 0
/-- scratch register of the `pop`s -/
abbrev rPop : Reg := 2
/-- the loop register -/
abbrev rLoop : Reg := 1

/-- flag: run one more iteration -/
def gCont : Glyph := .mk 0

/-- flag: stop -/
def gStop : Glyph := .mk 1

theorem gCont_ne_gStop : gCont ≠ gStop := by decide

theorem gStop_ne_gCont : gStop ≠ gCont := by decide

/-! ## The program -/

/-- One iteration of the walk over the list. -/
def bodyProg (rp mp sp : Cmd) : Cmd :=
  .seq (.peek 0 rHead)
    (.ite rHead Glyph.nil
      (.seq (.pop 0 rPop) (.set rLoop gStop))
      (.seq (.pop 0 rPop) (.seq rp (.seq mp (.seq sp (.set rLoop gCont))))))

/-- The walk. -/
def loopProg (rp mp sp : Cmd) : Cmd := .loop rLoop gCont (bodyProg rp mp sp)

/-- Push the initial accumulator `int 1`, swap it below the list, set the loop flag, then walk. -/
def fullProg (pushP swP lp : Cmd) : Cmd :=
  .seq pushP (.seq swP (.seq (.set rLoop gCont) lp))

/-! ## Sizes and costs -/

/-- The list of values encoding a list of naturals. -/
def intVals (ts : List ℕ) : List Val := ts.map fun n => Val.int (n : ℤ)

/-- Encoding size of a remaining list. -/
def SZrem (rem : List ℕ) : ℕ := vsz (ofList (intVals rem))

/-- Cost of one iteration of the loop, with head element `t`, remaining tail `rem` and
accumulator `P`: `peek` + `ite` test + `pop` + `set` (4 primitives) + `roll 2` + `mulS` + `swap`. -/
def stepCost (Kr Km Ks : ℕ) (t : ℕ) (rem : List ℕ) (P : ℕ) : ℕ :=
  4 + Kr * 3 * (isz (t : ℤ) + SZrem rem + isz (P : ℤ) + 1)
    + Km * isz (P : ℤ) * isz (t : ℤ)
    + Ks * (isz ((P * t : ℕ) : ℤ) + SZrem rem + 1)

/-- Cost of the whole loop on the remaining list `rem` with accumulator `P`. -/
def loopCost (Kr Km Ks : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 7
  | t :: rem, P => stepCost Kr Km Ks t rem P + loopCost Kr Km Ks rem (P * t) + 1

/-- The constant of the final cost bound. -/
def Kconst (Kp Kr Km Ks : ℕ) : ℕ := 4 * Kp + 1 + 4 * Ks + 19200 * (Kr + Km + Ks + 1)

/-! ## Specifications of the component words -/

/-- The `roll 2` of `KernelLib` with its cost written out. -/
def IsRoll2 (main p : Cmd) (Kr : ℕ) : Prop :=
  WordR main p (fun vs => 2 < vs.length)
    (fun vs out => out = vs.getD 2 .nil :: vs.eraseIdx 2)
    (fun vs => Kr * 3 * (((vs.take 3).map vsz).sum + 1))

/-- The schoolbook product of `IntLib` with its cost written out. -/
def IsMul (main p : Cmd) (Km : ℕ) : Prop :=
  BinOp main p (fun _ _ => True) (· * ·) (fun a b => Km * isz a * isz b)

/-- The `swap` of `KernelLib` with its cost written out. -/
def IsSwap (main p : Cmd) (Ks : ℕ) : Prop :=
  WordR main p (fun vs => 2 ≤ vs.length)
    (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
    (fun vs => Ks * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))

/-- Pushing the constant `int 1`. -/
def IsPushOne (main p : Cmd) (Kp : ℕ) : Prop :=
  WordR main p (fun _ => True) (fun vs out => out = Val.int 1 :: vs)
    (fun _ => Kp * (vsz (Val.int 1) + 1))

/-! ## Basic size lemmas -/

theorem isz_one : isz 1 = 3 := by decide

theorem isz_natCast (n : ℕ) : isz (n : ℤ) = n.size + 2 := by
  simp [isz]

theorem isz_nonneg (z : ℤ) : 2 ≤ isz z := by simp [isz]

/-- `isz` is submultiplicative. -/
theorem isz_mul_le (a b : ℤ) : isz (a * b) ≤ isz a + isz b := by
  have h : ((a * b).natAbs).size ≤ (a.natAbs).size + (b.natAbs).size := by
    rw [Int.natAbs_mul]
    by_cases ha : a.natAbs = 0
    · simp [ha]
    · by_cases hb : b.natAbs = 0
      · simp [hb]
      · rw [Nat.size_le, Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self _) (Nat.lt_size_self _)
  simp only [isz]
  omega

theorem vsz_intList_eq (ts : List ℕ) :
    vsz (intList ts) = ((ts.map fun t => isz (t : ℤ)).sum) + ts.length + 1 := by
  induction ts with
  | nil => simp [intList, ofList, vsz, Val.enc]
  | cons t ts ih =>
    have e : vsz (intList (t :: ts)) = vsz (Val.int (t : ℤ)) + vsz (intList ts) + 1 := by
      rw [show intList (t :: ts) = Val.cons (Val.int (t : ℤ)) (intList ts) from rfl, vsz_cons]
    rw [e, vsz_int, ih]
    simp [List.sum_cons]
    ring

theorem SZrem_eq (rem : List ℕ) :
    SZrem rem = ((rem.map fun t => isz (t : ℤ)).sum) + rem.length + 1 :=
  vsz_intList_eq rem

theorem intList_eq_ofList (ts : List ℕ) : intList ts = ofList (intVals ts) := rfl

theorem vsz_intList_eq_SZrem (ts : List ℕ) : vsz (intList ts) = SZrem ts := rfl


/-! ## Encoding lemmas -/

theorem encs_cons (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := by
  simp [encs]

theorem enc_nil : (Val.nil).enc = [Glyph.nil] := rfl

theorem enc_cons (a b : Val) : (Val.cons a b).enc = Glyph.cons :: (a.enc ++ b.enc) := rfl

theorem enc_ofList_intVals_cons (t : ℕ) (rem : List ℕ) :
    (ofList (intVals (t :: rem))).enc =
      Glyph.cons :: ((Val.int (t : ℤ)).enc ++ (ofList (intVals rem)).enc) := rfl

theorem ofList_intVals_cons (t : ℕ) (rem : List ℕ) :
    ofList (intVals (t :: rem)) = Val.cons (Val.int (t : ℤ)) (ofList (intVals rem)) := rfl

theorem ofList_intVals_nil : ofList (intVals ([] : List ℕ)) = Val.nil := rfl

/-- In the "nonempty list" case the head glyph of stack 0 is `cons`. -/
theorem headD_stack_cons (t : ℕ) (rem : List ℕ) (Q : ℕ) (rest : List Val) (R : List Glyph)
    (g : Glyph) :
    (encs (ofList (intVals (t :: rem)) :: Val.int (Q : ℤ) :: rest) ++ R).headD g = Glyph.cons := by
  rw [encs_cons, enc_ofList_intVals_cons]
  rfl

/-- In the "empty list" case the head glyph of stack 0 is `nil`. -/
theorem headD_stack_nil (Q : ℕ) (rest : List Val) (R : List Glyph) (g : Glyph) :
    (encs (Val.nil :: Val.int (Q : ℤ) :: rest) ++ R).headD g = Glyph.nil := by
  rw [encs_cons, enc_nil]
  rfl

/-- The stack after popping the `cons` glyph of `ofList (v :: vs)`. -/
theorem tail_cons_stack (t : ℕ) (rem : List ℕ) (Q : ℕ) (rest : List Val) (R : List Glyph) :
    (encs (ofList (intVals (t :: rem)) :: Val.int (Q : ℤ) :: rest) ++ R).tail =
      encs (Val.int (t : ℤ) :: ofList (intVals rem) :: Val.int (Q : ℤ) :: rest) ++ R := by
  simp only [encs_cons, enc_ofList_intVals_cons, List.cons_append, List.tail_cons, List.nil_append,
    List.append_assoc]

/-- The stack after popping the `nil` glyph. -/
theorem tail_nil_stack (Q : ℕ) (rest : List Val) (R : List Glyph) :
    (encs (Val.nil :: Val.int (Q : ℤ) :: rest) ++ R).tail = encs (Val.int (Q : ℤ) :: rest) ++ R := by
  simp only [encs_cons, enc_nil, List.cons_append, List.tail_cons, List.nil_append,
    List.append_assoc]

/-! ## List arithmetic used by the `roll 2` step -/

theorem eraseIdx_two (a b c : Val) (rest : List Val) :
    (a :: b :: c :: rest).eraseIdx 2 = a :: b :: rest := by
  simp [List.eraseIdx]

theorem getD_two (a b c : Val) (rest : List Val) (d : Val) :
    (a :: b :: c :: rest).getD 2 d = c := by
  simp

theorem take_three_sum (a b c : Val) (rest : List Val) :
    (((a :: b :: c :: rest).take 3).map vsz).sum = vsz a + vsz b + vsz c := by
  simp
  omega

theorem vsz_intVals_ofList_rem (rem : List ℕ) :
    vsz (ofList (intVals rem)) = SZrem rem := rfl

theorem intList_cons_eq (t : ℕ) (rem : List ℕ) :
    intList (t :: rem) = Val.cons (Val.int (t : ℤ)) (intList rem) := rfl

theorem intList_nil : intList ([] : List ℕ) = Val.nil := rfl

end Work.ConvR
