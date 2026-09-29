import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move

/-!
# Layout area: definitions for `LayoutLib.enumerate`

The enumerate word labels `xs[i]` by `cons (int i) xs[i]`.  The list is moved to a scratch stack
(stack 1) and the walk keeps a binary counter `int i` on top of the value stack (stack 0); per
element the counter is *copied* (`dupVal`), the copy is incremented (`IntLib.add` with `int 1`) and
the old value is used as the label.  The labelled element is consed onto an accumulator list
(stack 5); the accumulator is reversed at the very end.

This file contains only definitions and small, self-contained lemmas; the words themselves are
proved in `Submission/Work/Layout/enumInc.lean` (`dupVal`, `incDup`) and
`Submission/Work/Layout/enumDrop.lean` (`dropVal`).
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## Registers and constant pushes -/

/-- loop-flag register of the enumerate loop (`≠ 0..4`, the registers used by the movers) -/
def rEn : Reg := 5

/-- push `int 1` on stack 0 (encoding `pos :: bit true :: iend`) -/
def pushIntOne : Cmd :=
  seqs [pushConst 0 Glyph.iend, pushConst 0 (Glyph.bit true), pushConst 0 Glyph.pos]

/-- push `int 0` on stack 0 (encoding `pos :: iend`) -/
def pushIntZero : Cmd :=
  seqs [pushConst 0 Glyph.iend, pushConst 0 Glyph.pos]

theorem enc_int_one : (Val.int 1).enc = [Glyph.pos, Glyph.bit true, Glyph.iend] := rfl
theorem enc_int_zero : (Val.int 0).enc = [Glyph.pos, Glyph.iend] := rfl

theorem pushIntOne_ev (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph) :
    ∃ s' n, Ev main pushIntOne ⟨g, X⟩ s' n ∧ n ≤ 6 ∧
      s'.stk 0 = (Val.int 1).enc ++ X 0 ∧ (∀ k : Stk, k ≠ 0 → s'.stk k = X k) := by
  obtain ⟨s₁, n₁, h₁, hn₁, hk₁, hf₁, -, -⟩ :=
    pushConst_ev (main := main) (k := 0) (cst := Glyph.iend) (g := g) (X := X)
  obtain ⟨s₂, n₂, h₂, hn₂, hk₂, hf₂, -, -⟩ :=
    pushConst_ev (main := main) (k := 0) (cst := Glyph.bit true) (g := s₁.reg) (X := s₁.stk)
  obtain ⟨s₃, n₃, h₃, hn₃, hk₃, hf₃, -, -⟩ :=
    pushConst_ev (main := main) (k := 0) (cst := Glyph.pos) (g := s₂.reg) (X := s₂.stk)
  have hbb : Ev main (.seq (pushConst 0 (Glyph.bit true)) (pushConst 0 Glyph.pos)) s₁ s₃ (n₂ + n₃) :=
    Ev.seq h₂ h₃
  have hmain : Ev main pushIntOne ⟨g, X⟩ s₃ (n₁ + (n₂ + n₃)) := by
    unfold pushIntOne
    simp only [seqs]
    exact Ev.seq h₁ hbb
  refine ⟨s₃, _, hmain, ?_, ?_, ?_⟩
  · have : n₁ + (n₂ + n₃) ≤ 6 := by omega
    exact this
  · rw [hk₃, hk₂, hk₁]
    rfl
  · intro k hk
    rw [hf₃ k hk, hf₂ k hk, hf₁ k hk]

theorem pushIntZero_ev (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph) :
    ∃ s' n, Ev main pushIntZero ⟨g, X⟩ s' n ∧ n ≤ 4 ∧
      s'.stk 0 = (Val.int 0).enc ++ X 0 ∧ (∀ k : Stk, k ≠ 0 → s'.stk k = X k) := by
  obtain ⟨s₁, n₁, h₁, hn₁, hk₁, hf₁, -, -⟩ :=
    pushConst_ev (main := main) (k := 0) (cst := Glyph.iend) (g := g) (X := X)
  obtain ⟨s₂, n₂, h₂, hn₂, hk₂, hf₂, -, -⟩ :=
    pushConst_ev (main := main) (k := 0) (cst := Glyph.pos) (g := s₁.reg) (X := s₁.stk)
  have hmain : Ev main pushIntZero ⟨g, X⟩ s₂ (n₁ + n₂) := by
    unfold pushIntZero
    simp only [seqs]
    exact Ev.seq h₁ h₂
  refine ⟨s₂, _, hmain, by omega, ?_, ?_⟩
  · rw [hk₂, hk₁]
    rfl
  · intro k hk
    rw [hf₂ k hk, hf₁ k hk]

/-! ## `encs` and size arithmetic -/

theorem encs_cons (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := rfl

theorem encs_append (l₁ l₂ : List Val) : encs (l₁ ++ l₂) = encs l₁ ++ encs l₂ := by
  simp only [encs, List.map_append, List.flatten_append]

theorem vsz_enc_cons (x y : Val) : vsz (Val.cons x y) = vsz x + vsz y + 1 := by
  simp [vsz, Val.enc, List.length_append]

theorem vsz_ofList_en (xs : List Val) : vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
      rw [show ofList (x :: xs) = Val.cons x (ofList xs) from rfl, vsz_enc_cons, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

/-! ## `BinOp` as a bounded evaluation -/

/-- a `BinOp` word applied to the two integers on top of stack 0 -/
theorem binOp_ev {main p : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main p P f C) {a b : ℤ} {rest : List Val} {R : List Glyph} {s : State}
    (hP : P a b) (hs : s.stk 0 = encs (.int a :: .int b :: rest) ++ R) :
    ∃ s' n, Eval main p s s' n ∧ n ≤ C a b ∧
      s'.stk 0 = encs (.int (f a b) :: rest) ++ R ∧
      (∀ k : Stk, k ≠ 0 → s'.stk k = s.stk k) := by
  obtain ⟨out, s', n, hpost, hev, hle, hstk, hfr⟩ :=
    h (.int a :: .int b :: rest) ⟨a, b, rest, rfl, hP⟩ s R hs
  obtain ⟨a', b', rest', hpre, hout⟩ := hpost
  simp only [List.cons.injEq, Val.int.injEq] at hpre
  obtain ⟨rfl, rfl, rfl⟩ := hpre
  refine ⟨s', n, hev, ?_, ?_, hfr⟩
  · unfold binCost at hle
    exact hle
  · rw [hstk, hout]

/-! ## Copying a value: `dupVal` -/

/-- body of the dual push: pop the top glyph of `c`, push it on both `a` and `b`; stop at `gMark` -/
def dupBBody (c a b : Stk) : Cmd :=
  .seq (.pop c rA)
    (seqs [.ite rA gMark (.set rLoopG Glyph.eos) (seqs [.push a rA, .push b rA])])

/-- move the glyphs above the boundary marker `gMark` on stack `c` to *both* `a` and `b` -/
def dupB (c a b : Stk) : Cmd := seqs [.set rLoopG Glyph.cons, .loop rLoopG Glyph.cons (dupBBody c a b)]

/-- copy the top value of stack `a` to the top of stack `b` (keeping it on `a`), buffering on `c`
and counting on `d` -/
def dupVal (a b c d : Stk) : Cmd := seqs [mvA a c d, dupB c a b]

/-! ## The counter step: copy the counter and increment it -/

/-- `dupVal 0 4 6 7` (copy the counter to stack 4, the label), move the counter aside, push `int 1`,
bring the counter back and add.  `addP` is `IntLib.add`. -/
def incDup (addP : Cmd) : Cmd :=
  seqs [dupVal 0 4 6 7, mvVal 0 9 10 11, pushIntOne, mvVal 9 0 10 11, addP]

/-! ## Dropping a value: `dropVal` -/

/-- body of the drain loop: pop the top glyph of `c`; stop at `gMark` -/
def drainBody (c : Stk) : Cmd :=
  .seq (.pop c rA) (.ite rA gMark (.set rLoopG Glyph.eos) (.set rLoopG Glyph.cons))

/-- drain stack `c` down to (and including) the boundary marker `gMark` -/
def drainMark (c : Stk) : Cmd := seqs [.set rLoopG Glyph.cons, .loop rLoopG Glyph.cons (drainBody c)]

/-- delete (and discard) the top value of stack `a`, buffering on `c` and counting on `d` -/
def dropVal (a c d : Stk) : Cmd := seqs [mvA a c d, drainMark c]

/-! ## Labelling and the loop body -/

/-- `xs` with every element labelled by its index, starting at `i`:
`lab i xs = [cons (int i) xs[0], cons (int (i+1)) xs[1], …]` -/
def lab (i : ℕ) (xs : List Val) : List Val :=
  (List.range xs.length).map fun j => Val.cons (.int ((i + j : ℕ) : ℤ)) (xs.getD j .nil)

theorem lab_length (i : ℕ) (xs : List Val) : (lab i xs).length = xs.length := by
  simp [lab]

/-- one element step of the enumerate loop: `ofList (x :: xs)` ↦ `ofList xs`, the counter is
incremented, and `cons (int i) x` is consed onto the accumulator -/
def enumStep (addP : Cmd) : Cmd :=
  seqs [.pop 1 rA, mvVal 1 3 6 7, incDup addP, mvVal 4 3 6 7, pushConst 3 Glyph.cons,
    mvVal 3 5 6 7, pushConst 5 Glyph.cons, .set rEn Glyph.cons]

/-- the body of the enumerate loop -/
def enumBody (addP : Cmd) : Cmd :=
  .seq (.peek 1 rA)
    (.ite rA Glyph.nil (.seq (.pop 1 rA) (.set rEn Glyph.eos)) (enumStep addP))

/-! ## Loop cost -/

/-- cost budget of one (element) iteration of the enumerate loop -/
def iterCost (c i : ℕ) (x : Val) : ℕ := c * (vsz x + isz (i : ℤ) + 4)

/-- cost budget of the whole enumerate loop on `xs` (counter starting at `i`) -/
def enumCost (c i : ℕ) : List Val → ℕ
  | [] => 10
  | x :: xs => iterCost c i x + 1 + enumCost c (i + 1) xs

theorem enumCost_nil (c i : ℕ) : enumCost c i ([] : List Val) = 10 := rfl

theorem enumCost_cons (c i : ℕ) (x : Val) (xs : List Val) :
    enumCost c i (x :: xs) = iterCost c i x + 1 + enumCost c (i + 1) xs := rfl

theorem vsz_ofList_reverse (xs : List Val) : vsz (ofList xs.reverse) = vsz (ofList xs) := by
  rw [vsz_ofList_en, vsz_ofList_en, List.map_reverse, List.sum_reverse, List.length_reverse]

end Work.Layout
