import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full

/-!
# Kernel: `zipWith` — program definitions and elementary facts

`HvdH.KernelLib.zipWith` zips two lists of equal length with a StackLang word `q`.

The program `zipWith_prog q` uses the six stacks

* `0` — the value stack (carries `rest` while the lists are processed, and the output `ofList zs`);
* `1` — the remaining `ofList xs` (the `cons`-chain, first element on top of the encoding);
* `2` — the remaining `ofList ys`;
* `3` — the results `z`, in reverse order, above a frame marker `Work.Layout.gMark`;
* `4`, `5` — buffer and pending-counter of the value mover `Work.Layout.mvVal` (always restored).

It runs:

* setup — push the flag `cons`, push the marker `gMark` on stack 3, and move `ofList xs` and
  `ofList ys` from stack 0 to stacks 1 and 2;
* the **main loop** — while the top glyph of stack 1 is `cons`: pop the two `cons` glyphs, move the
  exposed element of stack 2 to stack 0 and then the exposed element of stack 1 to stack 0 (so that
  the value stack is exactly `x :: y :: rest`), run `q`, and move its result to stack 3; the loop
  stops (setting the flag to `eos`) when the two lists are exhausted;
* the two `nil` glyphs left on stacks 1 and 2 are popped;
* the **rebuild loop** — push the value `nil` on stack 0 and then, while the top glyph of stack 3 is
  not `gMark`, move the top value of stack 3 to stack 0 and push a `cons` glyph on top of it: this
  rebuilds `ofList zs` on top of `rest` (and pops the marker, restoring stack 3).

Every value is moved `O(1)` times, so the total cost is `xs.length * (c + K * (L + 1)) + K`.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-! ## The program -/

/-- Then-branch of the main loop body: peel one element off each list, run `q`, save the result. -/
def zipWith_bodyThen (q : Cmd) : Cmd :=
  Work.Layout.seqs
    [ .pop 1 Work.Layout.rA, .pop 2 Work.Layout.rA,
      Work.Layout.mvVal 2 0 4 5, Work.Layout.mvVal 1 0 4 5, q,
      Work.Layout.mvVal 0 3 4 5, .set Work.Layout.rLoopG Glyph.cons ]

/-- Main loop body: if the top glyph of stack 1 is `cons` (i.e. both lists are nonempty) process one
element of each, otherwise set the flag to `eos` and stop. -/
def zipWith_body (q : Cmd) : Cmd :=
  .seq (.peek 1 Work.Layout.rA)
    (.ite Work.Layout.rA Glyph.cons (zipWith_bodyThen q) (.set Work.Layout.rLoopG Glyph.eos))

/-- The main loop of `zipWith`. -/
def zipWith_loopProg (q : Cmd) : Cmd := .loop Work.Layout.rLoopG Glyph.cons (zipWith_body q)

/-- Rebuild-loop body: while the top glyph of stack 3 is not the marker, move the top value of
stack 3 to stack 0 and push a `cons` glyph on top of it. -/
def zipWith_rebuildBody : Cmd :=
  .seq (.peek 3 Work.Layout.rA)
    (.ite Work.Layout.rA Work.Layout.gMark
      (.seq (.pop 3 Work.Layout.rA) (.set Work.Layout.rLoopG Glyph.eos))
      (.seq (Work.Layout.mvVal 3 0 4 5)
        (.seq (Work.Layout.pushConst 0 Glyph.cons) (.set Work.Layout.rLoopG Glyph.cons))))

/-- The rebuild loop of `zipWith`. -/
def zipWith_rebuildProg : Cmd := .loop Work.Layout.rLoopG Glyph.cons zipWith_rebuildBody

/-- Setup of `zipWith`: push the marker on stack 3, move `ofList X0` and `ofList Y0` from the value
stack to stacks 1 and 2, and set the loop flag. -/
def zipWith_setupCmd : Cmd :=
  Work.Layout.seqs
    [ Work.Layout.pushConst 3 Work.Layout.gMark,
      Work.Layout.mvVal 0 1 4 5,
      Work.Layout.mvVal 0 2 4 5,
      .set Work.Layout.rLoopG Glyph.cons ]

/-- Cleanup and rebuild of `zipWith`: drop the two `nil` glyphs left on stacks 1 and 2, push the
value `nil` on the value stack, and run the rebuild loop. -/
def zipWith_finishCmd : Cmd :=
  Work.Layout.seqs
    [ .pop 1 Work.Layout.rA,
      .pop 2 Work.Layout.rA,
      Work.Layout.pushConst 0 Glyph.nil,
      .set Work.Layout.rLoopG Glyph.cons,
      zipWith_rebuildProg ]

/-- The whole `zipWith` program. -/
def zipWith_prog (q : Cmd) : Cmd :=
  Work.Layout.seqs [ zipWith_setupCmd, zipWith_loopProg q, zipWith_finishCmd ]

/-! ## Elementary facts about `encs`/`ofList` -/

@[simp] theorem zipWith_ofList_nil : ofList ([] : List Val) = .nil := rfl

@[simp] theorem zipWith_ofList_cons (x : Val) (xs : List Val) :
    ofList (x :: xs) = .cons x (ofList xs) := rfl

theorem zipWith_ofList_eq_nil {l : List Val} : ofList l = .nil ↔ l = [] := by
  cases l with
  | nil => simp
  | cons x xs => simp [zipWith_ofList_cons]

theorem zipWith_ofList_ne_nil {l : List Val} (h : l ≠ []) : ofList l ≠ .nil := by
  rw [Ne, zipWith_ofList_eq_nil]; exact h

@[simp] theorem zipWith_encs_singleton (x : Val) : encs [x] = x.enc := by simp [encs]

theorem zipWith_encs_append_singleton (l : List Val) (x : Val) :
    encs (l ++ [x]) = encs l ++ x.enc := by rw [encs_append]; simp [encs]

theorem zipWith_encs_reverse_cons (x : Val) (xs : List Val) :
    encs ((x :: xs).reverse) = encs xs.reverse ++ x.enc := by
  rw [List.reverse_cons, encs_append]; simp [encs]

/-- The encoding of `ofList (x :: xs)` starts with the glyph `cons`. -/
theorem zipWith_ofList_enc_cons (x : Val) (xs : List Val) :
    (ofList (x :: xs)).enc = Glyph.cons :: (x.enc ++ (ofList xs).enc) := rfl

/-- `encs (ofList xs :: rest)` with a nonempty list. -/
theorem zipWith_encs_ofList_cons (x : Val) (xs : List Val) (rest : List Val) :
    encs (ofList (x :: xs) :: rest) = Glyph.cons :: (x.enc ++ encs (ofList xs :: rest)) := by
  simp [encs, Val.enc, List.append_assoc]

/-- `encs (ofList xs :: rest)` with the empty list. -/
theorem zipWith_encs_ofList_nil (rest : List Val) :
    encs (ofList ([] : List Val) :: rest) = Glyph.nil :: encs rest := by
  simp [encs, Val.enc]

/-- Dropping `k < l.length` elements of a list splits off the head of the remaining encoding. -/
theorem zipWith_ofList_drop_enc {l : List Val} {k : ℕ} (h : k < l.length) :
    (ofList (l.drop k)).enc = Glyph.cons ::
      ((l.getD k .nil).enc ++ (ofList (l.drop (k + 1))).enc) := by
  have h1 : l.drop k = l.getD k .nil :: l.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem _ _ h]
  rw [h1]
  rfl

/-- The size of `ofList l` in terms of the sizes of its elements. -/
theorem zipWith_vsz_ofList_le {L : ℕ} : ∀ (l : List Val), (∀ x ∈ l, vsz x ≤ L) →
    vsz (ofList l) ≤ l.length * (L + 1) + 1 := by
  intro l
  induction l with
  | nil => intro _; simp [vsz, Val.enc]
  | cons x xs ih =>
    intro h
    have hx : vsz x ≤ L := h x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, vsz y ≤ L := fun y hy => h y (List.mem_cons_of_mem x hy)
    have h1 := ih hxs
    have h2 : vsz (ofList (x :: xs)) = 1 + vsz x + vsz (ofList xs) := by
      simp only [vsz, zipWith_ofList_cons, Val.enc, List.length_cons, List.length_append]
      omega
    have h4 : (xs.length + 1) * (L + 1) = xs.length * (L + 1) + (L + 1) := by ring
    rw [h2, List.length_cons, h4]
    omega

/-! ## The matching predicate -/

/-- `zipWith_corr Q X0 Y0 p`: the list `p` (in processing order) collects, for every index `i < p.length`,
the result of `Q` applied to the `i`-th elements of the original lists `X0` and `Y0`. -/
def zipWith_corr (Q : Val → Val → Val → Prop) (X0 Y0 p : List Val) : Prop :=
  p.length ≤ X0.length ∧ p.length ≤ Y0.length ∧
    ∀ i < p.length, Q (X0.getD i .nil) (Y0.getD i .nil) (p.getD i .nil)

theorem zipWith_corr_nil (Q : Val → Val → Val → Prop) (X0 Y0 : List Val) :
    zipWith_corr Q X0 Y0 [] := by
  refine ⟨by simp, by simp, ?_⟩
  intro i hi; simp at hi

theorem zipWith_corr_get {Q : Val → Val → Val → Prop} {X0 Y0 p : List Val}
    (h : zipWith_corr Q X0 Y0 p) {i : ℕ} (hi : i < p.length) :
    Q (X0.getD i .nil) (Y0.getD i .nil) (p.getD i .nil) := h.2.2 i hi

theorem zipWith_corr_snoc {Q : Val → Val → Val → Prop} {X0 Y0 p : List Val} {z : Val}
    (h : zipWith_corr Q X0 Y0 p) (hX : p.length < X0.length) (hY : p.length < Y0.length)
    (hz : Q (X0.getD p.length .nil) (Y0.getD p.length .nil) z) :
    zipWith_corr Q X0 Y0 (p ++ [z]) := by
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i p.length with hlt | hge
  · rw [List.getD_append p [z] .nil i hlt]; exact h.2.2 i hlt
  · have hi' : i = p.length := by omega
    rw [hi', List.getD_append_right p [z] .nil p.length (le_refl _)]
    simpa using hz

end Work.Kernel
