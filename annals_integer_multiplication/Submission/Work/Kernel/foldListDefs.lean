import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.Pend
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.mvVal_ev_full

/-!
# Kernel: definitions for the `foldList` field of `HvdH.KernelLib`

`foldList` folds `q` over the list `ofList xs` sitting on top of the accumulator stack: it must run
the value stack through `I 0 acc → I xs.length acc'` with `q` seeing `xs.getD i .nil :: acc` at step
`i`, at cost `xs.length * (c + K * (L + 1)) + K` where `L` bounds `vsz` of the elements.

The program is built from three phases, each with its own scratch stack:

* **phase 1** (`foldList_prog1`, stack `1` = `foldList_sA`): peel the `cons`-chain apart, moving the
  elements one by one onto stack `1` (so they end up there in *reverse* order, above the frame
  marker `foldList_tag`), leaving the accumulator alone on stack `0`;
* **phase 2** (`foldList_prog2`, stacks `1 → 2` = `foldList_sB`): move them back one by one, which
  restores the original order;
* **phase 3** (`foldList_prog3 q`): for each element, move it back on top of the accumulator, run
  `q`, and repeat until only the frame marker is left.

All moves are `Work.Layout.mvVal` (cost `≤ 16 * (vsz v + 1)`), so every element is touched twice and
the accumulator never moves: the total cost is `O(xs.length * (L + 1) + xs.length * c)`.

Everything below is `sorry`-free.  The three phase lemmas are proved in
`Submission/Work/Kernel/foldListPhase{1,2,3}.lean`, the assembly in
`Submission/Work/Kernel/foldList.lean`.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH
open Work.Layout

/-! ## 1. The marker glyph and the scratch registers -/

/-- Frame marker pushed at the bottom of the two scratch stacks `1`, `2`.  Never part of a
`Val.enc`. -/
def foldList_tag : Glyph := .mk 5

/-- Register holding the most recently peeked glyph (loop test of phase 1, marker test of 2, 3). -/
def foldList_rG : Reg := 0

/-- Register driving the `loop` of phases 2 and 3. -/
def foldList_rL : Reg := 1

/-- Scratch register of the trailing `pop`s. -/
def foldList_rS : Reg := 2

/-! ## 2. The programs -/

/-- One iteration of phase 1: drop the leading `cons` glyph of the remaining list, move the
exposed element to stack `1`, peek the next glyph of stack `0` into the test register. -/
def foldList_body1 : Cmd :=
  seqs [.pop (0 : Stk) foldList_rS, mvVal 0 1 3 4, .peek (0 : Stk) foldList_rG]

/-- Phase 1: dismantle `ofList xs` onto stack `1`, then drop the trailing `nil`. -/
def foldList_prog1 : Cmd :=
  seqs [.peek (0 : Stk) foldList_rG, .loop foldList_rG Glyph.cons foldList_body1,
    .pop (0 : Stk) foldList_rS]

/-- One iteration of phase 2: if the top of stack `1` is the frame marker, the loop is over; else
move one element from stack `1` to stack `2`, peek the new top of stack `1`, and refresh the loop
flag `foldList_rL`.  The flag is set *at the end* of the body, so the loop runs exactly once per
element (`xs.length` bodies, `xs.length + 1` tests). -/
def foldList_body2 : Cmd :=
  .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
    (seqs [mvVal 1 2 3 4, .peek (1 : Stk) foldList_rG,
      .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos) (.set foldList_rL Glyph.cons)])

/-- Phase 2: move every element from stack `1` to stack `2` (restoring their order), then drop the
frame marker of stack `1`.  The flag is initialised according to the first glyph of stack `1`. -/
def foldList_prog2 : Cmd :=
  seqs [.peek (1 : Stk) foldList_rG,
    .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos) (.set foldList_rL Glyph.cons),
    .loop foldList_rL Glyph.cons foldList_body2, .pop (1 : Stk) foldList_rS]

/-- One iteration of phase 3: if the top of stack `2` is the frame marker, the loop is over; else
move one element on top of the accumulator stack `0`, run `q` on it, peek the new top of stack `2`
and refresh the loop flag at the end of the body (so the loop runs exactly once per element). -/
def foldList_body3 (q : Cmd) : Cmd :=
  .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos)
    (seqs [mvVal 2 0 3 4, q, .peek (2 : Stk) foldList_rG,
      .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos) (.set foldList_rL Glyph.cons)])

/-- Phase 3: fold `q` over the elements sitting on stack `2`, then drop the frame marker. -/
def foldList_prog3 (q : Cmd) : Cmd :=
  seqs [.peek (2 : Stk) foldList_rG,
    .ite foldList_rG foldList_tag (.set foldList_rL Glyph.eos) (.set foldList_rL Glyph.cons),
    .loop foldList_rL Glyph.cons (foldList_body3 q), .pop (2 : Stk) foldList_rS]

/-- The whole `foldList` program: frame markers on both scratch stacks, then the three phases. -/
def foldList_comb (q : Cmd) : Cmd :=
  seqs [pushConst (1 : Stk) foldList_tag, pushConst (2 : Stk) foldList_tag,
    foldList_prog1, foldList_prog2, foldList_prog3 q]

/-! ## 3. The marker is not a glyph of any value -/

/-- The head of `v.enc` is never the frame marker. -/
theorem foldList_headD_enc_append_ne_tag (v : Val) (l : List Glyph) :
    (v.enc ++ l).headD Glyph.eos ≠ foldList_tag := by
  cases v with
  | int z => by_cases hz : z < 0 <;> simp [Val.enc, hz, foldList_tag]
  | nil => simp [Val.enc, foldList_tag]
  | cons a b => simp [Val.enc, foldList_tag]

/-- Same, for a value stack written as `encs (x :: rest) ++ W`. -/
theorem foldList_headD_encs_ne_tag (x : Val) (rest : List Val) (W : List Glyph) :
    (encs (x :: rest) ++ W).headD Glyph.eos ≠ foldList_tag := by
  rw [encs_cons, List.append_assoc]
  exact foldList_headD_enc_append_ne_tag x (encs rest ++ W)

/-- The frame marker sits on top of `encs us ++ foldList_tag :: W` exactly when `us` is empty. -/
theorem foldList_headD_encs_eq_tag_iff (us : List Val) (W : List Glyph) :
    (encs us ++ foldList_tag :: W).headD Glyph.eos = foldList_tag ↔ us = [] := by
  constructor
  · intro h
    match us with
    | [] => rfl
    | u :: us' => exact absurd h (foldList_headD_encs_ne_tag u us' (foldList_tag :: W))
  · intro h; subst h; simp [encs, foldList_tag]

/-- The first glyph of a list encoding: `cons` when the list is nonempty, `nil` otherwise. -/
theorem foldList_headD_ofList (l acc : List Val) (R : List Glyph) :
    (encs (ofList l :: acc) ++ R).headD Glyph.eos
      = (if l = [] then Glyph.nil else Glyph.cons) := by
  cases l with
  | nil => simp [ofList, encs, Val.enc]
  | cons a t => simp [ofList, encs, Val.enc]

/-- Dropping the `nil` glyph that encodes the empty list. -/
theorem foldList_tail_encs_ofList_nil (acc : List Val) (R : List Glyph) :
    (encs (ofList [] :: acc) ++ R).tail = encs acc ++ R := by
  simp [ofList, encs, Val.enc]

/-! ## 4. Elementary list facts -/

theorem foldList_getD_mem {xs : List Val} {i : ℕ} (h : i < xs.length) :
    xs.getD i Val.nil ∈ xs := by
  rw [List.getD_eq_getElem xs _ h]; exact List.getElem_mem h

theorem foldList_drop_eq_getD_cons (xs : List Val) (i : ℕ) (h : i < xs.length) :
    xs.drop i = xs.getD i Val.nil :: xs.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem xs Val.nil h]

theorem foldList_take_reverse_succ (xs : List Val) (i : ℕ) (h : i < xs.length) :
    (xs.take (i + 1)).reverse = xs.getD i Val.nil :: (xs.take i).reverse := by
  rw [← List.take_append_getElem h, List.reverse_append, List.getD_eq_getElem xs Val.nil h]
  simp

theorem foldList_take_reverse_length (xs : List Val) :
    (xs.take xs.length).reverse = xs.reverse := by simp

theorem foldList_drop_length (xs : List Val) : xs.drop xs.length = [] := List.drop_length ..

/-! ## 5. The invariants of the three phases -/

/-- Invariant of phase 1 after `i` iterations: stack `0` still holds `ofList (xs.drop i)` on top of
the accumulator, stack `1` holds the `i` elements already peeled off (in reverse order) above the
frame marker, and register `foldList_rG` holds the leading glyph of stack `0` (so the loop stops
exactly when `[]` has been reached). -/
def foldList_P1 (xs acc : List Val) (R : List Glyph) (A0 : List Glyph) (s : State) :
    ℕ → State → Prop :=
  fun i X =>
    X.stk 0 = encs (ofList (xs.drop i) :: acc) ++ R ∧
    X.stk 1 = encs ((xs.take i).reverse) ++ foldList_tag :: A0 ∧
    (∀ k, k ≠ 0 → k ≠ 1 → X.stk k = s.stk k) ∧
    X.reg foldList_rG = (if xs.drop i = [] then Glyph.nil else Glyph.cons)

/-- Invariant of phase 2 after `i` iterations: `i` elements have been moved from stack `1` to
stack `2`, both above their frame markers; register `foldList_rG` is the leading glyph of stack `1`
(so the loop stops exactly when only the frame marker is left) and the loop flag `foldList_rL` is
`Glyph.cons` as long as elements remain, `Glyph.eos` at index `xs.length`. -/
def foldList_P2 (xs : List Val) (A0 B0 : List Glyph) (s : State) : ℕ → State → Prop :=
  fun i X =>
    X.stk 0 = s.stk 0 ∧
    X.stk 1 = encs ((xs.reverse).drop i) ++ foldList_tag :: A0 ∧
    X.stk 2 = encs (((xs.reverse).take i).reverse) ++ foldList_tag :: B0 ∧
    (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → X.stk k = s.stk k) ∧
    X.reg foldList_rG = (X.stk 1).headD Glyph.eos ∧
    X.reg foldList_rL = (if i < xs.length then Glyph.cons else Glyph.eos)

/-- Invariant of phase 3 after `i` iterations: stack `0` holds the accumulator `a` with `I i a`,
stack `2` holds the remaining (not yet folded) elements above the frame marker, register `foldList_rG`
is the leading glyph of stack `2` and the loop flag `foldList_rL` is `Glyph.cons` while elements
remain, `Glyph.eos` at index `xs.length`. -/
def foldList_P3 (xs : List Val) (R : List Glyph) (I : ℕ → List Val → Prop) (B0 : List Glyph)
    (s : State) : ℕ → State → Prop :=
  fun i X =>
    (∃ a, I i a ∧ X.stk 0 = encs a ++ R) ∧
    X.stk 2 = encs (xs.drop i) ++ foldList_tag :: B0 ∧
    (∀ k, k ≠ 0 → k ≠ 2 → X.stk k = s.stk k) ∧
    X.reg foldList_rG = (X.stk 2).headD Glyph.eos ∧
    X.reg foldList_rL = (if i < xs.length then Glyph.cons else Glyph.eos)

/-! ## 6. Unrolling a `loop` along an invariant -/

/-! ## 5. Unrolling a `loop` along an invariant -/

/-- `P`-indexed unrolling of `Cmd.loop` with a *uniform* per-iteration budget `B`: if from every
`P i` state (`i < n`) the test succeeds and the body runs to a `P (i+1)` state within `B` steps,
and no `P n` state passes the test, then the whole loop runs from any `P 0` state to some `P n`
state within `n * B + n + 1` steps (the `n` successful tests plus the final failing one). -/
theorem foldList_loopEv (main : Cmd) (r : Reg) (cc : Glyph) (body : Cmd) :
    ∀ (n : ℕ) (P : ℕ → State → Prop) (B : ℕ) (s : State), P 0 s →
      (∀ i < n, ∀ X, P i X → X.reg r = cc ∧ ∃ X', P (i + 1) X' ∧ Ev main body X X' B) →
      (∀ X, P n X → X.reg r ≠ cc) →
      ∃ s', Ev main (.loop r cc body) s s' (n * B + n + 1) ∧ P n s' := by
  intro n
  induction n with
  | zero =>
      intro P B s h0 _ hstop
      exact ⟨s, ⟨1, Eval.loopF (hstop s h0), by simp⟩, h0⟩
  | succ n ih =>
      intro P B s h0 hstep hstop
      obtain ⟨hr0, X1, hP1, hev0⟩ := hstep 0 (Nat.zero_lt_succ n) s h0
      have hstep' : ∀ i < n, ∀ X, (fun (j : ℕ) (Y : State) => P (j + 1) Y) i X →
          X.reg r = cc ∧ ∃ X', (fun (j : ℕ) (Y : State) => P (j + 1) Y) (i + 1) X' ∧
            Ev main body X X' B :=
        fun i hi X hX => hstep (i + 1) (by omega) X hX
      have hstop' : ∀ X, (fun (j : ℕ) (Y : State) => P (j + 1) Y) n X → X.reg r ≠ cc := hstop
      obtain ⟨s', hev, hP⟩ := ih (fun (j : ℕ) (Y : State) => P (j + 1) Y) B X1 hP1 hstep' hstop'
      refine ⟨s', ?_, hP⟩
      refine (Ev.loopT hr0 hev0 hev).mono ?_
      ring_nf
      omega

end Work.Kernel
