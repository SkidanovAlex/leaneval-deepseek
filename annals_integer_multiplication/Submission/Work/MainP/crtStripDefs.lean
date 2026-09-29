import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.MainP.crtDefs
import Submission.Work.Layout.Move

/-!
# `crtStripWord`: stripping the keys off a list of records — shared definitions

`Work.MainP.crtStripWord` asks for a StackLang word turning the value stack `ofList rs :: rest`
into `ofList (rs.map recPayload) :: rest` when every `x ∈ rs` is a record `cons (int k) v`, at
cost linear in `vsz (ofList rs)`.  Write `uᵢ = recPayload rᵢ` for the payload of the `i`-th record;
at the glyph level the input is

  `X = C C t₁ u₁ C C t₂ u₂ … C C tₙ uₙ N`   (`C = Glyph.cons`, `tᵢ` the key encoding)

and the output is `ofList (rs.map recPayload)`, i.e.

  `V = C u₁ C u₂ … C uₙ N`.

The word walks the list once (no recursion, hence valid for every `main`):

* `stripTest` peeks the top glyph of stack 0 and records in register 2 whether the list is
  exhausted (`Glyph.nil`) or not;
* one *round* (`stripRound`) pushes the output `cons` glyph onto the output buffer (stack 2, with
  the frame marker `stripMark` at its bottom), splits the top value `ofList rs` into the record `r`
  and the tail list (`up` = `KernelLib.unconsV`), splits the record into its key and its payload
  (`up` again), drops the key (`dp` = `KernelLib.drop`) and moves the payload encoding to the
  buffer (`mv`, a scan of the payload with a unary pending-subtree counter on stack 1 pushing every
  glyph it reads, hence producing `(recPayload r).enc.reverse` on top of the buffer);
* after the loop the standing `nil` is dropped, a `nil` glyph is pushed on the buffer and
  `stripDrain` moves the whole buffer (down to `stripMark`) back to stack 0, which reverses it a
  second time and yields exactly `V`.

The buffer sits on stack 2, the value stack stays on stack 0, every other stack is restored; the
only side channel is the buffer stack, which the final drain empties again.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Frame markers -/

/-- Frame marker pushed at the bottom of the output buffer (stack 2).  (`.mk 12` is not used by
`Work.Layout` (`gMark = .mk 7`, `gSent = .mk 8`, `gPend = .mk 9`) nor by `Work.Kernel`.) -/
def stripMark : Glyph := .mk 12

/-- `stripGo`/`stripStop` are the two values of the loop-test registers. -/
def stripGo : Glyph := .mk 10
def stripStop : Glyph := .mk 11

theorem stripGo_ne_stop : stripGo ≠ stripStop := by decide
theorem stripMark_ne_tok : stripMark ≠ stripGo := by decide
theorem stripMark_ne_stop : stripMark ≠ stripStop := by decide
theorem stripMark_ne_pos : stripMark ≠ Glyph.pos := by decide
theorem stripMark_ne_neg : stripMark ≠ Glyph.neg := by decide
theorem stripMark_ne_nil : stripMark ≠ Glyph.nil := by decide
theorem stripMark_ne_cons : stripMark ≠ Glyph.cons := by decide
theorem stripMark_ne_iend : stripMark ≠ Glyph.iend := by decide
theorem stripMark_ne_eos : stripMark ≠ Glyph.eos := by decide
theorem stripMark_ne_bit (b : Bool) : stripMark ≠ Glyph.bit b := by cases b <;> decide

/-! ## Splitting a value stack -/

@[simp] theorem encs_cons (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := rfl

@[simp] theorem encs_nil : encs ([] : List Val) = [] := rfl

@[simp] theorem encs_append (vs ws : List Val) : encs (vs ++ ws) = encs vs ++ encs ws := by
  simp [encs]

/-! ## The buffer bookkeeping -/

/-- `consEnc xs` is the glyph string `C x₁.enc C x₂.enc … C xₙ.enc`, i.e. the body of the encoding
of `ofList xs`. -/
def consEnc (xs : List Val) : List Glyph := (xs.map fun x => Glyph.cons :: x.enc).flatten

theorem ofList_cons (x : Val) (xs : List Val) : ofList (x :: xs) = Val.cons x (ofList xs) := rfl

theorem ofList_nil : ofList ([] : List Val) = Val.nil := rfl

/-- The encoding of a list value: `ofList` inserts one `cons` per element, then the final `nil`. -/
theorem enc_ofList (xs : List Val) : (ofList xs).enc = consEnc xs ++ [Glyph.nil] := by
  induction xs with
  | nil => simp [ofList_nil, consEnc, Val.enc]
  | cons x xs ih =>
      rw [show ofList (x :: xs) = Val.cons x (ofList xs) from rfl, Val.enc, ih]
      simp [consEnc, List.map_cons, List.flatten_cons, List.cons_append, List.append_assoc]

theorem consEnc_nil : consEnc ([] : List Val) = [] := rfl

theorem consEnc_cons (x : Val) (xs : List Val) :
    consEnc (x :: xs) = Glyph.cons :: x.enc ++ consEnc xs := by
  simp [consEnc, List.map_cons, List.flatten_cons, List.cons_append]

theorem consEnc_append_singleton (xs : List Val) (x : Val) :
    consEnc (xs ++ [x]) = consEnc xs ++ Glyph.cons :: x.enc := by
  simp [consEnc, List.map_append, List.flatten_append]

/-- The chronological order of the glyphs pushed on the output buffer: for each record the output
`cons` glyph followed by the payload encoding. -/
def stripPush (rs : List Val) : List Glyph := consEnc (rs.map recPayload)

/-- The content of the output buffer above `stripMark` after `acc` records have been processed:
the *reverse* of the pushed glyph string. -/
def stripBuf (rs : List Val) : List Glyph := (stripPush rs).reverse

@[simp] theorem stripPush_nil : stripPush ([] : List Val) = [] := rfl

@[simp] theorem stripBuf_nil : stripBuf ([] : List Val) = [] := rfl

theorem stripBuf_reverse (rs : List Val) : (stripBuf rs).reverse = stripPush rs := by
  simp [stripBuf]

theorem stripPush_cons (r : Val) (rs : List Val) :
    stripPush (r :: rs) = Glyph.cons :: (recPayload r).enc ++ stripPush rs := by
  simp [stripPush, consEnc, List.map_cons, List.flatten_cons, List.cons_append]

theorem stripPush_append_singleton (acc : List Val) (r : Val) :
    stripPush (acc ++ [r]) = stripPush acc ++ Glyph.cons :: (recPayload r).enc := by
  simp [stripPush, List.map_append, consEnc_append_singleton]

theorem stripBuf_append_singleton (acc : List Val) (r : Val) :
    stripBuf (acc ++ [r]) = (recPayload r).enc.reverse ++ Glyph.cons :: stripBuf acc := by
  simp [stripBuf, stripPush_append_singleton, List.reverse_append, List.append_assoc]

/-- The object the walk has to produce: `ofList (rs.map recPayload)`. -/
theorem enc_target (rs : List Val) :
    (ofList (rs.map recPayload)).enc = stripPush rs ++ [Glyph.nil] := enc_ofList _

/-- The final content of stack 0 is the encoding of the output list. -/
theorem target_eq (rs : List Val) (rest : List Val) (R : List Glyph) :
    encs (ofList (rs.map recPayload) :: rest) ++ R =
      stripPush rs ++ [Glyph.nil] ++ encs rest ++ R := by
  rw [encs_cons, enc_target, List.append_assoc]

theorem length_stripPush (rs : List Val) :
    (stripPush rs).length = rs.length + (rs.map fun r => (recPayload r).enc.length).sum := by
  induction rs with
  | nil => simp [stripPush, consEnc]
  | cons r rs ih =>
      rw [stripPush_cons r rs, List.length_append, List.length_cons, ih, List.map_cons,
        List.sum_cons, List.length_cons]
      ring

/-! ## Size bounds -/

theorem vsz_cons_eq (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := vsz_cons a b

/-- Total payload size is at most the total size of the records. -/
theorem sum_vsz_recPayload_le (rs : List Val)
    (hrec : ∀ x ∈ rs, ∃ (k : ℤ) (u : Val), x = Val.cons (Val.int k) u) :
    (rs.map fun r => vsz (recPayload r)).sum ≤ (rs.map vsz).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
      obtain ⟨k, u, rfl⟩ := hrec r (by simp)
      have htail : ∀ x ∈ rs, ∃ (k : ℤ) (v : Val), x = Val.cons (Val.int k) v :=
        fun x hx => hrec x (by simp [hx])
      have h1 : vsz (recPayload (Val.cons (Val.int k) u)) ≤ vsz (Val.cons (Val.int k) u) := by
        rw [recPayload_cons, vsz_cons_eq]; omega
      have h2 := ih htail
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      omega

/-- The pushed glyph string fits in the encoding of the input list. -/
theorem length_stripPush_succ_le (rs : List Val)
    (hrec : ∀ x ∈ rs, ∃ (k : ℤ) (u : Val), x = Val.cons (Val.int k) u) :
    (stripPush rs).length + 1 ≤ vsz (ofList rs) := by
  have h1 := sum_vsz_recPayload_le rs hrec
  rw [length_stripPush, vsz_ofList]
  have h2 : (rs.map fun r => (recPayload r).enc.length).sum
      = (rs.map fun r => vsz (recPayload r)).sum := rfl
  rw [h2]
  omega

/-- A list is shorter than its encoding. -/
private theorem length_le_vsz_ofList (rs : List Val) : rs.length ≤ vsz (ofList rs) := by
  rw [vsz_ofList]; omega

/-- Each record contributes at most its own size. -/
theorem sum_vsz_succ_le (rs : List Val) :
    (rs.map fun r => vsz r + 1).sum ≤ vsz (ofList rs) := by
  rw [vsz_ofList]
  induction rs with
  | nil => simp
  | cons r rs ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.length_cons]
      omega

/-! ## The frame marker never occurs in a value encoding -/

theorem stripMark_notMem_map_bit (l : List Bool) : stripMark ∉ l.map Glyph.bit := by
  intro h
  rw [List.mem_map] at h
  obtain ⟨b, -, hb⟩ := h
  exact stripMark_ne_bit b hb.symm

/-- No value encoding contains the frame marker `stripMark`. -/
theorem stripMark_notMem_enc (v : Val) : stripMark ∉ v.enc := by
  induction v with
  | int z =>
      by_cases h : z < 0
      · simp [Val.enc, h, stripMark_notMem_map_bit, stripMark_ne_neg, stripMark_ne_iend]
      · simp [Val.enc, h, stripMark_notMem_map_bit, stripMark_ne_pos, stripMark_ne_iend]
  | nil => simp [Val.enc, stripMark_ne_nil]
  | cons a b iha ihb => simp [Val.enc, iha, ihb, stripMark_ne_cons]

theorem stripMark_notMem_stripPush (rs : List Val) : stripMark ∉ stripPush rs := by
  induction rs with
  | nil => simp [stripPush, consEnc]
  | cons r rs ih =>
      rw [stripPush_cons]
      intro h
      rcases List.mem_cons.mp h with h1 | h2
      · exact stripMark_ne_cons h1
      · rcases List.mem_append.mp h2 with h3 | h4
        · exact stripMark_notMem_enc (recPayload r) h3
        · exact ih h4

theorem stripMark_notMem_stripBuf (rs : List Val) : stripMark ∉ stripBuf rs := by
  rw [stripBuf, List.mem_reverse]
  exact stripMark_notMem_stripPush rs

/-! ## The programs -/

/-- Set register 2 to `stripGo` iff the top glyph of stack 0 is not the `nil` of an empty list. -/
def stripTest : Cmd := Cmd.seq (.peek 0 1) (.ite 1 Glyph.nil (.set 2 stripStop) (.set 2 stripGo))

/-- One round: push the output `cons` glyph, split off the record and its key, drop the key, move
the payload to the buffer, refresh the test. -/
def stripRound (up dp mv : Cmd) : Cmd :=
  Cmd.seq (.set 3 Glyph.cons) (Cmd.seq (.push 2 3)
    (Cmd.seq up (Cmd.seq up (Cmd.seq dp (Cmd.seq mv stripTest)))))

/-- One step of the final drain: move one buffer glyph to stack 0; stop (and do not push) at
`stripMark`.  Both branches cost two primitive steps, so every round of `stripDrain` costs 4. -/
def stripDrainBody : Cmd :=
  Cmd.seq (.pop 2 1) (.ite 1 stripMark (Cmd.seq (.set 4 stripStop) .skip)
    (Cmd.seq (.push 0 1) (.set 4 stripGo)))

/-- Move the whole output buffer back onto stack 0 (reversing it), stopping at `stripMark`. -/
def stripDrain : Cmd := Cmd.seq (.set 4 stripGo) (.loop 4 stripGo stripDrainBody)

/-- Set up the marker-free value mover: continue flag, counter sentinel and one counter unit. -/
def stripMvAInit (d : Stk) : Cmd :=
  Cmd.seq (.set Work.Layout.rLoopG Glyph.cons)
    (Cmd.seq (Work.Layout.pushConst d Work.Layout.gSent) (Work.Layout.pushConst d Work.Layout.gPend))

/-- Move the top value of stack `a` to stack `c` *reversed*, using `d` as the pending-subtree
counter of `Work.Layout`: this is `Work.Layout.mvA` with the boundary marker of its initialisation
left out, so that nothing is inserted below the moved glyphs on stack `c`. -/
def stripMvA (a c d : Stk) : Cmd :=
  Cmd.seq (stripMvAInit d)
    (Cmd.seq (.loop Work.Layout.rLoopG Glyph.cons (Work.Layout.mvABody a c d))
      (.pop d Work.Layout.rC))

/-- The whole word. -/
def stripProg (up dp mv : Cmd) : Cmd :=
  Cmd.seq (.set 3 stripMark) (Cmd.seq (.push 2 3)
    (Cmd.seq stripTest
      (Cmd.seq (.loop 2 stripGo (stripRound up dp mv))
        (Cmd.seq (.pop 0 3)
          (Cmd.seq (.set 3 Glyph.nil) (Cmd.seq (.push 2 3) stripDrain))))))

/-! ## The states of the walk -/

/-- The state of the walk during the main loop: the value stack is `ofList rs :: rest`, the output
buffer is `stripBuf acc` above the frame marker `stripMark` above `w`, and register 2 says whether
the list is exhausted. -/
def stripLoopState (s : State) (rest rs acc : List Val) (R w : List Glyph) : State :=
  (((s.updStk 0 (encs (ofList rs :: rest) ++ R)).updStk 2
      (stripBuf acc ++ stripMark :: w)).updReg 2 (if rs = [] then stripStop else stripGo))

@[simp] theorem stripLoopState_stk0 (s : State) (rest rs acc : List Val) (R w : List Glyph) :
    (stripLoopState s rest rs acc R w).stk 0 = encs (ofList rs :: rest) ++ R := by
  simp [stripLoopState]

@[simp] theorem stripLoopState_stk2 (s : State) (rest rs acc : List Val) (R w : List Glyph) :
    (stripLoopState s rest rs acc R w).stk 2 = stripBuf acc ++ stripMark :: w := by
  simp [stripLoopState]

@[simp] theorem stripLoopState_stk (s : State) (rest rs acc : List Val) (R w : List Glyph)
    (k : Stk) (h0 : k ≠ 0) (h2 : k ≠ 2) : (stripLoopState s rest rs acc R w).stk k = s.stk k := by
  simp [stripLoopState, h0, h2]

@[simp] theorem stripLoopState_reg2 (s : State) (rest rs acc : List Val) (R w : List Glyph) :
    (stripLoopState s rest rs acc R w).reg 2 = if rs = [] then stripStop else stripGo := by
  simp [stripLoopState]

/-- The state reached by the final drain: the buffer content `G` has been moved to stack 0
(reversed) and the buffer is back to `w`; register 4 holds `stripStop`. -/
def stripDrainPost (s : State) (G : List Glyph) (l0 w : List Glyph) : State :=
  (((s.updStk 0 (G.reverse ++ l0)).updStk 2 w).updReg 4 stripStop)

@[simp] theorem stripDrainPost_stk0 (s : State) (G l0 w : List Glyph) :
    (stripDrainPost s G l0 w).stk 0 = G.reverse ++ l0 := by simp [stripDrainPost]

@[simp] theorem stripDrainPost_stk2 (s : State) (G l0 w : List Glyph) :
    (stripDrainPost s G l0 w).stk 2 = w := by simp [stripDrainPost]

@[simp] theorem stripDrainPost_stk (s : State) (G l0 w : List Glyph) (k : Stk)
    (h0 : k ≠ 0) (h2 : k ≠ 2) : (stripDrainPost s G l0 w).stk k = s.stk k := by
  simp [stripDrainPost, h0, h2]

/-! ## The head glyph of the value stack -/

/-- The top glyph of the value stack `ofList rs :: rest` is `nil` exactly when the list `rs` is
empty (and `cons` otherwise). -/
theorem headD_encs_ofList (rs : List Val) (rest : List Val) (R : List Glyph) :
    (encs (ofList rs :: rest) ++ R).headD .eos =
      if rs = [] then Glyph.nil else Glyph.cons := by
  rw [encs_cons]
  cases rs with
  | nil => simp [ofList, Val.enc]
  | cons r rs' => rw [enc_ofList]; simp [consEnc_cons]

end Work.MainP
