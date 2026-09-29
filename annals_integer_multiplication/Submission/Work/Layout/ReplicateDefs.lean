import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Kernel.encodeNatBits

/-!
# Layout area: the `replicate` word — definitions

`LayoutLib.replicate`: `int k :: v :: rest ↦ ofList (replicate k v) :: rest`.

Route (paper: §2.3; `IntLib.chunk` with `x = 0`, `b = 1` produces `intList (replicate k 0)`):

1. push the constants `int 1`, `int 0` in front of `int k :: v :: rest`;
2. `IntLib.chunk 0 1 k` turns `int 0 :: int 1 :: int k` into `intList (replicate k 0)`, i.e. into the
   `k`-element list of zeros `L_k`;
3. move `L_k` to stack 1 (the *counter*) and `v` to stack 3 (the *source*), and push the accumulator
   `nil` on stack 0;
4. loop: while the counter's next glyph is `cons`, consume one `.int 0` (three glyphs
   `cons`,`pos`,`iend`), copy `v` from stack 3 onto stack 0, and prefix a `cons` glyph (this is
   `consV`-style: `acc := .cons v acc`);
5. pop the counter's terminating `nil`, move `v` back on top of the accumulator and `KernelLib.drop`
   it; the accumulator `ofList (replicate k v)` is left on stack 0.

The definitions live here so that the lemmas about them can be proved in parallel:
* `Work.Layout.pushList_ev`     — `pushList l` pushes `l` onto stack 0 (cost `2 * l.length + 1`);
* `Work.Layout.dupFrom_ev`      — `dupFrom a` copies the top value of stack `a` onto stack 0, keeping
  stack `a` (cost `≤ 16 * (vsz v + 1)`);
* `Work.Layout.repBody_ev`      — one iteration of the main loop;
* `Work.Layout.rep_loop`        — the main loop (in `Submission/Work/Layout/replicateWord.lean`).

No value is ever read "from below": the counter is scanned only through its own glyphs.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-- Push the glyph list `l` onto stack 0, so that stack 0 becomes `l ++ X 0`.  The list is pushed
from the back (`pushList (c :: cs)` pushes `cs` first, then `c`). -/
def pushList : List Glyph → Cmd
  | [] => Cmd.skip
  | c :: cs => Cmd.seq (pushList cs) (pushConst 0 c)

/-- Body of the "drain" loop: pop the top glyph of `c`; at the boundary marker `gMark` stop,
otherwise push it on *both* `b1` and `b2`. -/
def drain2Body (c b1 b2 : Stk) : Cmd :=
  seqs [Cmd.pop c rA, Cmd.ite rA gMark (Cmd.set rLoopG Glyph.eos)
    (seqs [Cmd.push b1 rA, Cmd.push b2 rA])]

/-- Pop the glyphs above the boundary marker `gMark` of stack `c`, pushing each glyph on `b1` *and*
on `b2`.  (The two destinations is what makes this a genuine duplication: `mvB` alone only moves.) -/
def drain2 (c b1 b2 : Stk) : Cmd :=
  seqs [Cmd.set rLoopG Glyph.cons, Cmd.loop rLoopG Glyph.cons (drain2Body c b1 b2)]

/-- Copy the top value of stack `a` onto the top of stack 0, leaving stack `a` unchanged.
`mvA` writes the reversal of `v.enc` above the boundary marker `gMark` on stack 5, and `drain2`
pushes it both back on stack `a` and on stack 0. -/
def dupFrom (a : Stk) : Cmd := seqs [mvA a 5 6, drain2 5 0 a]

/-- One iteration of the `replicate` loop.  Consumes one element `.int 0` of the counter on stack 1
(its three glyphs `cons`, `pos`, `iend`), copies the source `v` from stack 3 onto stack 0 and pushes
a `cons` glyph, so that the accumulator becomes `.cons v acc`; finally reads the counter's next
glyph into the loop register `rLoopG` (`cons` = one more element, `nil` = done). -/
def repBody : Cmd :=
  seqs [Cmd.pop 1 rB, Cmd.pop 1 rB, Cmd.pop 1 rB, dupFrom 3, pushConst 0 Glyph.cons,
    Cmd.peek 1 rLoopG]


/-! ## Encodings and sizes -/

theorem encs_cons'_rp (v : Val) (vs : List Val) : encs (v :: vs) = v.enc ++ encs vs := by
  simp [encs, List.flatten_cons]

theorem encs_nil' : encs ([] : List Val) = ([] : List Glyph) := rfl

theorem enc_int_zero_rp : (Val.int 0).enc = [Glyph.pos, Glyph.iend] := by
  simp [Val.enc, Work.Kernel.encodeNatBits]

theorem vsz_int_zero : vsz (Val.int 0) = 2 := by
  simp [vsz, Val.enc, Work.Kernel.encodeNatBits]

theorem isz_zero : isz (0 : ℤ) = 2 := by
  simp [isz, Nat.size_zero]

theorem isz_one : isz (1 : ℤ) = 3 := by
  simp [isz]

theorem vsz_cons (x y : Val) : vsz (Val.cons x y) = vsz x + vsz y + 1 := by
  simp [vsz, Val.enc, List.length_append]

/-- `IntLib.chunk 0 1 k` is the list of `k` zeros. -/
theorem chunks_zero_one (k : ℕ) : chunks 0 1 k = List.replicate k 0 := by
  simp only [chunks, Nat.zero_div, Nat.zero_mod]
  rw [List.map_const']
  simp

/-- the chunk list `intList (replicate k 0)` is the value `ofList (replicate k (.int 0))` -/
theorem intList_replicate (k : ℕ) : intList (List.replicate k 0) =
    ofList (List.replicate k (.int 0)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ]
      show Val.cons (Val.int 0) (intList (List.replicate k 0)) =
        Val.cons (Val.int 0) (ofList (List.replicate k (Val.int 0)))
      rw [ih]

theorem ofList_rep_succ (j : ℕ) : ofList (List.replicate (j+1) (.int 0)) =
    Val.cons (.int 0) (ofList (List.replicate j (.int 0))) := by
  rw [List.replicate_succ]; rfl

theorem enc_ofList_rep_succ (j : ℕ) : (ofList (List.replicate (j+1) (.int 0))).enc =
    Glyph.cons :: ((Val.int 0).enc ++ (ofList (List.replicate j (.int 0))).enc) := by
  rw [List.replicate_succ]; rfl

theorem enc_ofList_rep_zero : (ofList (List.replicate 0 (.int 0))).enc = [Glyph.nil] := by
  rw [List.replicate_zero]; rfl

theorem headD_enc_ofList_rep_zero :
    (ofList (List.replicate 0 (.int 0))).enc.headD Glyph.eos = Glyph.nil := by
  rw [List.replicate_zero]; rfl

theorem headD_enc_ofList_rep_succ (j : ℕ) :
    (ofList (List.replicate (j+1) (.int 0))).enc.headD Glyph.eos = Glyph.cons := by
  rw [List.replicate_succ]; rfl

/-- the counter with `j` elements has `3*j + 1` glyphs -/
theorem vsz_ofList_rep (j : ℕ) : vsz (ofList (List.replicate j (.int 0))) = 3 * j + 1 := by
  induction j with
  | zero =>
      show (ofList (List.replicate 0 (Val.int 0))).enc.length = 3 * 0 + 1
      rw [List.replicate_zero]; rfl
  | succ j ih =>
      rw [ofList_rep_succ, vsz_cons, ih, vsz_int_zero]
      omega

theorem size_ofList_rep (j : ℕ) : (ofList (List.replicate j (.int 0))).enc.length = 3 * j + 1 :=
  vsz_ofList_rep j

/-- consing one more `v` in front of a repeated list -/
theorem replicate_append_cons (i : ℕ) (v : Val) (l : List Val) :
    List.replicate i v ++ (v :: l) = List.replicate (i+1) v ++ l := by
  rw [show v :: l = List.replicate 1 v ++ l by rfl, ← List.append_assoc, ← List.replicate_add]

/-! ## The main loop -/

/-- Given a loop body which consumes one `.int 0` of the counter on stack 1, copies the source `v`
(fixed on stack 3) onto stack 0 with a leading `cons` glyph, and reads the counter's next glyph into
`rLoopG`, the loop runs once per remaining element. -/
theorem repLoop {main : Cmd} {body : Cmd} {Cd : ℕ → ℕ}
    (hstep : ∀ (v acc : Val) (L' : Val) (F S1 S3 : List Glyph) (g : Reg → Glyph)
      (X : Stk → List Glyph),
      X 0 = acc.enc ++ F → X 1 = (Val.cons (.int 0) L').enc ++ S1 → X 3 = v.enc ++ S3 →
      ∃ s' n, Ev main body ⟨g, X⟩ s' n ∧ n ≤ Cd (vsz v) + 6 ∧
        s'.stk 0 = (Val.cons v acc).enc ++ F ∧ s'.stk 1 = L'.enc ++ S1 ∧
        s'.stk 3 = v.enc ++ S3 ∧ s'.reg rLoopG = (L'.enc).headD Glyph.eos ∧
        (∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 3 → s'.stk k = X k)) :
    ∀ (j : ℕ) (accL : List Val) (v : Val) (F S1 S3 : List Glyph) (g : Reg → Glyph)
      (X : Stk → List Glyph),
      X 0 = (ofList accL).enc ++ F →
      X 1 = (ofList (List.replicate j (.int 0))).enc ++ S1 →
      X 3 = v.enc ++ S3 →
      g rLoopG = (ofList (List.replicate j (.int 0))).enc.headD Glyph.eos →
      ∃ s', loopRuns main rLoopG Glyph.cons body j ⟨g, X⟩ s' (j * (Cd (vsz v) + 7)) ∧
        s'.stk 0 = (ofList (List.replicate j v ++ accL)).enc ++ F ∧
        s'.stk 1 = (ofList (List.replicate 0 (.int 0))).enc ++ S1 ∧
        s'.stk 3 = v.enc ++ S3 ∧
        s'.reg rLoopG = (ofList (List.replicate 0 (.int 0))).enc.headD Glyph.eos ∧
        (∀ k : Stk, k ≠ 0 → k ≠ 1 → k ≠ 3 → s'.stk k = X k) := by
  intro j
  induction j with
  | zero =>
    intro accL v F S1 S3 g X h0 h1 h3 hg
    refine ⟨⟨g, X⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact loopRuns.congr rfl (by simp) loopRuns.zero
    · rw [List.replicate_zero]; exact h0
    · rw [List.replicate_zero]; exact h1
    · exact h3
    · rw [List.replicate_zero]; exact hg
    · intro k _ _ _; rfl
  | succ j ih =>
    intro accL v F S1 S3 g X h0 h1 h3 hg
    have hg1 : g rLoopG = Glyph.cons := by rw [hg]; exact headD_enc_ofList_rep_succ j
    have h1' : X 1 = (Val.cons (.int 0) (ofList (List.replicate j (.int 0)))).enc ++ S1 := by
      rw [← ofList_rep_succ]; exact h1
    obtain ⟨s₁, n₁, hev₁, hn₁, h1a, h1b, h1c, h1r, h1o⟩ :=
      hstep v (ofList accL) (ofList (List.replicate j (.int 0))) F S1 S3 g X h0 h1' h3
    have h1a' : s₁.stk 0 = (ofList (v :: accL)).enc ++ F := by rw [h1a]; rfl
    obtain ⟨s₂, hrun₂, h2a, h2b, h2c, h2r, h2o⟩ :=
      ih (v :: accL) v F S1 S3 s₁.reg s₁.stk h1a' h1b h1c h1r
    have hev₁' : Ev main body ⟨g, X⟩ s₁ (Cd (vsz v) + 6) := hev₁.mono (by omega)
    have hcat := loopRuns.concat j (loopRuns.one hg1 hev₁') hrun₂
    have hcost : (Cd (vsz v) + 6 + 1) + j * (Cd (vsz v) + 7) ≤ (j+1) * (Cd (vsz v) + 7) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have hcast : loopRuns main rLoopG Glyph.cons body (j+1) ⟨g, X⟩ s₂
        ((j+1) * (Cd (vsz v) + 7)) :=
      loopRuns.cast (show 1 + j = j + 1 by omega)
        (loopRuns.mono (show 1 ≤ 1 + j by omega) hcat hcost)
    refine ⟨s₂, hcast, ?_, h2b, h2c, h2r, ?_⟩
    · rw [h2a, replicate_append_cons j v accL]
    · intro k hk0 hk1 hk3
      rw [h2o k hk0 hk1 hk3, h1o k hk0 hk1 hk3]

/-- the cost bound for the assembled program -/
theorem replicateCostBound (Kc Kd k V I : ℕ) (hV : 2 ≤ V) :
    7 + 5 + Kc * (2 * k + I + 5) + (48 * k + 32) + 16 * V + 2 + 1 +
      (k * (16 * V + 7) + 1) + 1 + 16 * V + Kd * V
    ≤ (100 * (Kc + Kd + 10)) * ((k + 1) * V + I + 1) := by
  have h1 : V ≤ (k + 1) * V := Nat.le_mul_of_pos_left V (by omega)
  have h2 : 2 * k ≤ (k + 1) * V := by
    have h : (k + 1) * 2 ≤ (k + 1) * V := Nat.mul_le_mul_left (k + 1) hV
    omega
  have h3 : k ≤ (k + 1) * V := by omega
  have hKc : Kc * (2 * k + I + 5) ≤ Kc * (100 * ((k + 1) * V + I + 1)) := by
    apply Nat.mul_le_mul_left; omega
  have hKd : Kd * V ≤ Kd * (100 * ((k + 1) * V + I + 1)) := by
    apply Nat.mul_le_mul_left; omega
  have hrest : 7 + 5 + (48 * k + 32) + 16 * V + 2 + 1 + (k * (16 * V + 7) + 1) + 1 + 16 * V
      ≤ 1000 * ((k + 1) * V + I + 1) := by
    nlinarith [h1, h2, h3, Nat.zero_le k, Nat.zero_le I, Nat.zero_le V]
  nlinarith [hKc, hKd, hrest, Nat.zero_le Kc, Nat.zero_le Kd,
    Nat.zero_le ((k + 1) * V + I + 1)]


/-- `(ofList (replicate j (.int 0))).enc` is never empty -/
theorem enc_ofList_rep_ne_nil (j : ℕ) : (ofList (List.replicate j (.int 0))).enc ≠ [] := by
  cases j with
  | zero => rw [List.replicate_zero]; exact fun h => by cases h
  | succ j => rw [enc_ofList_rep_succ]; exact fun h => by cases h

/-- `headD` of a nonempty list is not affected by appending -/
theorem headD_append_of_ne (l₁ l₂ : List Glyph) (hl : l₁ ≠ []) (d : Glyph) :
    (l₁ ++ l₂).headD d = l₁.headD d := by
  cases l₁ with
  | nil => exact absurd rfl hl
  | cons a t => rfl



theorem enc_int_one_length : (Val.enc (.int 1)).length = 3 := by
  simp [Val.enc, Work.Kernel.encodeNatBits]

theorem enc_int_zero_length : (Val.enc (.int 0)).length = 2 := by
  simp [Val.enc, Work.Kernel.encodeNatBits]


end Work.Layout