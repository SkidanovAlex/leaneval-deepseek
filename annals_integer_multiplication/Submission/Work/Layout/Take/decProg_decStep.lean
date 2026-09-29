import Mathlib
import Submission.Work.Layout.Take.Basic
import Submission.Work.Layout.Take.decBitsDecomp

/-!
# `decProg` decrements the binary counter on `sBit` by one

`decProg = set rE_x gMark ;; push sTmp rE_x ;; set rF_tk gCont_x ;; loop rF_tk gCont_x decBody ;; mvB sTmp sBit`
(`Submission/Work/Layout/Take/Defs.lean`).  The counter is held on stack `sBit` as `bitsG_x k.bits`
above a frame marker `gMark`.  The scan loop pops bits of `sBit`; a `bit false` is pushed back as
`bit true` on the carry stack `sTmp` and the scan goes on (the low bits of `k` are `false`, so
subtracting one turns them into `true`s and propagates the borrow); the first `bit true` stops the
scan, and it becomes a `bit false` on `sTmp` unless it was the leading bit of `k`.  Finally `mvB`
moves the buffered bits back from `sTmp` onto `sBit`, reversing them into correct order.

The main statement is `Work.Layout.DecStep main`: starting from `X sBit = bitsG_x k.bits ++ gMark :: R`
with `0 < k`, `decProg` reaches a state whose `sBit` is `bitsG_x (k - 1).bits ++ gMark :: R`, restores
`sTmp` and every stack other than `sBit` and `sTmp`, and costs at most `20 * (tzB k.bits + 2)`.

## Contents

1. one scan iteration in each of its two cases (`decBodyCont_ev`, `decBodyStop_nil`,
   `decBodyStop_cons`);
2. the buffer of bits the scan leaves on `sTmp` (`decBuf`) and the list identities it satisfies;
3. the loop (`decLoopRuns`), by induction on the number of low `false` bits;
4. the assembly of `decProg` (`decProg_decStep`), using the pure arithmetic fact
   `Work.Layout.Take.decBitsDecomp` to identify the resulting bit list with `(k - 1).bits`.

The cost bound has a lot of slack: the scan costs `9 * (tzB k.bits + 1) + 1` and `mvB` costs
`4 * (tzB k.bits + 2) + 3`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.Layout.Take

open HvdH

/-! ## 1. One iteration of the scan -/

/-- One iteration of the scan loop when the low bit of the counter is `false`: it is popped and a
`bit true` is pushed on the carry stack `sTmp`, and the loop driver `rF_tk` goes back to `gCont_x`, so the
scan continues.  Cost 5. -/
theorem decBodyCont_ev (main : Cmd) {g : Reg → Glyph} {X : Stk → List Glyph} {l : List Bool}
    {R : List Glyph} (hr : g rF_tk = gCont_x)
    (hbit : X sBit = bitsG_x (false :: l) ++ gMark :: R) :
    ∃ s' n, Ev main decBody ⟨g, X⟩ s' n ∧ n ≤ 5 ∧
      s'.stk sBit = bitsG_x l ++ gMark :: R ∧ s'.stk sTmp = Glyph.bit true :: X sTmp ∧
      s'.reg rF_tk = gCont_x := by
  have hbit' : X sBit = Glyph.bit false :: (bitsG_x l ++ gMark :: R) := by
    rw [hbit]; simp [bitsG_x]
  set g1 : Reg → Glyph := Function.update g rE_x (Glyph.bit false) with hg1
  set X1 : Stk → List Glyph := Function.update X sBit (bitsG_x l ++ gMark :: R) with hX1
  set g2 : Reg → Glyph := Function.update g1 rE_x (Glyph.bit true) with hg2
  set X2 : Stk → List Glyph := Function.update X1 sTmp (Glyph.bit true :: X1 sTmp) with hX2
  set g3 : Reg → Glyph := Function.update g2 rF_tk gCont_x with hg3
  have hpop : Ev main (.pop sBit rE_x) ⟨g, X⟩ ⟨g1, X1⟩ 1 := by
    rw [hg1, hX1]
    have h := ev_pop' main sBit rE_x g X
    rw [hbit'] at h
    exact h
  have hset1 : Ev main (.set rE_x (Glyph.bit true)) ⟨g1, X1⟩ ⟨g2, X1⟩ 1 := by
    rw [hg2]; exact ev_set' main rE_x (Glyph.bit true) g1 X1
  have hpush : Ev main (.push sTmp rE_x) ⟨g2, X1⟩ ⟨g2, X2⟩ 1 := by
    rw [hX2]; exact ev_push' main sTmp rE_x g2 X1
  have hset2 : Ev main (.set rF_tk gCont_x) ⟨g2, X2⟩ ⟨g3, X2⟩ 1 := by
    rw [hg3]; exact ev_set' main rF_tk gCont_x g2 X2
  have hbr : Ev main (seqs [.set rE_x (Glyph.bit true), .push sTmp rE_x, .set rF_tk gCont_x])
      ⟨g1, X1⟩ ⟨g3, X2⟩ 3 :=
    Ev.seq' hset1 (Ev.seq' hpush hset2 (C := 2) (by omega)) (C := 3) (by omega)
  have hite : Ev main (.ite rE_x (Glyph.bit false)
      (seqs [.set rE_x (Glyph.bit true), .push sTmp rE_x, .set rF_tk gCont_x])
      (.ite rE_x (Glyph.bit true)
        (seqs [.peek sBit rE_x, .ite rE_x gMark (.set rF_tk Glyph.eos)
          (seqs [.set rE_x (Glyph.bit false), .push sTmp rE_x, .set rF_tk Glyph.eos])])
        (.set rF_tk Glyph.eos))) ⟨g1, X1⟩ ⟨g3, X2⟩ 4 := by
    refine Ev.iteT ?_ hbr
    rw [hg1]; simp
  have hseq : Ev main decBody ⟨g, X⟩ ⟨g3, X2⟩ 5 := by
    unfold decBody
    simp only [seqs]
    exact Ev.seq' hpop hite (by omega)
  refine ⟨⟨g3, X2⟩, 5, hseq, le_rfl, ?_, ?_, ?_⟩
  · simp only [hX2, hX1, Function.update_of_ne (show sBit ≠ sTmp by decide), Function.update_self]
  · simp only [hX2, Function.update_self, hX1, Function.update_of_ne (show sTmp ≠ sBit by decide)]
  · simp only [hg3, Function.update_self]

/-- One iteration of the scan loop when the low bit is `true` and it is the leading bit of the
counter (`rest = []`): the `true` is popped, nothing is pushed on `sTmp`, and the loop stops
(`rF_tk` becomes `eos`).  Cost 6. -/
theorem decBodyStop_nil (main : Cmd) {g : Reg → Glyph} {X : Stk → List Glyph} {R : List Glyph}
    (hr : g rF_tk = gCont_x) (hbit : X sBit = bitsG_x [true] ++ gMark :: R) :
    ∃ s' n, Ev main decBody ⟨g, X⟩ s' n ∧ n ≤ 6 ∧
      s'.stk sBit = gMark :: R ∧ s'.stk sTmp = X sTmp ∧ s'.reg rF_tk = Glyph.eos := by
  have hbit' : X sBit = Glyph.bit true :: (gMark :: R) := by
    rw [hbit]; simp [bitsG_x]
  set g1 : Reg → Glyph := Function.update g rE_x (Glyph.bit true) with hg1
  set X1 : Stk → List Glyph := Function.update X sBit (gMark :: R) with hX1
  set g2 : Reg → Glyph := Function.update g1 rE_x gMark with hg2
  set g3 : Reg → Glyph := Function.update g2 rF_tk Glyph.eos with hg3
  have hpop : Ev main (.pop sBit rE_x) ⟨g, X⟩ ⟨g1, X1⟩ 1 := by
    rw [hg1, hX1]
    have h := ev_pop' main sBit rE_x g X
    rw [hbit'] at h
    exact h
  have hpeek : Ev main (.peek sBit rE_x) ⟨g1, X1⟩ ⟨g2, X1⟩ 1 := by
    rw [hg2]
    have h := ev_peek' main sBit rE_x g1 X1
    have hv : X1 sBit = gMark :: R := by
      rw [hX1, Function.update_self]
    rw [hv] at h
    exact h
  have hset : Ev main (.set rF_tk Glyph.eos) ⟨g2, X1⟩ ⟨g3, X1⟩ 1 := by
    rw [hg3]; exact ev_set' main rF_tk Glyph.eos g2 X1
  have hite2 : Ev main (.ite rE_x gMark (.set rF_tk Glyph.eos)
      (seqs [.set rE_x (Glyph.bit false), .push sTmp rE_x, .set rF_tk Glyph.eos])) ⟨g2, X1⟩ ⟨g3, X1⟩ 2 := by
    refine Ev.iteT ?_ hset
    rw [hg2]; simp
  have hA : Ev main (seqs [.peek sBit rE_x,
      .ite rE_x gMark (.set rF_tk Glyph.eos)
        (seqs [.set rE_x (Glyph.bit false), .push sTmp rE_x, .set rF_tk Glyph.eos])])
      ⟨g1, X1⟩ ⟨g3, X1⟩ 3 := Ev.seq' hpeek hite2 (C := 3) (by omega)
  have hT : Ev main (.ite rE_x (Glyph.bit true)
      (seqs [.peek sBit rE_x,
        .ite rE_x gMark (.set rF_tk Glyph.eos)
          (seqs [.set rE_x (Glyph.bit false), .push sTmp rE_x, .set rF_tk Glyph.eos])])
      (.set rF_tk Glyph.eos)) ⟨g1, X1⟩ ⟨g3, X1⟩ 4 := by
    refine Ev.iteT ?_ hA
    rw [hg1]; simp
  have hite1 : Ev main (.ite rE_x (Glyph.bit false)
      (seqs [.set rE_x (Glyph.bit true), .push sTmp rE_x, .set rF_tk gCont_x])
      (.ite rE_x (Glyph.bit true)
        (seqs [.peek sBit rE_x,
          .ite rE_x gMark (.set rF_tk Glyph.eos)
            (seqs [.set rE_x (Glyph.bit false), .push sTmp rE_x, .set rF_tk Glyph.eos])])
        (.set rF_tk Glyph.eos))) ⟨g1, X1⟩ ⟨g3, X1⟩ 5 := by
    refine Ev.iteF ?_ hT
    rw [hg1]; simp
  have hseq : Ev main decBody ⟨g, X⟩ ⟨g3, X1⟩ 6 := by
    unfold decBody
    simp only [seqs]
    exact Ev.seq' hpop hite1 (by omega)
  refine ⟨⟨g3, X1⟩, 6, hseq, le_rfl, ?_, ?_, ?_⟩
  · simp only [hX1, Function.update_self]
  · simp only [hX1, Function.update_of_ne (show sTmp ≠ sBit by decide)]
  · simp only [hg3, Function.update_self]

/-- One iteration of the scan loop when the low bit is `true` and there are further bits above it
(`rest = b :: rest'`): the `true` is popped, a `bit false` is pushed on `sTmp` (the borrow stops
there), and the loop stops (`rF_tk` becomes `eos`).  Cost 8. -/
theorem decBodyStop_cons (main : Cmd) {g : Reg → Glyph} {X : Stk → List Glyph} {b : Bool}
    {rest' : List Bool} {R : List Glyph} (hr : g rF_tk = gCont_x)
    (hbit : X sBit = bitsG_x (true :: b :: rest') ++ gMark :: R) :
    ∃ s' n, Ev main decBody ⟨g, X⟩ s' n ∧ n ≤ 8 ∧
      s'.stk sBit = bitsG_x (b :: rest') ++ gMark :: R ∧
      s'.stk sTmp = Glyph.bit false :: X sTmp ∧ s'.reg rF_tk = Glyph.eos := by
  have hbit' : X sBit = Glyph.bit true :: (bitsG_x (b :: rest') ++ gMark :: R) := by
    rw [hbit]; simp [bitsG_x]
  set g1 : Reg → Glyph := Function.update g rE_x (Glyph.bit true) with hg1
  set X1 : Stk → List Glyph := Function.update X sBit (bitsG_x (b :: rest') ++ gMark :: R) with hX1
  set g2 : Reg → Glyph := Function.update g1 rE_x (Glyph.bit b) with hg2
  set g3 : Reg → Glyph := Function.update g2 rE_x (Glyph.bit false) with hg3
  set X2 : Stk → List Glyph := Function.update X1 sTmp (Glyph.bit false :: X1 sTmp) with hX2
  set g4 : Reg → Glyph := Function.update g3 rF_tk Glyph.eos with hg4
  have hpop : Ev main (.pop sBit rE_x) ⟨g, X⟩ ⟨g1, X1⟩ 1 := by
    rw [hg1, hX1]
    have h := ev_pop' main sBit rE_x g X
    rw [hbit'] at h
    exact h
  have hv : X1 sBit = Glyph.bit b :: (bitsG_x rest' ++ gMark :: R) := by
    rw [hX1, Function.update_self]; simp [bitsG_x]
  have hpeek : Ev main (.peek sBit rE_x) ⟨g1, X1⟩ ⟨g2, X1⟩ 1 := by
    rw [hg2]
    have h := ev_peek' main sBit rE_x g1 X1
    rw [hv] at h
    exact h
  have hset1 : Ev main (.set rE_x (Glyph.bit false)) ⟨g2, X1⟩ ⟨g3, X1⟩ 1 := by
    rw [hg3]; exact ev_set' main rE_x (Glyph.bit false) g2 X1
  have hpush : Ev main (.push sTmp rE_x) ⟨g3, X1⟩ ⟨g3, X2⟩ 1 := by
    rw [hX2]; exact ev_push' main sTmp rE_x g3 X1
  have hset2 : Ev main (.set rF_tk Glyph.eos) ⟨g3, X2⟩ ⟨g4, X2⟩ 1 := by
    rw [hg4]; exact ev_set' main rF_tk Glyph.eos g3 X2
  have hbr : Ev main (seqs [.set rE_x (Glyph.bit false), .push sTmp rE_x, .set rF_tk Glyph.eos])
      ⟨g2, X1⟩ ⟨g4, X2⟩ 3 :=
    Ev.seq' hset1 (Ev.seq' hpush hset2 (C := 2) (by omega)) (C := 3) (by omega)
  have hite2 : Ev main (.ite rE_x gMark (.set rF_tk Glyph.eos)
      (seqs [.set rE_x (Glyph.bit false), .push sTmp rE_x, .set rF_tk Glyph.eos]))
      ⟨g2, X1⟩ ⟨g4, X2⟩ 4 := by
    refine Ev.iteF ?_ hbr
    rw [hg2]
    simp only [Function.update_self]
    intro h
    exact gMark_ne_bit b h.symm
  have hA : Ev main (seqs [.peek sBit rE_x,
      .ite rE_x gMark (.set rF_tk Glyph.eos)
        (seqs [.set rE_x (Glyph.bit false), .push sTmp rE_x, .set rF_tk Glyph.eos])])
      ⟨g1, X1⟩ ⟨g4, X2⟩ 5 := Ev.seq' hpeek hite2 (C := 5) (by omega)
  have hT : Ev main (.ite rE_x (Glyph.bit true)
      (seqs [.peek sBit rE_x,
        .ite rE_x gMark (.set rF_tk Glyph.eos)
          (seqs [.set rE_x (Glyph.bit false), .push sTmp rE_x, .set rF_tk Glyph.eos])])
      (.set rF_tk Glyph.eos)) ⟨g1, X1⟩ ⟨g4, X2⟩ 6 := by
    refine Ev.iteT ?_ hA
    rw [hg1]; simp
  have hite1 : Ev main (.ite rE_x (Glyph.bit false)
      (seqs [.set rE_x (Glyph.bit true), .push sTmp rE_x, .set rF_tk gCont_x])
      (.ite rE_x (Glyph.bit true)
        (seqs [.peek sBit rE_x,
          .ite rE_x gMark (.set rF_tk Glyph.eos)
            (seqs [.set rE_x (Glyph.bit false), .push sTmp rE_x, .set rF_tk Glyph.eos])])
        (.set rF_tk Glyph.eos))) ⟨g1, X1⟩ ⟨g4, X2⟩ 7 := by
    refine Ev.iteF ?_ hT
    rw [hg1]; simp
  have hseq : Ev main decBody ⟨g, X⟩ ⟨g4, X2⟩ 8 := by
    unfold decBody
    simp only [seqs]
    exact Ev.seq' hpop hite1 (by omega)
  refine ⟨⟨g4, X2⟩, 8, hseq, le_rfl, ?_, ?_, ?_⟩
  · simp only [hX2, hX1, Function.update_of_ne (show sBit ≠ sTmp by decide), Function.update_self]
  · simp only [hX2, Function.update_self, hX1, Function.update_of_ne (show sTmp ≠ sBit by decide)]
  · simp only [hg4, Function.update_self]

/-! ## 2. The bits buffered on `sTmp` -/

/-- The `bit` glyphs pushed on `sTmp` by a completed scan: `bit false` (only when the popped
`true` was not the leading bit) on top of `tz` copies of `bit true`. -/
def decBuf (tz : ℕ) (rest : List Bool) : List Glyph :=
  (if rest = [] then [] else [Glyph.bit false]) ++ List.replicate tz (Glyph.bit true)

/-- One more `false` bit in the counter prepends one more `bit true` to the buffer. -/
theorem decBuf_succ (tz : ℕ) (rest : List Bool) (X : List Glyph) :
    decBuf tz rest ++ (Glyph.bit true :: X) = decBuf (tz + 1) rest ++ X := by
  have hrep : ∀ (n : ℕ) (l : List Glyph),
      List.replicate n (Glyph.bit true) ++ (Glyph.bit true :: l) =
        List.replicate (n + 1) (Glyph.bit true) ++ l := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ k ih => intro l; simp only [List.replicate_succ, List.cons_append, ih]
  simp only [decBuf, List.replicate_succ, List.append_assoc, hrep tz X]

/-- `mvB` reverses the buffer; this is the reversed buffer. -/
theorem decBuf_reverse (tz : ℕ) (rest : List Bool) :
    (decBuf tz rest).reverse =
      List.replicate tz (Glyph.bit true) ++ (if rest = [] then [] else [Glyph.bit false]) := by
  by_cases he : rest = []
  · simp [decBuf, he, List.reverse_replicate]
  · simp [decBuf, he, List.reverse_replicate]

/-- The reversed buffer appended to the remaining bits of the counter is the bit list of
`k - 1`, where `k.bits = false^tz ++ true :: rest` (see `decBitsDecomp`). -/
theorem bitsG_decBufTarget (tz : ℕ) (rest : List Bool) :
    bitsG_x (List.replicate tz true ++ (if rest = [] then [] else false :: rest)) =
      (List.replicate tz (Glyph.bit true) ++
        (if rest = [] then [] else [Glyph.bit false])) ++ bitsG_x rest := by
  by_cases he : rest = []
  · simp [he, bitsG_x]
  · simp [he, bitsG_x, List.map_append, List.map_replicate, List.append_assoc,
      List.singleton_append]

/-- The length of the buffer, for the cost of the final `mvB`. -/
theorem decBuf_length_le (tz : ℕ) (rest : List Bool) : (decBuf tz rest).length ≤ tz + 1 := by
  by_cases he : rest = []
  · simp [decBuf, he]
  · simp [decBuf, he]

/-! ## 3. The scan loop -/

/-- The scan loop: from a counter `bitsG_x (false^tz ++ true :: rest)` above the frame marker it runs
`tz + 1` iterations (the `tz` low `false` bits and the following `true` one), leaving the counter
with the bits `rest` and the buffer `decBuf tz rest` on `sTmp`.  Cost `9 * (tz + 1)`. -/
theorem decLoopRuns (main : Cmd) :
    ∀ (tz : ℕ) (rest : List Bool) (R : List Glyph) (g : Reg → Glyph) (X : Stk → List Glyph),
      g rF_tk = gCont_x →
      X sBit = bitsG_x (List.replicate tz false ++ (true :: rest)) ++ gMark :: R →
      ∃ s', loopRuns main rF_tk gCont_x decBody (tz + 1) ⟨g, X⟩ s' (9 * (tz + 1)) ∧
        s'.stk sBit = bitsG_x rest ++ gMark :: R ∧
        s'.stk sTmp = decBuf tz rest ++ X sTmp ∧
        s'.reg rF_tk = Glyph.eos := by
  intro tz
  induction tz with
  | zero =>
      intro rest R g X hr hbit
      rcases rest with _ | ⟨b, rest'⟩
      · obtain ⟨s', n, hev, hn, hsB, hsT_x, hr'⟩ :=
          decBodyStop_nil main hr (by simpa using hbit)
        refine ⟨s', ?_, ?_, ?_, hr'⟩
        · exact loopRuns.mono (by omega) (loopRuns.one hr (hev.mono hn)) (by omega)
        · simpa [bitsG_x] using hsB
        · simpa [decBuf] using hsT_x
      · obtain ⟨s', n, hev, hn, hsB, hsT_x, hr'⟩ :=
          decBodyStop_cons main hr (by simpa using hbit)
        refine ⟨s', ?_, ?_, ?_, hr'⟩
        · exact loopRuns.mono (by omega) (loopRuns.one hr (hev.mono hn)) (by omega)
        · simpa using hsB
        · simpa [decBuf, List.singleton_append] using hsT_x
  | succ tz ih =>
      intro rest R g X hr hbit
      have hbit₁ : X sBit = bitsG_x (false :: (List.replicate tz false ++ (true :: rest))) ++
          gMark :: R := by
        have h : List.replicate (tz + 1) false ++ (true :: rest) =
            false :: (List.replicate tz false ++ (true :: rest)) := by
          rw [List.replicate_succ, List.cons_append]
        rw [← h]; exact hbit
      obtain ⟨s₁, n₁, hev₁, hn₁, hsB₁, hsT₁, hr₁⟩ := decBodyCont_ev main hr hbit₁
      obtain ⟨s₂, hrun₂, hsB₂, hsT₂, hr₂⟩ := ih rest R s₁.reg s₁.stk hr₁ hsB₁
      refine ⟨s₂, ?_, hsB₂, ?_, hr₂⟩
      · exact loopRuns.succ' hr (hev₁.mono hn₁) hrun₂ (by omega)
      · rw [hsT₂, hsT₁]
        exact decBuf_succ tz rest (X sTmp)

/-! ## 4. The whole program -/

/-- `decProg` (`Submission/Work/Layout/Take/Defs.lean`) decrements the binary counter on stack
`sBit` by one: the counter is held as the bits of `k` least significant first (`bitsG_x k.bits`)
above a `gMark` frame marker, and the scan pops the low bits (`bit false` becomes `bit true` on the
carry stack `sTmp`) up to the first `bit true`, which becomes `bit false` unless it was the leading
bit.  `tzB l` is the number of leading `false`s of `l`.  This is the predicate
`Work.Layout.DecStep main` (which also fixes the cost bound `20 * (tzB k.bits + 2)`).

Hints: `decProg = set rE_x gMark ;; push sTmp rE_x ;; set rF_tk gCont_x ;; loop rF_tk gCont_x decBody ;;
mvB sTmp sBit`; `decBits` (the pure list-level decrement) is defined in Defs.lean next to `tzB`.
To identify `decBits k.bits` with `(k - 1).bits` you can use the `ofBits` API of
`Submission/Work/IntLib/ofBitsAPI.lean` (`ofBits_bits`, `bits_ofBits_of_isBits`, `isBits_bits`,
`ofBits_append`, `ofBits_cons`) together with `Nat.bits` facts; a related raw development
`IntLib/decValuePiece.lean` may also exist in the workspace. -/
theorem decProg_decStep (main : HvdH.Cmd) : Work.Layout.DecStep main := by
  intro k R g X hk hbit
  obtain ⟨tz, rest, hbits, htz, hdec⟩ := decBitsDecomp k hk
  have hbit' : X sBit = bitsG_x (List.replicate tz false ++ (true :: rest)) ++ gMark :: R := by
    rw [← hbits]; exact hbit
  have ha : Ev main (.set rE_x gMark) ⟨g, X⟩ ⟨Function.update g rE_x gMark, X⟩ 1 :=
    ev_set' main rE_x gMark g X
  have hb : Ev main (.push sTmp rE_x) ⟨Function.update g rE_x gMark, X⟩
      ⟨Function.update g rE_x gMark, Function.update X sTmp (gMark :: X sTmp)⟩ 1 := by
    simpa using ev_push' main sTmp rE_x (Function.update g rE_x gMark) X
  have hc : Ev main (.set rF_tk gCont_x)
      ⟨Function.update g rE_x gMark, Function.update X sTmp (gMark :: X sTmp)⟩
      ⟨Function.update (Function.update g rE_x gMark) rF_tk gCont_x,
        Function.update X sTmp (gMark :: X sTmp)⟩ 1 :=
    ev_set' main rF_tk gCont_x _ _
  have hdrv : (Function.update (Function.update g rE_x gMark) rF_tk gCont_x) rF_tk = gCont_x := by simp
  have hstkL : (Function.update X sTmp (gMark :: X sTmp)) sBit =
      bitsG_x (List.replicate tz false ++ (true :: rest)) ++ gMark :: R := by
    rw [Function.update_of_ne (show sBit ≠ sTmp by decide)]
    exact hbit'
  obtain ⟨s₄, hrun, hsB₄, hsT₄, hr₄⟩ :=
    decLoopRuns main tz rest R (Function.update (Function.update g rE_x gMark) rF_tk gCont_x)
      (Function.update X sTmp (gMark :: X sTmp)) hdrv hstkL
  have hloopEv : Ev main (.loop rF_tk gCont_x decBody)
      ⟨Function.update (Function.update g rE_x gMark) rF_tk gCont_x,
        Function.update X sTmp (gMark :: X sTmp)⟩ s₄ (9 * (tz + 1) + 1) :=
    loopRuns.eval hrun (by rw [hr₄]; decide)
  have hbuf : s₄.stk sTmp = decBuf tz rest ++ gMark :: X sTmp := by
    rw [hsT₄]; simp
  have hgm : gMark ∉ decBuf tz rest := by
    intro hmem
    have hmem' : gMark ∈ (if rest = [] then [] else [Glyph.bit false]) ++
        List.replicate tz (Glyph.bit true) := hmem
    rcases List.mem_append.mp hmem' with h1 | h2
    · by_cases he : rest = []
      · rw [if_pos he] at h1; exact List.not_mem_nil h1
      · rw [if_neg he] at h1
        exact gMark_ne_bit false (List.mem_singleton.mp h1)
    · exact gMark_ne_bit true (List.eq_of_mem_replicate h2)
  obtain ⟨s₅, n₅, hev₅, hn₅, hsT₅, hsB₅, hframe₅⟩ :=
    mvB_ev (main := main) (c := sTmp) (b := sBit) (by decide)
      (G := decBuf tz rest) (C := X sTmp) (B := bitsG_x rest ++ gMark :: R)
      (g := s₄.reg) (X := s₄.stk) hgm hbuf hsB₄
  have hmainEv : Ev main decProg ⟨g, X⟩ s₅
      (1 + (1 + (1 + ((9 * (tz + 1) + 1) + (4 * ((decBuf tz rest).length + 1) + 3))))) :=
    Ev.seqs_cons ha (Ev.seqs_cons hb (Ev.seqs_cons hc (Ev.seqs_cons hloopEv (hev₅.mono hn₅))))
  have htouches : cmdTouches decProg ⊆ ({sBit, sTmp} : Finset Stk) := by decide
  have hframe : ∀ j, j ≠ sBit → j ≠ sTmp → s₅.stk j = X j := by
    intro j hj1 hj2
    exact Ev.frame hmainEv (S := ({sBit, sTmp} : Finset Stk)) htouches (k := j) (by simp [hj1, hj2])
  obtain ⟨n, he, hn⟩ := hmainEv
  have key : (decBuf tz rest).reverse ++ bitsG_x rest = bitsG_x (k - 1).bits := by
    rw [hdec, decBuf_reverse, bitsG_decBufTarget]
  refine ⟨s₅, n, ⟨n, he, le_rfl⟩, ?_, ?_, hsT₅, hframe⟩
  · rw [← htz]
    have hlen := decBuf_length_le tz rest
    omega
  · rw [hsB₅, ← List.append_assoc, key]

end Work.Layout.Take
