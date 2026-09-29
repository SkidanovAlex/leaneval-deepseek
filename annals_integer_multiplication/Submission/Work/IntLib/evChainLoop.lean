import Mathlib
import Submission.Work.IntLib.evChainDefs

/-!
# `IntLib` / `evChainLoop`: the loop of the chain word `evChainMove`

`evChainLoop` is the central induction of the chain word `evChainProg` of
`Submission/Work/IntLib/evChainDefs.lean`: the loop

`evChainLoopP k readG = loop rLp fGo (evChainBody k readG)`

walks a `cons`-chain `intList t` lying on top of stack 0, and for every element `h` of `t`

1. pops the leading `cons` cell of the chain and pushes it on stack `k`,
2. runs the single-value reader `readG`, which moves the encoding of `int h` (reversed) off
   stack 0 and prepends it to stack `k`,

so that after the whole chain has been consumed stack 0 holds only the closing `nil` and stack `k`
holds `revAcc t` above the caller's data `A`; the loop flag ends at `fStop`.

The cost is exactly the natural one: the body has seven primitive steps plus the reader, and each
iteration pays one loop test (`8 * t.length`), plus the four additional steps of the first (and, for
an empty chain, only) iteration and the final failing test (`5`).

The proof is by induction on the chain `t`.  The invariant after `j` processed elements is the
stack function `LStk k (t.drop j) (revAcc (t.take j) ++ A) rest Y`, i.e. the remaining chain on
stack 0 and the accumulated reverse blocks above `A` on stack `k`.  One step is
`chainBody_step` (the seven-command trace through `evChainBody`), the empty-chain base case is
`chainBody_nil`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open Work.Layout

/-! ## The loop invariant -/

/-- The stack layout of the chain loop after `l` elements of the chain have been processed:
stack 0 carries the encoding of the remaining chain `l`, and stack `k` the accumulated reverse
blocks `Acc` above the caller's data `Y k`. -/
def LStk (k : Stk) (l : List ℕ) (Acc rest : List Glyph) (Y : Stk → List Glyph) : Stk → List Glyph :=
  fun j => if j = 0 then Val.enc (intList l) ++ rest else if j = k then Acc ++ Y k else Y j

@[simp] theorem LStk_zero (k : Stk) (l : List ℕ) (Acc rest : List Glyph) (Y : Stk → List Glyph) :
    LStk k l Acc rest Y 0 = Val.enc (intList l) ++ rest := by simp [LStk]

theorem LStk_k (k : Stk) (l : List ℕ) (Acc rest : List Glyph) (Y : Stk → List Glyph)
    (hk : k ≠ 0) : LStk k l Acc rest Y k = Acc ++ Y k := by simp [LStk, hk]

theorem LStk_ne (k : Stk) (l : List ℕ) (Acc rest : List Glyph) (Y : Stk → List Glyph) {j : Stk}
    (hj0 : j ≠ 0) (hjk : j ≠ k) : LStk k l Acc rest Y j = Y j := by simp [LStk, hj0, hjk]

/-- The head of the encoding of a chain says whether the chain is empty. -/
theorem enc_intList_headD (l : List ℕ) (rest : List Glyph) :
    (Val.enc (intList l) ++ rest).headD Glyph.eos = if l = [] then Glyph.nil else Glyph.cons := by
  cases l with
  | nil => rw [enc_intList_nil]; simp
  | cons h tl => rw [enc_intList_cons]; simp

/-! ## Elementary `Ev` lemmas with explicit states -/

theorem ev_pop_cons (main : Cmd) (kk : Stk) (r : Reg) (g : Reg → Glyph) (X : Stk → List Glyph)
    {c : Glyph} {l : List Glyph} (hX : X kk = c :: l) :
    Ev main (.pop kk r) ⟨g, X⟩ ⟨Function.update g r c, Function.update X kk l⟩ 1 := by
  refine ⟨1, ?_, le_rfl⟩
  convert Eval.pop kk r ⟨g, X⟩ using 1
  simp [hX]

theorem ev_peek_eq (main : Cmd) (kk : Stk) (r : Reg) (g : Reg → Glyph) (X : Stk → List Glyph)
    {c : Glyph} (hX : (X kk).headD Glyph.eos = c) :
    Ev main (.peek kk r) ⟨g, X⟩ ⟨Function.update g r c, X⟩ 1 := by
  refine ⟨1, ?_, le_rfl⟩
  subst hX
  exact Eval.peek kk r ⟨g, X⟩

theorem ev_push_eq (main : Cmd) (kk : Stk) (r : Reg) (g : Reg → Glyph) (X : Stk → List Glyph)
    {c : Glyph} (hX : g r = c) :
    Ev main (.push kk r) ⟨g, X⟩ ⟨g, Function.update X kk (c :: X kk)⟩ 1 := by
  refine ⟨1, ?_, le_rfl⟩
  subst hX
  exact Eval.push kk r ⟨g, X⟩

theorem ev_set_eq (main : Cmd) (r : Reg) (c : Glyph) (g : Reg → Glyph) (X : Stk → List Glyph) :
    Ev main (.set r c) ⟨g, X⟩ ⟨Function.update g r c, X⟩ 1 :=
  ⟨1, Eval.set r c ⟨g, X⟩, le_rfl⟩

/-! ## The hypothesis on the reader, in explicit-state form -/

/-- The hypothesis on `readG`, rewritten so that the post-state is given as an explicit stack
function of the pre-state. -/
theorem readGPack (k : Stk) (hk : k ≠ 0) (readG : Cmd) (KR : ℕ)
    (hread : ∀ (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph) (h : ℕ) (rest : List Glyph),
      X 0 = Val.enc (.int (h : ℤ)) ++ rest →
      ∃ (s' : State) (n : ℕ), Ev main readG ⟨g, X⟩ s' n ∧ n ≤ KR * (h.size + 2) ∧
        s'.stk 0 = rest ∧ s'.stk k = (Val.enc (.int (h : ℤ))).reverse ++ X k ∧
        (∀ j : Stk, j ≠ 0 → j ≠ k → s'.stk j = X j)) :
    ∀ (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph) (h : ℕ) (rest : List Glyph),
      X 0 = Val.enc (.int (h : ℤ)) ++ rest →
      ∃ (g' : Reg → Glyph) (n : ℕ), n ≤ KR * (h.size + 2) ∧
        Ev main readG ⟨g, X⟩ ⟨g', fun j => if j = 0 then rest
          else if j = k then (Val.enc (.int (h : ℤ))).reverse ++ X k else X j⟩ n := by
  intro main g X h rest hX
  obtain ⟨s', n, hev, hn, h0, hk', hoth⟩ := hread main g X h rest hX
  obtain ⟨rg, stk⟩ := s'
  have hstk : stk = (fun j => if j = 0 then rest
      else if j = k then (Val.enc (.int (h : ℤ))).reverse ++ X k else X j) := by
    funext j
    rcases eq_or_ne j 0 with hj0 | hj0
    · subst hj0; simpa using h0
    · rcases eq_or_ne j k with hjk | hjk
      · rw [hjk]; simpa [hk] using hk'
      · rw [if_neg hj0, if_neg hjk]; exact hoth j hj0 hjk
  rw [hstk] at hev
  exact ⟨rg, n, hn, hev⟩

/-! ## One iteration of the loop -/

/-- One iteration of the chain loop, for a chain whose head is `h`: the `cons` cell is popped and
pushed on stack `k`, the reader runs, and the loop flag is set according to whether the chain is
exhausted (`tl = []`) or not.  Cost: seven primitive steps plus the reader. -/
theorem chainBody_step (k : Stk) (hk : k ≠ 0) (readG : Cmd) (KR : ℕ)
    (hread : ∀ (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph) (h : ℕ) (rest : List Glyph),
      X 0 = Val.enc (.int (h : ℤ)) ++ rest →
      ∃ (g' : Reg → Glyph) (n : ℕ), n ≤ KR * (h.size + 2) ∧
        Ev main readG ⟨g, X⟩ ⟨g', fun j => if j = 0 then rest
          else if j = k then (Val.enc (.int (h : ℤ))).reverse ++ X k else X j⟩ n)
    (h : ℕ) (tl : List ℕ) (main : Cmd) (Acc rest : List Glyph) (Y : Stk → List Glyph)
    (gm : Reg → Glyph) :
    ∃ (gm' : Reg → Glyph),
      gm' rLp = (if (Val.enc (intList tl) ++ rest).headD Glyph.eos = Glyph.cons then fGo else fStop) ∧
      Ev main (evChainBody k readG) ⟨gm, LStk k (h :: tl) Acc rest Y⟩
        ⟨gm', LStk k tl (revBlk h ++ Acc) rest Y⟩ (7 + KR * (h.size + 2)) := by
  have h0k : (0 : Stk) ≠ k := fun h0 => hk h0.symm
  set X0 : Stk → List Glyph := LStk k (h :: tl) Acc rest Y with hX0'
  set X1 : Stk → List Glyph := Function.update X0 (0 : Stk)
      (Val.enc (.int (h : ℤ)) ++ (Val.enc (intList tl) ++ rest)) with hX1'
  set X2 : Stk → List Glyph := Function.update X1 k (Glyph.cons :: X1 k) with hX2'
  set X3 : Stk → List Glyph := LStk k tl (revBlk h ++ Acc) rest Y with hX3'
  set c : Glyph := (Val.enc (intList tl) ++ rest).headD Glyph.eos with hc'
  have hX0 : X0 0 = Glyph.cons :: (Val.enc (.int (h : ℤ)) ++ (Val.enc (intList tl) ++ rest)) := by
    rw [hX0', LStk_zero, enc_intList_cons, List.cons_append, List.append_assoc]
  have hX20 : X2 0 = Val.enc (.int (h : ℤ)) ++ (Val.enc (intList tl) ++ rest) := by
    rw [hX2', hX1']
    simp [h0k]
  set g1 : Reg → Glyph := Function.update gm rX Glyph.cons with hg1'
  have hreg1 : g1 rX = Glyph.cons := by simp [hg1']
  have e1 : Ev main (.peek (0 : Stk) rX) ⟨gm, X0⟩ ⟨g1, X0⟩ 1 := by
    have hh := ev_peek_eq main (0 : Stk) rX gm X0 (c := Glyph.cons) (by simp [hX0])
    simpa [hg1'] using hh
  set g2 : Reg → Glyph := Function.update g1 rX Glyph.cons with hg2'
  have e2 : Ev main (.pop (0 : Stk) rX) ⟨g1, X0⟩ ⟨g2, X1⟩ 1 := by
    have hh := ev_pop_cons main (0 : Stk) rX g1 X0 (c := Glyph.cons)
      (l := Val.enc (.int (h : ℤ)) ++ (Val.enc (intList tl) ++ rest)) (by rw [hX0])
    simpa [hg2', hX1'] using hh
  have hg2r : g2 rX = Glyph.cons := by simp [hg2']
  have e3 : Ev main (.push k rX) ⟨g2, X1⟩ ⟨g2, X2⟩ 1 := by
    have hh := ev_push_eq main k rX g2 X1 (c := Glyph.cons) hg2r
    simpa [hX2'] using hh
  obtain ⟨g3, nR, hnR, e4⟩ := hread main g2 X2 h (Val.enc (intList tl) ++ rest) hX20
  have hX3 : (fun j => if j = 0 then Val.enc (intList tl) ++ rest
      else if j = k then (Val.enc (.int (h : ℤ))).reverse ++ X2 k else X2 j) = X3 := by
    funext j
    rcases eq_or_ne j 0 with hj0 | hj0
    · subst hj0; simp [hX3']
    · rcases eq_or_ne j k with hjk | hjk
      · rw [hjk]
        have h1 : X2 k = Glyph.cons :: X1 k := by simp [hX2']
        have h2 : X1 k = X0 k := by rw [hX1']; simp only [Function.update_apply, if_neg hk]
        have h3 : X0 k = Acc ++ Y k := by rw [hX0', LStk_k k (h :: tl) Acc rest Y hk]
        have h4 : X3 k = (revBlk h ++ Acc) ++ Y k := by
          rw [hX3', LStk_k k tl (revBlk h ++ Acc) rest Y hk]
        simp [hk, h1, h2, h3, h4, revBlk, List.cons_append, List.append_assoc]
      · rw [if_neg hj0, if_neg hjk]
        have h1 : X2 j = X1 j := by rw [hX2']; simp only [Function.update_apply, if_neg hjk]
        have h2 : X1 j = X0 j := by rw [hX1']; simp only [Function.update_apply, if_neg hj0]
        have h3 : X0 j = Y j := by rw [hX0', LStk_ne k (h :: tl) Acc rest Y hj0 hjk]
        have h4 : X3 j = Y j := by rw [hX3', LStk_ne k tl (revBlk h ++ Acc) rest Y hj0 hjk]
        rw [h1, h2, h3, h4]
  have e4' : Ev main readG ⟨g2, X2⟩ ⟨g3, X3⟩ nR := by rw [← hX3]; exact e4
  set g4 : Reg → Glyph := Function.update g3 rX c with hg4'
  have hX30 : X3 0 = Val.enc (intList tl) ++ rest := by rw [hX3', LStk_zero]
  have e5 : Ev main (.peek (0 : Stk) rX) ⟨g3, X3⟩ ⟨g4, X3⟩ 1 := by
    have hh := ev_peek_eq main (0 : Stk) rX g3 X3 (c := c) (by rw [hX30, hc'])
    simpa [hg4'] using hh
  by_cases hc : c = Glyph.cons
  · -- the chain goes on: the loop flag is set to `fGo`
    set g5 : Reg → Glyph := Function.update g4 rLp fGo with hg5'
    have hreg : g4 rX = Glyph.cons := by simp [hg4', hc]
    have e6 : Ev main (.ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)) ⟨g4, X3⟩ ⟨g5, X3⟩ 2 := by
      have hh := ev_set_eq main rLp fGo g4 X3
      exact Ev.iteT hreg (by simpa [hg5'] using hh)
    have h3 : Ev main (seqs [.peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) ⟨g3, X3⟩ ⟨g5, X3⟩ 3 :=
      Ev.seqs_cons (cs := [.ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) e5 e6
    have h4 : Ev main (seqs [readG, .peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) ⟨g2, X2⟩ ⟨g5, X3⟩ (nR + 3) :=
      Ev.seqs_cons (cs := [.peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) e4' h3
    have h5 : Ev main (seqs [.push k rX, readG, .peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) ⟨g2, X1⟩ ⟨g5, X3⟩ (nR + 4) :=
      (Ev.seqs_cons (cs := [readG, .peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) e3 h4).mono (by omega)
    have h6 : Ev main (seqs [.pop (0 : Stk) rX, .push k rX, readG, .peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) ⟨g1, X0⟩ ⟨g5, X3⟩ (nR + 5) :=
      (Ev.seqs_cons (cs := [.push k rX, readG, .peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) e2 h5).mono (by omega)
    have h7 : Ev main (.ite rX Glyph.cons (seqs [.pop (0 : Stk) rX, .push k rX, readG,
        .peek (0 : Stk) rX, .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) (.set rLp fStop))
        ⟨g1, X0⟩ ⟨g5, X3⟩ (nR + 6) := (Ev.iteT hreg1 h6).mono (by omega)
    have h8 : Ev main (evChainBody k readG) ⟨gm, X0⟩ ⟨g5, X3⟩ (7 + nR) :=
      (Ev.seqs_cons (cs := [.ite rX Glyph.cons (seqs [.pop (0 : Stk) rX, .push k rX, readG,
        .peek (0 : Stk) rX, .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) (.set rLp fStop)])
        e1 h7).mono (by omega)
    exact ⟨g5, by simp [hg5', hc], h8.mono (by omega)⟩
  · -- the chain is exhausted: the loop flag is set to `fStop`
    set g5 : Reg → Glyph := Function.update g4 rLp fStop with hg5'
    have hreg : ¬ (g4 rX = Glyph.cons) := by simp [hg4', hc]
    have e6 : Ev main (.ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)) ⟨g4, X3⟩ ⟨g5, X3⟩ 2 := by
      have hh := ev_set_eq main rLp fStop g4 X3
      exact Ev.iteF hreg (by simpa [hg5'] using hh)
    have h3 : Ev main (seqs [.peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) ⟨g3, X3⟩ ⟨g5, X3⟩ 3 :=
      Ev.seqs_cons (cs := [.ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) e5 e6
    have h4 : Ev main (seqs [readG, .peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) ⟨g2, X2⟩ ⟨g5, X3⟩ (nR + 3) :=
      Ev.seqs_cons (cs := [.peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) e4' h3
    have h5 : Ev main (seqs [.push k rX, readG, .peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) ⟨g2, X1⟩ ⟨g5, X3⟩ (nR + 4) :=
      (Ev.seqs_cons (cs := [readG, .peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) e3 h4).mono (by omega)
    have h6 : Ev main (seqs [.pop (0 : Stk) rX, .push k rX, readG, .peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) ⟨g1, X0⟩ ⟨g5, X3⟩ (nR + 5) :=
      (Ev.seqs_cons (cs := [.push k rX, readG, .peek (0 : Stk) rX,
        .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) e2 h5).mono (by omega)
    have h7 : Ev main (.ite rX Glyph.cons (seqs [.pop (0 : Stk) rX, .push k rX, readG,
        .peek (0 : Stk) rX, .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) (.set rLp fStop))
        ⟨g1, X0⟩ ⟨g5, X3⟩ (nR + 6) := (Ev.iteT hreg1 h6).mono (by omega)
    have h8 : Ev main (evChainBody k readG) ⟨gm, X0⟩ ⟨g5, X3⟩ (7 + nR) :=
      (Ev.seqs_cons (cs := [.ite rX Glyph.cons (seqs [.pop (0 : Stk) rX, .push k rX, readG,
        .peek (0 : Stk) rX, .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) (.set rLp fStop)])
        e1 h7).mono (by omega)
    exact ⟨g5, by simp [hg5', hc], h8.mono (by omega)⟩

/-- The final iteration of the chain loop: stack 0 carries the closing `nil`, so the loop body does
nothing but set the flag to `fStop`. -/
theorem chainBody_nil (k : Stk) (_hk : k ≠ 0) (readG : Cmd) (main : Cmd) (Acc rest : List Glyph)
    (Y : Stk → List Glyph) (gm : Reg → Glyph) :
    ∃ (gm' : Reg → Glyph), gm' rLp = fStop ∧
      Ev main (evChainBody k readG) ⟨gm, LStk k [] Acc rest Y⟩ ⟨gm', LStk k [] Acc rest Y⟩ 3 := by
  set g1 : Reg → Glyph := Function.update gm rX Glyph.nil with hg1'
  have hX0 : LStk k [] Acc rest Y 0 = Glyph.nil :: rest := by simp [LStk, enc_intList_nil]
  have e1 : Ev main (.peek (0 : Stk) rX) ⟨gm, LStk k [] Acc rest Y⟩ ⟨g1, LStk k [] Acc rest Y⟩ 1 := by
    have hh := ev_peek_eq main (0 : Stk) rX gm (LStk k [] Acc rest Y) (c := Glyph.nil)
      (by simp [hX0])
    simpa [hg1'] using hh
  have hreg : ¬ (g1 rX = Glyph.cons) := by simp [hg1']
  set g2 : Reg → Glyph := Function.update g1 rLp fStop with hg2'
  have e2 : Ev main (.ite rX Glyph.cons (seqs [.pop (0 : Stk) rX, .push k rX, readG,
      .peek (0 : Stk) rX, .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) (.set rLp fStop))
      ⟨g1, LStk k [] Acc rest Y⟩ ⟨g2, LStk k [] Acc rest Y⟩ 2 := by
    have hh := ev_set_eq main rLp fStop g1 (LStk k [] Acc rest Y)
    exact Ev.iteF hreg (by simpa [hg2'] using hh)
  refine ⟨g2, by simp [hg2'], ?_⟩
  exact Ev.seqs_cons (cs := [.ite rX Glyph.cons (seqs [.pop (0 : Stk) rX, .push k rX, readG,
    .peek (0 : Stk) rX, .ite rX Glyph.cons (.set rLp fGo) (.set rLp fStop)]) (.set rLp fStop)])
    e1 e2

/-! ## The loop, by induction on the chain -/

/-- The chain loop, for a chain of size `t.length`: from `LStk k t Acc rest Y` it reaches
`LStk k [] (revAcc t ++ Acc) rest Y` with the flag at `fStop`, at the exact cost
`8 * t.length + 5 + Σ KR * (h.size + 2)`. -/
theorem chainLoop_aux (k : Stk) (hk : k ≠ 0) (readG : Cmd) (KR : ℕ)
    (hread : ∀ (main : Cmd) (g : Reg → Glyph) (X : Stk → List Glyph) (h : ℕ) (rest : List Glyph),
      X 0 = Val.enc (.int (h : ℤ)) ++ rest →
      ∃ (g' : Reg → Glyph) (n : ℕ), n ≤ KR * (h.size + 2) ∧
        Ev main readG ⟨g, X⟩ ⟨g', fun j => if j = 0 then rest
          else if j = k then (Val.enc (.int (h : ℤ))).reverse ++ X k else X j⟩ n) :
    ∀ (t : List ℕ) (main : Cmd) (Acc rest : List Glyph) (Y : Stk → List Glyph) (gm : Reg → Glyph),
      gm rLp = fGo →
      ∃ (gm' : Reg → Glyph), gm' rLp = fStop ∧
        Ev main (evChainLoopP k readG) ⟨gm, LStk k t Acc rest Y⟩
          ⟨gm', LStk k [] (revAcc t ++ Acc) rest Y⟩
          (8 * t.length + 5 + (t.map (fun h => KR * (h.size + 2))).sum) := by
  intro t
  induction t with
  | nil =>
      intro main Acc rest Y gm hgm
      obtain ⟨g1, hg1, hbody⟩ := chainBody_nil k hk readG main Acc rest Y gm
      have hg1ne : g1 rLp ≠ fGo := by rw [hg1]; decide
      have hstop : Ev main (evChainLoopP k readG) ⟨g1, LStk k [] Acc rest Y⟩
          ⟨g1, LStk k [] Acc rest Y⟩ 1 :=
        Ev.loopF (r := rLp) (c := fGo) (body := evChainBody k readG) hg1ne
      have hloop : Ev main (evChainLoopP k readG) ⟨gm, LStk k [] Acc rest Y⟩
          ⟨g1, LStk k [] Acc rest Y⟩ 5 :=
        Ev.loopT (r := rLp) (c := fGo) (body := evChainBody k readG) hgm hbody hstop
      exact ⟨g1, hg1, by simpa using hloop⟩
  | cons h tl ih =>
      intro main Acc rest Y gm hgm
      cases tl with
      | nil =>
          -- the only element is consumed and the chain ends
          obtain ⟨g1, hg1, hbody⟩ := chainBody_step k hk readG KR hread h [] main Acc rest Y gm
          have hhead : (if (Val.enc (intList ([] : List ℕ)) ++ rest).headD Glyph.eos = Glyph.cons
              then fGo else fStop) = fStop := by rw [enc_intList_headD]; simp
          have hg1s : g1 rLp = fStop := by rw [hg1, hhead]
          have hg1ne : g1 rLp ≠ fGo := by rw [hg1s]; decide
          have hstop : Ev main (evChainLoopP k readG) ⟨g1, LStk k [] (revBlk h ++ Acc) rest Y⟩
              ⟨g1, LStk k [] (revBlk h ++ Acc) rest Y⟩ 1 :=
            Ev.loopF (r := rLp) (c := fGo) (body := evChainBody k readG) hg1ne
          have hloop : Ev main (evChainLoopP k readG) ⟨gm, LStk k (h :: []) Acc rest Y⟩
              ⟨g1, LStk k [] (revBlk h ++ Acc) rest Y⟩ (7 + KR * (h.size + 2) + 1 + 1) :=
            Ev.loopT (r := rLp) (c := fGo) (body := evChainBody k readG) hgm hbody hstop
          refine ⟨g1, hg1s, ?_⟩
          rw [revAcc_cons, revAcc_nil, List.nil_append]
          refine hloop.mono ?_
          simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, Nat.add_zero]
          omega
      | cons h' tl' =>
          -- the first element is consumed, then the induction hypothesis for the rest
          obtain ⟨g1, hg1, hbody⟩ :=
            chainBody_step k hk readG KR hread h (h' :: tl') main Acc rest Y gm
          have hhead : (if (Val.enc (intList (h' :: tl')) ++ rest).headD Glyph.eos = Glyph.cons
              then fGo else fStop) = fGo := by rw [enc_intList_headD]; simp
          have hg1s : g1 rLp = fGo := by rw [hg1, hhead]
          obtain ⟨g2, hg2, hrec⟩ := ih main (revBlk h ++ Acc) rest Y g1 hg1s
          have hloop : Ev main (evChainLoopP k readG) ⟨gm, LStk k (h :: h' :: tl') Acc rest Y⟩
              ⟨g2, LStk k [] (revAcc (h' :: tl') ++ (revBlk h ++ Acc)) rest Y⟩
              (7 + KR * (h.size + 2) + (8 * (h' :: tl').length + 5
                + ((h' :: tl').map (fun h => KR * (h.size + 2))).sum) + 1) :=
            Ev.loopT (r := rLp) (c := fGo) (body := evChainBody k readG) hgm hbody hrec
          have hst2 : LStk k [] (revAcc (h :: h' :: tl') ++ Acc) rest Y
              = LStk k [] (revAcc (h' :: tl') ++ (revBlk h ++ Acc)) rest Y := by
            rw [revAcc_cons]; simp [List.append_assoc]
          refine ⟨g2, hg2, ?_⟩
          rw [hst2]
          refine hloop.mono ?_
          simp only [List.length_cons, List.map_cons, List.sum_cons]
          omega

theorem evChainLoop (k : HvdH.Stk) (hk : k ≠ 0) (readG : HvdH.Cmd) (KR : ℕ)
    (hread : ∀ (main : HvdH.Cmd) (g : HvdH.Reg → HvdH.Glyph) (X : HvdH.Stk → List HvdH.Glyph)
      (h : ℕ) (rest : List HvdH.Glyph),
      X 0 = HvdH.Val.enc (.int (h : ℤ)) ++ rest →
      ∃ (s' : HvdH.State) (n : ℕ), Work.Layout.Ev main readG ⟨g, X⟩ s' n ∧
        n ≤ KR * (h.size + 2) ∧ s'.stk 0 = rest ∧
        s'.stk k = (HvdH.Val.enc (.int (h : ℤ))).reverse ++ X k ∧
        (∀ j : HvdH.Stk, j ≠ 0 → j ≠ k → s'.stk j = X j)) :
    ∀ (main : HvdH.Cmd) (t : List ℕ) (A rest : List HvdH.Glyph) (Y : HvdH.Stk → List HvdH.Glyph)
      (gm : HvdH.Reg → HvdH.Glyph), gm Work.IntLib.rLp = Work.IntLib.fGo →
      ∃ (gm' : HvdH.Reg → HvdH.Glyph), gm' Work.IntLib.rLp = Work.IntLib.fStop ∧
        Work.Layout.Ev main (Work.IntLib.evChainLoopP k readG)
          ⟨gm, fun j => if j = 0 then HvdH.Val.enc (HvdH.intList t) ++ rest
                        else if j = k then A ++ Y k else Y j⟩
          ⟨gm', fun j => if j = 0 then [HvdH.Glyph.nil] ++ rest
                        else if j = k then Work.IntLib.revAcc t ++ A ++ Y k else Y j⟩
          (8 * t.length + 5 + (t.map (fun h => KR * (h.size + 2))).sum) := by
  intro main t A rest Y gm hgm
  obtain ⟨gm', hgm', hev⟩ :=
    chainLoop_aux k hk readG KR (readGPack k hk readG KR hread) t main A rest Y gm hgm
  refine ⟨gm', hgm', ?_⟩
  have h1 : LStk k t A rest Y = (fun j => if j = 0 then Val.enc (intList t) ++ rest
      else if j = k then A ++ Y k else Y j) := rfl
  have h2 : LStk k [] (revAcc t ++ A) rest Y = (fun j => if j = 0 then [Glyph.nil] ++ rest
      else if j = k then revAcc t ++ A ++ Y k else Y j) := by
    funext j
    by_cases hj0 : j = 0
    · subst hj0; simp [LStk, enc_intList_nil]
    · by_cases hjk : j = k
      · rw [hjk]; simp [LStk, hk]
      · simp [LStk, hj0, hjk]
  rw [h1, h2] at hev
  exact hev

end Work.IntLib
