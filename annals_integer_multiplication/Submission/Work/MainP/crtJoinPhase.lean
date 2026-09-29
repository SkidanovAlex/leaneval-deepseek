import Mathlib
import Submission.Work.MainP.crtJoinPhaseAux
import Submission.Work.MainP.blkLoopEval
import Submission.Work.IntLib.UR.Main

/-!
# `crtJoinPhase`: the interleaving phase of the CRT reindexing word

`Work.MainP.joinPhase` (`Submission/Work/MainP/crtJoinDefs.lean`) is the last phase of the
Agarwal--Cooley reindexing word: from the two element buffers built by `consumeList` (stack 2 holds
the reversed `x`-blocks, stack 3 the reversed `w`-blocks, counted by the unary regions on stacks 6
and 7 above the base markers `jcb`) it pushes, for every element pair, `cons cons wᵢ xᵢ` onto stack 0,
so that the value stack becomes `outGlyphs Ws Gs` followed by the untouched tail `t`.

The proof decomposes into
* `blkLoopEval` (`Submission/Work/MainP/blkLoopEval.lean`): the counted block copy of one buffer;
* `joinBody_eval`: one round of the interleaving loop (both block copies, the two separators and the
  two `cons` glyphs);
* `joinLoopBody_eval`: the bare loop `Cmd.loop 1 jtok joinBody`, by induction on the list of pairs;
* `joinLoop_eval`: `joinLoop` (the bare loop preceded by its `peek`);
* `crtJoinPhase`: the assembly, with the costs added up.

The list-algebra of the pair list `Gs.reverse.zip Ws.reverse` (identifying the abstract buffers
`bufGs`, `cntGs`, ... with the `bufReg`/`cntReg` of `crtJoinDefs`) lives in `crtJoinPhaseAux`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH


/-! stand-in for the delegated lemma -/




/-! ## One round of the interleaving loop -/

theorem joinBody_eval (main : Cmd) (X : State) (acc : List Glyph) (g w : List Glyph)
    (rest2 rest3 rest6 rest7 : List Glyph)
    (h0 : X.stk 0 = acc) (h2 : X.stk 2 = g.reverse ++ rest2)
    (h3 : X.stk 3 = w.reverse ++ rest3)
    (h6 : X.stk 6 = List.replicate g.length jtok ++ jdelim :: rest6)
    (h7 : X.stk 7 = List.replicate w.length jtok ++ jdelim :: rest7)
    (h4 : X.reg 4 = Glyph.cons) :
    ∃ (Y : State) (n : ℕ), n ≤ 5 * (g.length + w.length) + 9 ∧ Eval main joinBody X Y n ∧
      Y.stk 0 = outPair w g ++ acc ∧ Y.stk 2 = rest2 ∧ Y.stk 3 = rest3 ∧
      Y.stk 6 = rest6 ∧ Y.stk 7 = rest7 ∧ Y.reg 4 = X.reg 4 ∧
      Y.reg 1 = (Y.stk 6).headD Glyph.eos ∧
      ∀ k : Stk, k ≠ 0 → k ≠ 2 → k ≠ 3 → k ≠ 6 → k ≠ 7 → Y.stk k = X.stk k := by
  obtain ⟨Y1, n1, hn1, he1, hY1_0, hY1_6, hY1_2, hY1_fr⟩ :=
    blkLoopEval main X 6 2 g.length g.reverse (jdelim :: rest6) rest2
      (by simp) (by simp) (by decide) (by decide) (by decide) h6 h2
  have ht : g.reverse.take g.length = g.reverse := by
    apply List.take_of_length_le; simp
  have hdropg : g.reverse.drop g.length = [] := by
    apply List.drop_eq_nil_of_le; simp
  have hY1_0' : Y1.stk 0 = g ++ acc := by rw [hY1_0, ht, List.reverse_reverse, h0]
  have hY1_3 : Y1.stk 3 = X.stk 3 := hY1_fr 3 (by decide) (by decide) (by decide)
  have hY1_7 : Y1.stk 7 = X.stk 7 := hY1_fr 7 (by decide) (by decide) (by decide)
  have hY1_r4 : Y1.reg 4 = X.reg 4 := Work.IntLib.UR.Eval_reg_frame he1 (by decide)
  have he2 : Eval main (.pop 6 1) Y1 (State.tPop Y1 6 1) 1 := Eval.pop 6 1 Y1
  have e2_0 : (State.tPop Y1 6 1).stk 0 = g ++ acc := by
    rw [tPop_stk_ne Y1 6 0 1 (by decide), hY1_0']
  have e2_2 : (State.tPop Y1 6 1).stk 2 = rest2 := by
    rw [tPop_stk_ne Y1 6 2 1 (by decide), hY1_2]
    simp [hdropg]
  have e2_3 : (State.tPop Y1 6 1).stk 3 = w.reverse ++ rest3 := by
    rw [tPop_stk_ne Y1 6 3 1 (by decide), hY1_3, h3]
  have e2_6 : (State.tPop Y1 6 1).stk 6 = rest6 := by
    rw [tPop_stk_tail, hY1_6, List.tail_cons]
  have e2_7 : (State.tPop Y1 6 1).stk 7 = List.replicate w.length jtok ++ jdelim :: rest7 := by
    rw [tPop_stk_ne Y1 6 7 1 (by decide), hY1_7, h7]
  have e2_r4 : (State.tPop Y1 6 1).reg 4 = X.reg 4 := by
    rw [tPop_reg_ne Y1 6 1 4 (by decide), hY1_r4]
  obtain ⟨Y3, n3, hn3, he3, hY3_0, hY3_7, hY3_3, hY3_fr⟩ :=
    blkLoopEval main (State.tPop Y1 6 1) 7 3 w.length w.reverse (jdelim :: rest7) rest3
      (by simp) (by simp) (by decide) (by decide) (by decide) e2_7 e2_3
  have hw : w.reverse.take w.length = w.reverse := by
    apply List.take_of_length_le; simp
  have hdropw : w.reverse.drop w.length = [] := by
    apply List.drop_eq_nil_of_le; simp
  have hY3_0' : Y3.stk 0 = w ++ (g ++ acc) := by rw [hY3_0, hw, List.reverse_reverse, e2_0]
  have hY3_2 : Y3.stk 2 = rest2 := by
    rw [hY3_fr 2 (by decide) (by decide) (by decide), e2_2]
  have hY3_6 : Y3.stk 6 = rest6 := by
    rw [hY3_fr 6 (by decide) (by decide) (by decide), e2_6]
  have hY3_r4 : Y3.reg 4 = X.reg 4 := by
    rw [Work.IntLib.UR.Eval_reg_frame he3 (by decide), e2_r4]
  have he4 : Eval main (.pop 7 1) Y3 (State.tPop Y3 7 1) 1 := Eval.pop 7 1 Y3
  have e4_0 : (State.tPop Y3 7 1).stk 0 = w ++ g ++ acc := by
    rw [tPop_stk_ne Y3 7 0 1 (by decide), hY3_0', List.append_assoc]
  have e4_2 : (State.tPop Y3 7 1).stk 2 = rest2 := by
    rw [tPop_stk_ne Y3 7 2 1 (by decide), hY3_2]
  have e4_3 : (State.tPop Y3 7 1).stk 3 = rest3 := by
    rw [tPop_stk_ne Y3 7 3 1 (by decide), hY3_3]
    simp [hdropw]
  have e4_6 : (State.tPop Y3 7 1).stk 6 = rest6 := by
    rw [tPop_stk_ne Y3 7 6 1 (by decide), hY3_6]
  have e4_7 : (State.tPop Y3 7 1).stk 7 = rest7 := by
    rw [tPop_stk_tail, hY3_7, List.tail_cons]
  have e4_r4 : (State.tPop Y3 7 1).reg 4 = X.reg 4 := by
    rw [tPop_reg_ne Y3 7 1 4 (by decide), hY3_r4]
  have he5 : Eval main (.push 0 4) (State.tPop Y3 7 1)
      (State.tPush (State.tPop Y3 7 1) 0 4) 1 := Eval.push 0 4 _
  have e5_0 : (State.tPush (State.tPop Y3 7 1) 0 4).stk 0
      = Glyph.cons :: (w ++ g ++ acc) := by
    rw [tPush_stk_self, e4_r4, h4, e4_0]
  have he6 : Eval main (.push 0 4) (State.tPush (State.tPop Y3 7 1) 0 4)
      (State.tPush (State.tPush (State.tPop Y3 7 1) 0 4) 0 4) 1 := Eval.push 0 4 _
  have e6_0 : (State.tPush (State.tPush (State.tPop Y3 7 1) 0 4) 0 4).stk 0
      = Glyph.cons :: Glyph.cons :: (w ++ g ++ acc) := by
    rw [tPush_stk_self, tPush_reg, e4_r4, h4, tPush_stk_self, e4_r4, h4, e4_0]
  have he7 : Eval main (.peek 6 1)
      (State.tPush (State.tPush (State.tPop Y3 7 1) 0 4) 0 4)
      (State.tPeek (State.tPush (State.tPush (State.tPop Y3 7 1) 0 4) 0 4) 6 1) 1 :=
    Eval.peek 6 1 _
  have hEval : Eval main joinBody X
      (State.tPeek (State.tPush (State.tPush (State.tPop Y3 7 1) 0 4) 0 4) 6 1) _ :=
    Eval.seq he1 (Eval.seq he2 (Eval.seq he3 (Eval.seq he4 (Eval.seq he5 (Eval.seq he6 he7)))))
  refine ⟨State.tPeek (State.tPush (State.tPush (State.tPop Y3 7 1) 0 4) 0 4) 6 1,
    _, ?_, hEval, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [tPeek_stk', e6_0]; simp [outPair]
  · rw [tPeek_stk', tPush_stk_ne _ 0 2 _ (by decide), tPush_stk_ne _ 0 2 _ (by decide),
      tPop_stk_ne _ 7 2 _ (by decide), hY3_2]
  · rw [tPeek_stk', tPush_stk_ne _ 0 3 _ (by decide), tPush_stk_ne _ 0 3 _ (by decide),
      tPop_stk_ne _ 7 3 _ (by decide), hY3_3]; simp [hdropw]
  · rw [tPeek_stk', tPush_stk_ne _ 0 6 _ (by decide), tPush_stk_ne _ 0 6 _ (by decide),
      tPop_stk_ne _ 7 6 _ (by decide), hY3_6]
  · rw [tPeek_stk', tPush_stk_ne _ 0 7 _ (by decide), tPush_stk_ne _ 0 7 _ (by decide),
      tPop_stk_tail, hY3_7, List.tail_cons]
  · exact Work.IntLib.UR.Eval_reg_frame hEval (by decide)
  · rw [tPeek_reg', tPeek_stk', tPush_stk_ne _ 0 6 _ (by decide),
      tPush_stk_ne _ 0 6 _ (by decide), tPop_stk_ne _ 7 6 _ (by decide), hY3_6]
  · intro k hk0 hk2 hk3 hk6 hk7
    rw [tPeek_stk', tPush_stk_ne _ 0 k _ hk0, tPush_stk_ne _ 0 k _ hk0,
      tPop_stk_ne _ 7 k _ hk7, hY3_fr k hk0 hk7 hk3, tPop_stk_ne _ 6 k _ hk6,
      hY1_fr k hk0 hk6 hk2]

/-! ## The bare interleaving loop -/

theorem joinLoopBody_eval (main : Cmd) : ∀ (rs : List (List Glyph × List Glyph)) (X : State)
    (acc : List Glyph) (rest2 rest3 rest6 rest7 : List Glyph),
    X.stk 0 = acc → X.stk 2 = bufGs rs ++ rest2 → X.stk 3 = bufWs rs ++ rest3 →
    X.stk 6 = cntGs rs ++ jcb :: rest6 → X.stk 7 = cntWs rs ++ jcb :: rest7 →
    X.reg 4 = Glyph.cons → X.reg 1 = (X.stk 6).headD Glyph.eos →
    (∀ p ∈ rs, p.1 ≠ []) →
    ∃ (Y : State) (n : ℕ), n ≤ jcostL rs ∧ Eval main (.loop 1 jtok joinBody) X Y n ∧
      Y.stk 0 = outsOf rs ++ acc ∧ Y.stk 2 = rest2 ∧ Y.stk 3 = rest3 ∧
      Y.stk 6 = jcb :: rest6 ∧ Y.stk 7 = jcb :: rest7 ∧
      ∀ k : Stk, k ≠ 0 → k ≠ 2 → k ≠ 3 → k ≠ 6 → k ≠ 7 → Y.stk k = X.stk k := by
  intro rs
  induction rs with
  | nil =>
      intro X acc rest2 rest3 rest6 rest7 h0 h2 h3 h6 h7 h4 h1 hne
      have h6' : X.stk 6 = jcb :: rest6 := h6
      have h1' : X.reg 1 ≠ jtok := by
        rw [h1, h6']
        simp
      refine ⟨X, 1, ?_, Eval.loopF h1', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [jcostL]
      · rw [outsOf_nil, List.nil_append]; exact h0
      · rw [h2]; rfl
      · rw [h3]; rfl
      · exact h6'
      · rw [h7]; rfl
      · intro k hk0 hk2 hk3 hk6 hk7; rfl
  | cons p rs ih =>
      intro X acc rest2 rest3 rest6 rest7 h0 h2 h3 h6 h7 h4 h1 hne
      have hp : p.1 ≠ [] := hne p (by simp)
      have hne' : ∀ q ∈ rs, q.1 ≠ [] := fun q hq => hne q (by simp [hq])
      have hlen : p.1.length ≠ 0 := fun hh => hp (List.length_eq_zero_iff.mp hh)
      have h6blk : X.stk 6
          = List.replicate p.1.length jtok ++ jdelim :: (cntGs rs ++ jcb :: rest6) := by
        rw [h6, cntGs_cons, blkCnt]
        simp [List.append_assoc]
      have h1tok : X.reg 1 = jtok := by
        rw [h1, h6blk]
        exact headD_replicate _ _ hlen
      obtain ⟨Y1, nb, hnb, heb, hY1_0, hY1_2, hY1_3, hY1_6, hY1_7, hY1_r4, hY1_r1,
        hY1_fr⟩ :=
        joinBody_eval main X acc p.1 p.2 (bufGs rs ++ rest2) (bufWs rs ++ rest3)
          (cntGs rs ++ jcb :: rest6) (cntWs rs ++ jcb :: rest7) h0
          (by rw [h2, bufGs_cons, List.append_assoc])
          (by rw [h3, bufWs_cons, List.append_assoc])
          h6blk
          (by rw [h7, cntWs_cons, blkCnt]; simp [List.append_assoc]) h4
      obtain ⟨Y2, nl, hnl, hel, hY2_0, hY2_2, hY2_3, hY2_6, hY2_7, hY2_fr⟩ :=
        ih Y1 (Pm p ++ acc) rest2 rest3 rest6 rest7 hY1_0 hY1_2 hY1_3 hY1_6 hY1_7
          (by rw [hY1_r4, h4]) hY1_r1 hne'
      have hEval : Eval main (.loop 1 jtok joinBody) X Y2 _ := Eval.loopT h1tok heb hel
      refine ⟨Y2, _, ?_, hEval, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [jcostL_cons]; omega
      · rw [hY2_0, outsOf_cons]; simp [List.append_assoc]
      · exact hY2_2
      · exact hY2_3
      · exact hY2_6
      · exact hY2_7
      · intro k hk0 hk2 hk3 hk6 hk7
        rw [hY2_fr k hk0 hk2 hk3 hk6 hk7]
        exact hY1_fr k hk0 hk2 hk3 hk6 hk7

/-! ## The interleaving loop (with its initial `peek`) -/

theorem joinLoop_eval (main : Cmd) (X : State) (acc : List Glyph)
    (rs : List (List Glyph × List Glyph)) (rest2 rest3 rest6 rest7 : List Glyph)
    (h0 : X.stk 0 = acc) (h2 : X.stk 2 = bufGs rs ++ rest2) (h3 : X.stk 3 = bufWs rs ++ rest3)
    (h6 : X.stk 6 = cntGs rs ++ jcb :: rest6) (h7 : X.stk 7 = cntWs rs ++ jcb :: rest7)
    (h4 : X.reg 4 = Glyph.cons) (hne : ∀ p ∈ rs, p.1 ≠ []) :
    ∃ (Y : State) (n : ℕ), n ≤ jcost rs ∧ Eval main joinLoop X Y n ∧
      Y.stk 0 = outsOf rs ++ acc ∧ Y.stk 2 = rest2 ∧ Y.stk 3 = rest3 ∧
      Y.stk 6 = jcb :: rest6 ∧ Y.stk 7 = jcb :: rest7 ∧
      ∀ k : Stk, k ≠ 0 → k ≠ 2 → k ≠ 3 → k ≠ 6 → k ≠ 7 → Y.stk k = X.stk k := by
  obtain ⟨Y1, n1, hn1, he1, hY1_0, hY1_2, hY1_3, hY1_6, hY1_7, hY1_fr⟩ :=
    joinLoopBody_eval main rs (State.tPeek X 6 1) acc rest2 rest3 rest6 rest7
      (by rw [tPeek_stk']; exact h0)
      (by rw [tPeek_stk']; exact h2)
      (by rw [tPeek_stk']; exact h3)
      (by rw [tPeek_stk']; exact h6)
      (by rw [tPeek_stk']; exact h7)
      (by rw [Work.Kernel.dropValue_tPeek_reg]; simp [h4])
      (by rw [tPeek_reg', tPeek_stk'])
      hne
  have hEval : Eval main joinLoop X Y1 _ := Eval.seq (Eval.peek 6 1 X) he1
  refine ⟨Y1, _, ?_, hEval, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [jcost]; omega
  · exact hY1_0
  · exact hY1_2
  · exact hY1_3
  · exact hY1_6
  · exact hY1_7
  · intro k hk0 hk2 hk3 hk6 hk7
    rw [hY1_fr k hk0 hk2 hk3 hk6 hk7, tPeek_stk']

/-! ## The whole interleaving phase -/

theorem crtJoinPhase (main : HvdH.Cmd) (s : HvdH.State)
    (Ws Gs : List (List HvdH.Glyph)) (t : List HvdH.Glyph) (hlen : Ws.length = Gs.length)
    (hG : ∀ G ∈ Gs, G ≠ []) :
    ∃ (s' : HvdH.State) (n : ℕ),
      n ≤ 20 * ((Ws.map List.length).sum + (Gs.map List.length).sum + Ws.length + Gs.length + 1) + 10 ∧
      HvdH.Eval main Work.MainP.joinPhase (Work.MainP.jpPre s Ws Gs t) s' n ∧
      s'.stk 0 = Work.MainP.outGlyphs Ws Gs ++ t ∧
      ∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = s.stk k := by
  set Ps : List (List Glyph × List Glyph) := Gs.reverse.zip Ws.reverse with hPs
  have hbufG : bufGs Ps = bufReg Gs := by rw [hPs]; exact bufGs_spairs Gs Ws hlen
  have hbufW : bufWs Ps = bufReg Ws := by rw [hPs]; exact bufWs_spairs Gs Ws hlen
  have hcntG : cntGs Ps = cntReg Gs := by rw [hPs]; exact cntGs_spairs Gs Ws hlen
  have hcntW : cntWs Ps = cntReg Ws := by rw [hPs]; exact cntWs_spairs Gs Ws hlen
  have houts : outsOf Ps = (List.zipWith outPair Ws Gs).flatten := by
    rw [hPs]; exact outsOf_spairs Gs Ws hlen
  have hlenPs : Ps.length = Gs.length := by rw [hPs]; exact length_spairs Gs Ws hlen
  have hsumPs : (Ps.map (fun p => p.1.length + p.2.length)).sum
      = (Gs.map List.length).sum + (Ws.map List.length).sum := by
    rw [hPs]; exact sum_spairs Gs Ws hlen
  have hne : ∀ p ∈ Ps, p.1 ≠ [] := by
    intro p hp
    rw [hPs] at hp
    exact hG p.1 (List.mem_reverse.mp (mem_fst_zip_aux hp))
  set X0 : State := jpPre s Ws Gs t with hX0
  have hX0_0 : X0.stk 0 = t := by rw [hX0]; simp [jpPre]
  have hX0_2 : X0.stk 2 = bufReg Gs ++ s.stk 2 := by rw [hX0]; simp [jpPre]
  have hX0_3 : X0.stk 3 = bufReg Ws ++ s.stk 3 := by rw [hX0]; simp [jpPre]
  have hX0_6 : X0.stk 6 = cntReg Gs ++ jcb :: s.stk 6 := by rw [hX0]; simp [jpPre]
  have hX0_7 : X0.stk 7 = cntReg Ws ++ jcb :: s.stk 7 := by rw [hX0]; simp [jpPre]
  have hX0_oth : ∀ k : Stk, k ≠ 0 → k ≠ 2 → k ≠ 3 → k ≠ 6 → k ≠ 7 → X0.stk k = s.stk k := by
    intro k h0 h2 h3 h6 h7
    rw [hX0]
    simp [jpPre, State.updStk, h0, h2, h3, h6, h7]
  set X1 : State := State.tSet X0 4 Glyph.cons with hX1
  set X2 : State := State.tSet X1 2 Glyph.nil with hX2
  set X3 : State := State.tPush X2 0 2 with hX3
  have hreg2 : X2.reg 2 = Glyph.nil := by
    rw [hX2, hX1]
    exact tSet_reg_self (State.tSet X0 4 Glyph.cons) 2 Glyph.nil
  have hX3_0 : X3.stk 0 = Glyph.nil :: t := by
    rw [hX3, tPush_stk_self, hreg2, hX2, hX1, tSet_stk', tSet_stk', hX0_0]
  have hX3_2 : X3.stk 2 = bufReg Gs ++ s.stk 2 := by
    rw [hX3, tPush_stk_ne _ 0 2 _ (by decide), hX2, hX1, tSet_stk', tSet_stk', hX0_2]
  have hX3_3 : X3.stk 3 = bufReg Ws ++ s.stk 3 := by
    rw [hX3, tPush_stk_ne _ 0 3 _ (by decide), hX2, hX1, tSet_stk', tSet_stk', hX0_3]
  have hX3_6 : X3.stk 6 = cntReg Gs ++ jcb :: s.stk 6 := by
    rw [hX3, tPush_stk_ne _ 0 6 _ (by decide), hX2, hX1, tSet_stk', tSet_stk', hX0_6]
  have hX3_7 : X3.stk 7 = cntReg Ws ++ jcb :: s.stk 7 := by
    rw [hX3, tPush_stk_ne _ 0 7 _ (by decide), hX2, hX1, tSet_stk', tSet_stk', hX0_7]
  have hX3_4 : X3.reg 4 = Glyph.cons := by
    rw [hX3, tPush_reg, hX2, Work.Kernel.dropValue_compSet_reg, hX1,
      Work.Kernel.dropValue_compSet_reg]
    simp
  have hX3_oth : ∀ k : Stk, k ≠ 0 → k ≠ 2 → k ≠ 3 → k ≠ 6 → k ≠ 7 → X3.stk k = s.stk k := by
    intro k h0 h2 h3 h6 h7
    rw [hX3, tPush_stk_ne _ 0 k _ h0, hX2, hX1, tSet_stk', tSet_stk']
    exact hX0_oth k h0 h2 h3 h6 h7
  obtain ⟨Y, nl, hnl, hel, hY0, hY2, hY3, hY6, hY7, hYfr⟩ :=
    joinLoop_eval main X3 (Glyph.nil :: t) Ps (s.stk 2) (s.stk 3) (s.stk 6) (s.stk 7)
      hX3_0 (by rw [hX3_2, hbufG]) (by rw [hX3_3, hbufW])
      (by rw [hX3_6, hcntG]) (by rw [hX3_7, hcntW]) hX3_4 hne
  have hset1 : Eval main (.set 4 Glyph.cons) X0 X1 1 := Eval.set 4 Glyph.cons X0
  have hset2 : Eval main (.set 2 Glyph.nil) X1 X2 1 := Eval.set 2 Glyph.nil X1
  have hpush : Eval main (.push 0 2) X2 X3 1 := Eval.push 0 2 X2
  have hpop1 : Eval main (.pop 6 1) Y (State.tPop Y 6 1) 1 := Eval.pop 6 1 Y
  have hpop2 : Eval main (.pop 7 1) (State.tPop Y 6 1) (State.tPop (State.tPop Y 6 1) 7 1) 1 :=
    Eval.pop 7 1 _
  have hEval : Eval main joinPhase X0 (State.tPop (State.tPop Y 6 1) 7 1) _ :=
    Eval.seq hset1 (Eval.seq hset2 (Eval.seq hpush (Eval.seq hel (Eval.seq hpop1 hpop2))))
  refine ⟨State.tPop (State.tPop Y 6 1) 7 1, _, ?_, hEval, ?_, ?_⟩
  · rw [jcost, jcostL, hsumPs, hlenPs] at hnl
    omega
  · rw [tPop_stk_ne _ 7 0 _ (by decide), tPop_stk_ne _ 6 0 _ (by decide), hY0, houts,
      zipWith_outPair_elim, outGlyphs, List.append_assoc]
    rfl
  · intro k hk0
    by_cases hk6 : k = 6
    · subst hk6
      rw [tPop_stk_ne _ 7 6 _ (by decide), tPop_stk_tail, hY6, List.tail_cons]
    · by_cases hk7 : k = 7
      · subst hk7
        rw [tPop_stk_tail, tPop_stk_ne _ 6 7 _ (by decide), hY7, List.tail_cons]
      · rw [tPop_stk_ne _ 7 k _ hk7, tPop_stk_ne _ 6 k _ hk6]
        by_cases hk2 : k = 2
        · subst hk2; exact hY2
        · by_cases hk3 : k = 3
          · subst hk3; exact hY3
          · rw [hYfr k hk0 hk2 hk3 hk6 hk7]
            exact hX3_oth k hk0 hk2 hk3 hk6 hk7


end Work.MainP
