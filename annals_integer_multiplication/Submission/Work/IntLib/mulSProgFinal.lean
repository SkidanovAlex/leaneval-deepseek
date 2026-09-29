import Submission.Work.IntLib.mulSDefs
import Submission.Work.IntLib.mulSEv
import Submission.Work.IntLib.mulSArith
import Submission.Work.IntLib.mulSProgEv

/-!
# The final phase `finalizeProg`

`finalizeProg` turns the accumulated output bits on `sC` (most significant on top) and the leftover
high bits `ρ` on `sR` into the encoding of the product on stack 0, and pushes the sign glyph on top
of it.  The bits are stripped of their leading zeros (`stripProg`), and the sign is the parity of
the two stored sign glyphs, overridden to `pos` when the product is `0`.
-/

set_option autoImplicit false
open HvdH

namespace Work.IntLib
open MulS

/-- Body of the `stripProg` loop: drop a leading `bit false`, stop otherwise. -/
def stripBody : Cmd :=
  .seq (.peek sC rTmp)
    (.ite rTmp (.bit false) (.seq (.pop sC rTmp) (.set rL .eos)) (.set rL mkStop))

/-- `stripProg`'s loop drops the leading `false` bits of `sC` (i.e. the high zeros). -/
theorem strip_ev {main : Cmd} {belowC : List Glyph} (W : List Bool) :
    ∀ (s : State), s.stk sC = W.map Glyph.bit ++ [mkC] ++ belowC → s.reg rL = Glyph.eos →
    ∃ s' n, Eval main (.loop rL Glyph.eos stripBody) s s' n ∧ n ≤ 5 * W.length + 5 ∧
      s'.stk sC = (W.dropWhile (fun b => !b)).map Glyph.bit ++ [mkC] ++ belowC ∧
      (∀ k, k ≠ sC → s'.stk k = s.stk k) ∧ s'.reg rL = mkStop := by
  induction W with
  | nil =>
    intro s hC hrL
    have hC' : s.stk sC = mkC :: belowC := by rw [hC]; simp
    let S1 : State := ⟨Function.update s.reg rTmp mkC, s.stk⟩
    have e1 : Eval main (.peek sC rTmp) s S1 1 := by
      dsimp only [S1]; simpa [hC'] using Eval.peek sC rTmp s
    have hS1rt : S1.reg rTmp = mkC := by simp [S1]
    let S2 : State := ⟨Function.update S1.reg rL mkStop, S1.stk⟩
    have e2 : Eval main (.set rL mkStop) S1 S2 1 := by dsimp only [S2]; exact Eval.set rL mkStop S1
    have hne : S1.reg rTmp ≠ Glyph.bit false := by rw [hS1rt]; intro h; cases h
    have hite : Eval main (.ite rTmp (.bit false) (.seq (.pop sC rTmp) (.set rL .eos))
        (.set rL mkStop)) S1 S2 2 := Eval.iteF hne e2
    have hbody : Ev main stripBody s S2 3 := Ev.seq (ev_of_eval e1) (ev_of_eval hite)
    have hstop : S2.reg rL ≠ Glyph.eos := by simp +decide [S2, S1]
    have hloopF : Ev main (.loop rL Glyph.eos stripBody) S2 S2 1 := Ev.loopF hstop
    obtain ⟨n, hev, hn⟩ := Ev.loopT hrL hbody hloopF
    refine ⟨S2, n, hev, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_nil, Nat.mul_zero]; omega
    · change S2.stk sC = mkC :: belowC
      dsimp only [S2, S1]; exact hC'
    · intro k hk; dsimp only [S2, S1]
    · simp +decide [S2, S1]
  | cons b W' ih =>
    intro s hC hrL
    have hC' : s.stk sC = Glyph.bit b :: (W'.map Glyph.bit ++ [mkC] ++ belowC) := by
      rw [hC]
      simp only [List.map_cons, List.cons_append, List.append_assoc, List.singleton_append]
    let S1 : State := ⟨Function.update s.reg rTmp (Glyph.bit b), s.stk⟩
    have e1 : Eval main (.peek sC rTmp) s S1 1 := by
      dsimp only [S1]; simpa [hC'] using Eval.peek sC rTmp s
    have hS1rt : S1.reg rTmp = Glyph.bit b := by simp [S1]
    cases b with
    | false =>
      let S2 : State := ⟨Function.update S1.reg rTmp (Glyph.bit false),
        Function.update S1.stk sC (W'.map Glyph.bit ++ [mkC] ++ belowC)⟩
      have e2 : Eval main (.pop sC rTmp) S1 S2 1 := by
        dsimp only [S2]; simpa [S1, hC'] using Eval.pop sC rTmp S1
      let S3 : State := ⟨Function.update S2.reg rL Glyph.eos, S2.stk⟩
      have e3 : Eval main (.set rL Glyph.eos) S2 S3 1 := by
        dsimp only [S3]; exact Eval.set rL Glyph.eos S2
      have hite : Eval main (.ite rTmp (.bit false) (.seq (.pop sC rTmp) (.set rL .eos))
          (.set rL mkStop)) S1 S3 3 := by
        refine Eval.iteT ?_ (Eval.seq e2 e3)
        simpa using hS1rt
      have hbody : Ev main stripBody s S3 4 := Ev.seq (ev_of_eval e1) (ev_of_eval hite)
      have hS3rL : S3.reg rL = Glyph.eos := by simp [S3]
      have hS3C : S3.stk sC = W'.map Glyph.bit ++ [mkC] ++ belowC := by simp [S3, S2]
      obtain ⟨s', n', hev', hn', gC, gfr, gL⟩ := ih S3 hS3C hS3rL
      obtain ⟨n, hev, hn⟩ := Ev.loopT hrL hbody (ev_of_eval hev')
      refine ⟨s', n, hev, ?_, ?_, ?_, gL⟩
      · have h : n ≤ (4 : ℕ) + n' + 1 := hn
        simp only [List.length_cons]; omega
      · change s'.stk sC = ((false :: W').dropWhile (fun b => !b)).map Glyph.bit ++ [mkC] ++ belowC
        rw [List.dropWhile_cons]
        simp only [Bool.not_false, if_true]
        exact gC
      · intro k hk
        rw [gfr k hk]
        dsimp only [S3, S2, S1]
        rw [Function.update_of_ne (show k ≠ sC from hk)]
    | true =>
      let S2 : State := ⟨Function.update S1.reg rL mkStop, S1.stk⟩
      have e2 : Eval main (.set rL mkStop) S1 S2 1 := by
        dsimp only [S2]; exact Eval.set rL mkStop S1
      have hne : S1.reg rTmp ≠ Glyph.bit false := by rw [hS1rt]; intro h; cases h
      have hite : Eval main (.ite rTmp (.bit false) (.seq (.pop sC rTmp) (.set rL .eos))
          (.set rL mkStop)) S1 S2 2 := Eval.iteF hne e2
      have hbody : Ev main stripBody s S2 3 := Ev.seq (ev_of_eval e1) (ev_of_eval hite)
      have hstop : S2.reg rL ≠ Glyph.eos := by simp +decide [S2, S1]
      have hloopF : Ev main (.loop rL Glyph.eos stripBody) S2 S2 1 := Ev.loopF hstop
      obtain ⟨n, hev, hn⟩ := Ev.loopT hrL hbody hloopF
      refine ⟨S2, n, hev, ?_, ?_, ?_, ?_⟩
      · have h : n ≤ (3 : ℕ) + 1 + 1 := hn
        simp only [List.length_cons]; omega
      · change S2.stk sC = ((true :: W').dropWhile (fun b => !b)).map Glyph.bit ++ [mkC] ++ belowC
        rw [List.dropWhile_cons]
        simp only [Bool.not_true, if_false, List.map_cons, List.cons_append]
        exact hC'
      · intro k hk; dsimp only [S2, S1]
      · simp +decide [S2, S1]

/-- Head of the stripped bit list: the marker exactly when everything was stripped. -/
private theorem headD_strip (F : List Bool) (B : List Glyph) :
    ((((F.reverse).dropWhile (fun b => !b)).map Glyph.bit) ++ [mkC] ++ B).headD Glyph.eos
      = (if (F.reverse).dropWhile (fun b => !b) = [] then mkC else Glyph.bit true) := by
  rcases or_head?_dropWhile F.reverse with h | h
  · rw [List.head?_eq_none_iff.mp h]; simp
  · obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp h
    rw [ht]; simp

/-- `stripProg` drops the leading `false` bits of `sC`. -/
theorem stripProg_ev {main : Cmd} {belowC : List Glyph} (W : List Bool) (s : State)
    (hC : s.stk sC = W.map Glyph.bit ++ [mkC] ++ belowC) :
    ∃ s' n, Eval main stripProg s s' n ∧ n ≤ 5 * W.length + 7 ∧
      s'.stk sC = (W.dropWhile (fun b => !b)).map Glyph.bit ++ [mkC] ++ belowC ∧
      (∀ k, k ≠ sC → s'.stk k = s.stk k) ∧ s'.reg rL = mkStop := by
  have e0 : Eval main (.set rL Glyph.eos) s ⟨Function.update s.reg rL Glyph.eos, s.stk⟩ 1 :=
    Eval.set rL Glyph.eos s
  obtain ⟨s', n, hev, hn, gC, gfr, gL⟩ :=
    strip_ev (main := main) (belowC := belowC) W
      ⟨Function.update s.reg rL Glyph.eos, s.stk⟩ hC (by simp)
  have hprog : stripProg = .seq (.set rL Glyph.eos) (.loop rL Glyph.eos stripBody) := by
    simp only [stripProg, seqs, stripBody]
  have hchain : Eval main stripProg s s' (1 + n) := by
    rw [hprog]; exact Eval.seq e0 hev
  exact ⟨s', 1 + n, hchain, by omega, gC, gfr, gL⟩
theorem mulSProgFinal {main : Cmd} {s : State} {acc rho : List Bool} {sa sb : Glyph}
    {below0 : List Glyph} {belowR belowC belowS belowT belowU : List Glyph}
    (h0 : s.stk 0 = below0)
    (hR : s.stk sR = rho.map Glyph.bit ++ [mkR] ++ belowR)
    (hC : s.stk sC = acc.map Glyph.bit ++ [mkC] ++ belowC)
    (hS : s.stk sS = sb :: sa :: [mkS] ++ belowS)
    (hT : s.stk sT = [mkT] ++ belowT) (hU : s.stk sU = [mkU] ++ belowU)
    (hIe : s.reg rIe = Glyph.iend) :
    ∃ s' n, Eval main finalizeProg s s' n ∧
      n ≤ 60 * (acc.length + rho.length + 1) + 60 ∧
      s'.stk 0 = (if stripHigh (acc.reverse ++ rho) = [] then Glyph.pos
            else if sa = Glyph.neg then (if sb = Glyph.neg then Glyph.pos else Glyph.neg)
            else (if sb = Glyph.neg then Glyph.neg else Glyph.pos))
          :: (stripHigh (acc.reverse ++ rho)).map Glyph.bit ++ [Glyph.iend] ++ below0 ∧
      s'.stk sR = [mkR] ++ belowR ∧ s'.stk sC = [mkC] ++ belowC ∧
      s'.stk sS = belowS ∧ s'.stk sT = [mkT] ++ belowT ∧ s'.stk sU = [mkU] ++ belowU ∧
      (∀ k : Stk, k ≠ 0 → k ≠ sR → k ≠ sC → k ≠ sS → k ≠ sT → k ≠ sU →
        s'.stk k = s.stk k) := by
  -- ## step 1 : sR -> sT
  have hws1 : ∀ g ∈ rho.map Glyph.bit, g ≠ mkR := by
    intro g hg; obtain ⟨x, -, rfl⟩ := List.mem_map.mp hg; intro h; cases h
  have hR' : s.stk sR = rho.map Glyph.bit ++ mkR :: belowR := by
    simp only [hR, List.append_assoc, List.singleton_append]
  obtain ⟨S1, n1, hev1, hn1, h1R, h1T, h1fr⟩ :=
    drain_ev' (main := main) (src := sR) (dst := sT) (hne := (by decide : sR ≠ sT))
      (T := mkR) (r := rL) (below := belowR) (rho.map Glyph.bit) ([mkT] ++ belowT) s hR' hT hws1
  have e1 : Ev main (consume sR mkR rL (.push sT rL)) s S1 (5 * (rho.length + 1) + 2) := by
    refine Ev.mono (ev_of_eval hev1) ?_
    simp only [List.length_map] at hn1; exact hn1
  have h1ie : S1.reg rIe = Glyph.iend := by
    rw [eval_reg_frame hev1 (by decide : rIe ∉ cmdRegs (drain sR sT mkR rL))]; exact hIe
  have h1T' : S1.stk sT = (rho.map Glyph.bit).reverse ++ mkT :: belowT := by
    simp only [h1T, List.append_assoc, List.singleton_append]
  have h1U : S1.stk sU = [mkU] ++ belowU := by
    rw [h1fr sU (by decide) (by decide)]; exact hU
  -- ## step 2 : sT -> sU
  have hws2 : ∀ g ∈ (rho.map Glyph.bit).reverse, g ≠ mkT := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hg)
    intro h; cases h
  obtain ⟨S2, n2, hev2, hn2, h2T, h2U, h2fr⟩ :=
    drain_ev' (main := main) (src := sT) (dst := sU) (hne := (by decide : sT ≠ sU))
      (T := mkT) (r := rL) (below := belowT) ((rho.map Glyph.bit).reverse) ([mkU] ++ belowU)
      S1 h1T' h1U hws2
  have e2 : Ev main (consume sT mkT rL (.push sU rL)) S1 S2 (5 * (rho.length + 1) + 2) := by
    refine Ev.mono (ev_of_eval hev2) ?_
    simp only [List.length_reverse, List.length_map] at hn2; exact hn2
  have h2ie : S2.reg rIe = Glyph.iend := by
    rw [eval_reg_frame hev2 (by decide : rIe ∉ cmdRegs (drain sT sU mkT rL))]; exact h1ie
  have h2U' : S2.stk sU = rho.map Glyph.bit ++ [mkU] ++ belowU := by
    simp only [h2U, List.reverse_reverse, List.append_assoc]
  have h2R : S2.stk sR = mkR :: belowR := by
    rw [h2fr sR (by decide) (by decide)]; exact h1R
  have h2C : S2.stk sC = acc.map Glyph.bit ++ mkC :: belowC := by
    rw [h2fr sC (by decide) (by decide), h1fr sC (by decide) (by decide)]
    simp only [hC, List.append_assoc, List.singleton_append]
  -- ## step 3 : sC -> sU
  have hws3 : ∀ g ∈ acc.map Glyph.bit, g ≠ mkC := by
    intro g hg; obtain ⟨x, -, rfl⟩ := List.mem_map.mp hg; intro h; cases h
  obtain ⟨S3, n3, hev3, hn3, h3C, h3U, h3fr⟩ :=
    drain_ev' (main := main) (src := sC) (dst := sU) (hne := (by decide : sC ≠ sU))
      (T := mkC) (r := rL) (below := belowC) (acc.map Glyph.bit)
      (rho.map Glyph.bit ++ [mkU] ++ belowU) S2 h2C h2U' hws3
  have e3 : Ev main (consume sC mkC rL (.push sU rL)) S2 S3 (5 * (acc.length + 1) + 2) := by
    refine Ev.mono (ev_of_eval hev3) ?_
    simp only [List.length_map] at hn3; exact hn3
  have h3ie : S3.reg rIe = Glyph.iend := by
    rw [eval_reg_frame hev3 (by decide : rIe ∉ cmdRegs (drain sC sU mkC rL))]; exact h2ie
  have h3U' : S3.stk sU = (acc.reverse ++ rho).map Glyph.bit ++ [mkU] ++ belowU := by
    simp only [h3U, List.map_reverse, List.map_append, List.append_assoc]
  have h3R : S3.stk sR = mkR :: belowR := by
    rw [h3fr sR (by decide) (by decide)]; exact h2R
  have h3T : S3.stk sT = mkT :: belowT := by
    rw [h3fr sT (by decide) (by decide)]; exact h2T
  have h3S : S3.stk sS = sb :: sa :: [mkS] ++ belowS := by
    rw [h3fr sS (by decide) (by decide), h2fr sS (by decide) (by decide),
      h1fr sS (by decide) (by decide)]
    exact hS
  have h3_0 : S3.stk 0 = below0 := by
    rw [h3fr 0 (by decide) (by decide), h2fr 0 (by decide) (by decide),
      h1fr 0 (by decide) (by decide)]
    exact h0
  -- ## step 4 : sU -> sC
  have h3U'' : S3.stk sU = (acc.reverse ++ rho).map Glyph.bit ++ mkU :: belowU := by
    simp only [h3U', List.append_assoc, List.singleton_append]
  have hws4 : ∀ g ∈ (acc.reverse ++ rho).map Glyph.bit, g ≠ mkU := by
    intro g hg; obtain ⟨x, -, rfl⟩ := List.mem_map.mp hg; intro h; cases h
  obtain ⟨S4, n4, hev4, hn4, h4U, h4C, h4fr⟩ :=
    drain_ev' (main := main) (src := sU) (dst := sC) (hne := (by decide : sU ≠ sC))
      (T := mkU) (r := rL) (below := belowU) ((acc.reverse ++ rho).map Glyph.bit)
      (mkC :: belowC) S3 h3U'' h3C hws4
  have e4 : Ev main (consume sU mkU rL (.push sC rL)) S3 S4
      (5 * (acc.length + rho.length + 1) + 2) := by
    refine Ev.mono (ev_of_eval hev4) ?_
    simp only [List.length_map, List.length_append, List.length_reverse] at hn4; exact hn4
  have h4ie : S4.reg rIe = Glyph.iend := by
    rw [eval_reg_frame hev4 (by decide : rIe ∉ cmdRegs (drain sU sC mkU rL))]; exact h3ie
  have h4C' : S4.stk sC = ((acc.reverse ++ rho).reverse).map Glyph.bit ++ [mkC] ++ belowC := by
    simp only [h4C, List.map_reverse, List.append_assoc, List.singleton_append]
  have h4R : S4.stk sR = mkR :: belowR := by
    rw [h4fr sR (by decide) (by decide)]; exact h3R
  have h4T : S4.stk sT = mkT :: belowT := by
    rw [h4fr sT (by decide) (by decide)]; exact h3T
  have h4U' : S4.stk sU = mkU :: belowU := by simp only [h4U, List.singleton_append]
  have h4S : S4.stk sS = sb :: sa :: [mkS] ++ belowS := by
    rw [h4fr sS (by decide) (by decide)]; exact h3S
  have h4_0 : S4.stk 0 = below0 := by rw [h4fr 0 (by decide) (by decide)]; exact h3_0
  -- ## step 5 : stripProg
  obtain ⟨S5, n5, hev5, hn5, h5C, h5fr, h5L⟩ :=
    stripProg_ev (main := main) (belowC := belowC) ((acc.reverse ++ rho).reverse) S4 h4C'
  have e5 : Ev main stripProg S4 S5 (5 * (acc.length + rho.length) + 7) := by
    refine Ev.mono (ev_of_eval hev5) ?_
    simp only [List.length_reverse, List.length_append, List.length_reverse] at hn5; exact hn5
  have h5S : S5.stk sS = sb :: sa :: [mkS] ++ belowS := by
    rw [h5fr sS (by decide)]; exact h4S
  have h5R : S5.stk sR = mkR :: belowR := by rw [h5fr sR (by decide)]; exact h4R
  have h5T : S5.stk sT = mkT :: belowT := by rw [h5fr sT (by decide)]; exact h4T
  have h5U : S5.stk sU = mkU :: belowU := by rw [h5fr sU (by decide)]; exact h4U'
  have h5_0 : S5.stk 0 = below0 := by rw [h5fr 0 (by decide)]; exact h4_0
  have h5ie : S5.reg rIe = Glyph.iend := by
    rw [eval_reg_frame hev5 (by decide : rIe ∉ cmdRegs stripProg)]; exact h4ie
  -- ## step 6 : push the terminator
  let S6 : State := ⟨S5.reg, Function.update S5.stk 0 (Glyph.iend :: S5.stk 0)⟩
  have e6 : Ev main (.push 0 rIe) S5 S6 1 := by
    have hh : Eval main (.push 0 rIe) S5
        ⟨S5.reg, Function.update S5.stk 0 (Glyph.iend :: S5.stk 0)⟩ 1 := by
      have h : Eval main (.push 0 rIe) S5
          ⟨S5.reg, Function.update S5.stk 0 (S5.reg rIe :: S5.stk 0)⟩ 1 := Eval.push 0 rIe S5
      rw [h5ie] at h
      exact h
    dsimp only [S6]; exact ev_of_eval hh
  have h6S : S6.stk sS = sb :: sa :: [mkS] ++ belowS := by
    dsimp only [S6]
    rw [Function.update_of_ne (by decide : (sS : Stk) ≠ 0)]; exact h5S
  have h6_0 : S6.stk 0 = Glyph.iend :: below0 := by
    dsimp only [S6]; rw [Function.update_self, h5_0]
  -- ## step 7 : the sign
  let V : Glyph := if sa = Glyph.neg then (if sb = Glyph.neg then Glyph.pos else Glyph.neg)
    else (if sb = Glyph.neg then Glyph.neg else Glyph.pos)
  let T1 : State := ⟨Function.update S6.reg rBit sb, Function.update S6.stk sS (sa :: [mkS] ++ belowS)⟩
  have f1 : Eval main (.pop sS rBit) S6 T1 1 := by
    dsimp only [T1]; simpa [h6S] using Eval.pop sS rBit S6
  have gT1S : T1.stk sS = sa :: [mkS] ++ belowS := by simp [T1]
  let T2 : State := ⟨Function.update T1.reg rA sa, Function.update T1.stk sS ([mkS] ++ belowS)⟩
  have f2 : Eval main (.pop sS rA) T1 T2 1 := by
    dsimp only [T2]; simpa [gT1S] using Eval.pop sS rA T1
  have gT2S : T2.stk sS = [mkS] ++ belowS := by simp [T2]
  let T3 : State := ⟨Function.update T2.reg rTmp mkS, Function.update T2.stk sS belowS⟩
  have f3 : Eval main (.pop sS rTmp) T2 T3 1 := by
    dsimp only [T3]; simpa [gT2S] using Eval.pop sS rTmp T2
  have hT3bit : T3.reg rBit = sb := by simp +decide [T3, T2, T1]
  have hT3A : T3.reg rA = sa := by simp +decide [T3, T2, T1]
  let T4 : State := ⟨Function.update T3.reg rSign V, T3.stk⟩
  have f4 : Eval main
      (.ite rA Glyph.neg (.ite rBit Glyph.neg (.set rSign Glyph.pos) (.set rSign Glyph.neg))
        (.ite rBit Glyph.neg (.set rSign Glyph.neg) (.set rSign Glyph.pos))) T3 T4 3 := by
    by_cases hA : sa = Glyph.neg
    · have hA' : T3.reg rA = Glyph.neg := by rw [hT3A]; exact hA
      by_cases hB : sb = Glyph.neg
      · have hV : V = Glyph.pos := by simp only [V, if_pos hA, if_pos hB]
        have hset : Eval main (.set rSign Glyph.pos) T3
            ⟨Function.update T3.reg rSign V, T3.stk⟩ 1 := by
          rw [hV]; exact Eval.set rSign Glyph.pos T3
        exact Eval.iteT hA' (Eval.iteT (by rw [hT3bit]; exact hB) hset)
      · have hV : V = Glyph.neg := by simp only [V, if_pos hA, if_neg hB]
        have hset : Eval main (.set rSign Glyph.neg) T3
            ⟨Function.update T3.reg rSign V, T3.stk⟩ 1 := by
          rw [hV]; exact Eval.set rSign Glyph.neg T3
        exact Eval.iteT hA' (Eval.iteF (by rw [hT3bit]; exact hB) hset)
    · have hA' : T3.reg rA ≠ Glyph.neg := by rw [hT3A]; exact hA
      by_cases hB : sb = Glyph.neg
      · have hV : V = Glyph.neg := by simp only [V, if_neg hA, if_pos hB]
        have hset : Eval main (.set rSign Glyph.neg) T3
            ⟨Function.update T3.reg rSign V, T3.stk⟩ 1 := by
          rw [hV]; exact Eval.set rSign Glyph.neg T3
        exact Eval.iteF hA' (Eval.iteT (by rw [hT3bit]; exact hB) hset)
      · have hV : V = Glyph.pos := by simp only [V, if_neg hA, if_neg hB]
        have hset : Eval main (.set rSign Glyph.pos) T3
            ⟨Function.update T3.reg rSign V, T3.stk⟩ 1 := by
          rw [hV]; exact Eval.set rSign Glyph.pos T3
        exact Eval.iteF hA' (Eval.iteF (by rw [hT3bit]; exact hB) hset)
  have hT4rSign : T4.reg rSign = V := by dsimp only [T4]; simp
  have hT4_0 : T4.stk 0 = Glyph.iend :: below0 := by
    simp +decide [S6, T4, T3, T2, T1, h6_0, h5_0]
  have hT4W : T4.stk sC =
      ((((acc.reverse ++ rho).reverse).dropWhile (fun b => !b)).map Glyph.bit) ++ [mkC] ++ belowC := by
    simp +decide [S6, T4, T3, T2, T1, h5C]
  have hT4S : T4.stk sS = belowS := by simp +decide [S6, T4, T3, T2, T1]
  have hT4R : T4.stk sR = mkR :: belowR := by simp +decide [S6, T4, T3, T2, T1, h5R]
  have hT4T : T4.stk sT = mkT :: belowT := by simp +decide [S6, T4, T3, T2, T1, h5T]
  have hT4U : T4.stk sU = mkU :: belowU := by simp +decide [S6, T4, T3, T2, T1, h5U]
  have hsgn : Ev main sgnProg S6 T4 6 := by
    have hprog : sgnProg = .seq (.pop sS rBit) (.seq (.pop sS rA) (.seq (.pop sS rTmp)
        (.ite rA Glyph.neg (.ite rBit Glyph.neg (.set rSign Glyph.pos) (.set rSign Glyph.neg))
          (.ite rBit Glyph.neg (.set rSign Glyph.neg) (.set rSign Glyph.pos))))) := by
      simp only [sgnProg, seqs]
    rw [hprog]
    exact Ev.mono (Ev.seq (ev_of_eval f1) (Ev.seq (ev_of_eval f2)
      (Ev.seq (ev_of_eval f3) (ev_of_eval f4)))) (by norm_num)
  -- ## step 8 : the zero test
  let T5 : State := ⟨Function.update T4.reg rTmp ((T4.stk sC).headD Glyph.eos), T4.stk⟩
  have f5 : Ev main (.peek sC rTmp) T4 T5 1 := by
    dsimp only [T5]; exact ev_of_eval (Eval.peek sC rTmp T4)
  have hcondrev : stripHigh (acc.reverse ++ rho) = []
      ↔ ((acc.reverse ++ rho).reverse).dropWhile (fun b => !b) = [] := by
    rw [stripHigh]; exact List.reverse_eq_nil_iff
  have hheadval : T5.reg rTmp = (if stripHigh (acc.reverse ++ rho) = [] then mkC else Glyph.bit true) := by
    have h : T5.reg rTmp = (T5.stk sC).headD Glyph.eos := by
      simp only [T5, Function.update_self]
    rw [h, show T5.stk sC
      = ((((acc.reverse ++ rho).reverse).dropWhile (fun b => !b)).map Glyph.bit) ++ [mkC] ++ belowC
      from by simp only [T5, hT4W], headD_strip]
    by_cases hc : stripHigh (acc.reverse ++ rho) = []
    · rw [if_pos hc, if_pos (hcondrev.mp hc)]
    · rw [if_neg hc, if_neg (fun hh => hc (hcondrev.mpr hh))]
  have hT5_0 : T5.stk 0 = Glyph.iend :: below0 := by simp only [T5, hT4_0]
  have hT5W : T5.stk sC =
      ((((acc.reverse ++ rho).reverse).dropWhile (fun b => !b)).map Glyph.bit) ++ [mkC] ++ belowC := by
    simp only [T5, hT4W]
  have hT5S : T5.stk sS = belowS := by simp only [T5, hT4S]
  have hT5R : T5.stk sR = mkR :: belowR := by simp only [T5, hT4R]
  have hT5T : T5.stk sT = mkT :: belowT := by simp only [T5, hT4T]
  have hT5U : T5.stk sU = mkU :: belowU := by simp only [T5, hT4U]
  -- ## step 9 : override a zero product to `pos`
  let T6 : State := ⟨Function.update T5.reg rSign
    (if stripHigh (acc.reverse ++ rho) = [] then Glyph.pos else V), T5.stk⟩
  have f6 : Ev main (.ite rTmp mkC (.set rSign Glyph.pos) .skip) T5 T6 2 := by
    by_cases hzero : stripHigh (acc.reverse ++ rho) = []
    · have hT6 : T6 = ⟨Function.update T5.reg rSign Glyph.pos, T5.stk⟩ := by
        dsimp only [T6]; rw [if_pos hzero]
      rw [hT6]
      exact Ev.iteT (by rw [hheadval, if_pos hzero]) (ev_of_eval (Eval.set rSign Glyph.pos T5))
    · have hTsgn : T5.reg rSign = V := by
        simp only [T5, Function.update_of_ne (by decide : (rSign : Reg) ≠ rTmp), hT4rSign]
      have hreg : Function.update T5.reg rSign V = T5.reg := by
        funext rr
        by_cases hr : rr = rSign
        · subst hr; rw [Function.update_self, hTsgn]
        · rw [Function.update_of_ne hr]
      have hT6 : T6 = T5 := by
        dsimp only [T6]; rw [if_neg hzero, hreg]
      rw [hT6]
      refine Ev.iteF ?_ (ev_of_eval (Eval.skip T5))
      rw [hheadval, if_neg hzero]
      intro h; cases h
  have hT6rSign : T6.reg rSign = (if stripHigh (acc.reverse ++ rho) = [] then Glyph.pos else V) := by
    simp only [T6, Function.update_self]
  have hT6W : T6.stk sC =
      ((((acc.reverse ++ rho).reverse).dropWhile (fun b => !b)).map Glyph.bit) ++ [mkC] ++ belowC := by
    simp only [T6, hT5W]
  have hT6_0 : T6.stk 0 = Glyph.iend :: below0 := by simp only [T6, hT5_0]
  have hT6S : T6.stk sS = belowS := by simp only [T6, hT5S]
  have hT6R : T6.stk sR = mkR :: belowR := by simp only [T6, hT5R]
  have hT6T : T6.stk sT = mkT :: belowT := by simp only [T6, hT5T]
  have hT6U : T6.stk sU = mkU :: belowU := by simp only [T6, hT5U]
  have hT6stk : T6.stk = T5.stk := by dsimp only [T6]
  -- ## step 10 : sC -> stack 0
  have hWlen : ((((acc.reverse ++ rho).reverse).dropWhile (fun b => !b)).length)
      ≤ acc.length + rho.length := by
    have h1 := List.length_dropWhile_le (fun b => !b) ((acc.reverse ++ rho).reverse)
    rw [List.length_reverse] at h1
    rw [List.length_append, List.length_reverse] at h1
    exact h1
  have hws10 : ∀ g ∈ (((acc.reverse ++ rho).reverse).dropWhile (fun b => !b)).map Glyph.bit,
      g ≠ mkC := by
    intro g hg; obtain ⟨x, -, rfl⟩ := List.mem_map.mp hg; intro h; cases h
  have hT6W' : T6.stk sC =
      ((((acc.reverse ++ rho).reverse).dropWhile (fun b => !b)).map Glyph.bit) ++ mkC :: belowC := by
    simp only [hT6W, List.append_assoc, List.singleton_append]
  obtain ⟨T7, n7, hev7, hn7, h7C, h70, h7fr⟩ :=
    drain_ev' (main := main) (src := sC) (dst := 0) (hne := (by decide : sC ≠ 0))
      (T := mkC) (r := rL) (below := belowC)
      ((((acc.reverse ++ rho).reverse).dropWhile (fun b => !b)).map Glyph.bit)
      (Glyph.iend :: below0) T6 hT6W' hT6_0 hws10
  have e10 : Ev main (consume sC mkC rL (.push 0 rL)) T6 T7
      (5 * (acc.length + rho.length + 1) + 2) := by
    refine Ev.mono (ev_of_eval hev7) ?_
    simp only [List.length_map] at hn7
    omega
  have h70' : T7.stk 0 = (stripHigh (acc.reverse ++ rho)).map Glyph.bit ++ [Glyph.iend] ++ below0 := by
    show T7.stk 0 = ((((acc.reverse ++ rho).reverse).dropWhile (fun b => !b)).reverse).map Glyph.bit
      ++ [Glyph.iend] ++ below0
    rw [h70, List.map_reverse, List.append_assoc, List.singleton_append]
  have h7C' : T7.stk sC = [mkC] ++ belowC := by
    simp only [h7C, List.singleton_append]
  have h7S : T7.stk sS = belowS := by rw [h7fr sS (by decide) (by decide)]; exact hT6S
  have h7R : T7.stk sR = mkR :: belowR := by rw [h7fr sR (by decide) (by decide)]; exact hT6R
  have h7T : T7.stk sT = mkT :: belowT := by rw [h7fr sT (by decide) (by decide)]; exact hT6T
  have h7U : T7.stk sU = mkU :: belowU := by rw [h7fr sU (by decide) (by decide)]; exact hT6U
  have h7rSign : T7.reg rSign = T6.reg rSign :=
    eval_reg_frame hev7 (by decide : rSign ∉ cmdRegs (drain sC 0 mkC rL))
  -- ## step 11 : push the sign
  let T8 : State := ⟨T7.reg, Function.update T7.stk 0 (T7.reg rSign :: T7.stk 0)⟩
  have e11 : Ev main (.push 0 rSign) T7 T8 1 := by
    dsimp only [T8]; exact ev_of_eval (Eval.push 0 rSign T7)
  have hsignEq : T7.reg rSign = (if stripHigh (acc.reverse ++ rho) = [] then Glyph.pos
      else if sa = Glyph.neg then (if sb = Glyph.neg then Glyph.pos else Glyph.neg)
      else (if sb = Glyph.neg then Glyph.neg else Glyph.pos)) := by
    rw [h7rSign, hT6rSign]
  have h8_0 : T8.stk 0 = T7.reg rSign :: T7.stk 0 := by
    dsimp only [T8]; rw [Function.update_self]
  have h80 : T8.stk 0 = (if stripHigh (acc.reverse ++ rho) = [] then Glyph.pos
        else if sa = Glyph.neg then (if sb = Glyph.neg then Glyph.pos else Glyph.neg)
        else (if sb = Glyph.neg then Glyph.neg else Glyph.pos))
      :: (stripHigh (acc.reverse ++ rho)).map Glyph.bit ++ [Glyph.iend] ++ below0 := by
    rw [h8_0, hsignEq, h70']
    simp only [List.cons_append, List.append_assoc]
  have h8R : T8.stk sR = mkR :: belowR := by
    dsimp only [T8]; rw [Function.update_of_ne (by decide : (sR : Stk) ≠ 0)]; exact h7R
  have h8C : T8.stk sC = mkC :: belowC := by
    dsimp only [T8]; rw [Function.update_of_ne (by decide : (sC : Stk) ≠ 0)]; exact h7C'
  have h8S : T8.stk sS = belowS := by
    dsimp only [T8]; rw [Function.update_of_ne (by decide : (sS : Stk) ≠ 0)]; exact h7S
  have h8T : T8.stk sT = mkT :: belowT := by
    dsimp only [T8]; rw [Function.update_of_ne (by decide : (sT : Stk) ≠ 0)]; exact h7T
  have h8U : T8.stk sU = mkU :: belowU := by
    dsimp only [T8]; rw [Function.update_of_ne (by decide : (sU : Stk) ≠ 0)]; exact h7U
  have h8fr : ∀ k, k ≠ 0 → k ≠ sR → k ≠ sC → k ≠ sS → k ≠ sT → k ≠ sU →
      T8.stk k = s.stk k := by
    intro k hk0 hkR hkC hkS hkT hkU
    have a8 : T8.stk k = T7.stk k := by
      dsimp only [T8]; rw [Function.update_of_ne (show k ≠ 0 from hk0)]
    have a7 : T7.stk k = T6.stk k := h7fr k hkC hk0
    have a6 : T6.stk k = T5.stk k := by rw [hT6stk]
    have a5 : T5.stk k = S6.stk k := by
      simp only [T5, T4, T3, T2, T1, Function.update_of_ne (show k ≠ sS from hkS)]
    have a6' : S6.stk k = S5.stk k := by
      dsimp only [S6]; rw [Function.update_of_ne (show k ≠ 0 from hk0)]
    have a5' : S5.stk k = S4.stk k := h5fr k hkC
    have a4' : S4.stk k = S3.stk k := h4fr k hkU hkC
    have a3' : S3.stk k = S2.stk k := h3fr k hkC hkU
    have a2' : S2.stk k = S1.stk k := h2fr k hkT hkU
    have a1' : S1.stk k = s.stk k := h1fr k hkR hkT
    rw [a8, a7, a6, a5, a6', a5', a4', a3', a2', a1']
  -- ## the program and its cost
  have hprog : finalizeProg = (.seq (consume sR mkR rL (.push sT rL)) (.seq (consume sT mkT rL (.push sU rL)) (.seq (consume sC mkC rL (.push sU rL)) (.seq (consume sU mkU rL (.push sC rL)) (.seq stripProg (.seq (.push 0 rIe) (.seq sgnProg (.seq (.peek sC rTmp) (.seq (.ite rTmp mkC (.set rSign Glyph.pos) .skip) (.seq (consume sC mkC rL (.push 0 rL)) (.push 0 rSign))))))))))) := by
    simp only [finalizeProg, seqs]
  have htot : Ev main finalizeProg s T8 (60 * (acc.length + rho.length + 1) + 60) := by
    rw [hprog]
    exact Ev.mono (Ev.seq e1 (Ev.seq e2 (Ev.seq e3 (Ev.seq e4 (Ev.seq e5 (Ev.seq e6
      (Ev.seq hsgn (Ev.seq f5 (Ev.seq f6 (Ev.seq e10 e11)))))))))) (by omega)
  obtain ⟨ntot, hev, hntot⟩ := htot
  exact ⟨T8, ntot, hev, hntot, h80, h8R, h8C, h8S, h8T, h8U, h8fr⟩

end Work.IntLib
