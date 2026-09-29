import Submission.Work.IntLib.mulSDefs
import Submission.Work.IntLib.mulSEv
import Submission.Work.IntLib.mulSArith
import Submission.Work.IntLib.encodeNatBridge

/-!
# Program-level simulation lemmas for the schoolbook multiplication word

Generic helpers used by the top-level assembly of `Work.IntLib.mulSWord`:

* `cmdRegs` / `eval_reg_frame` : a run never writes a register outside `cmdRegs`;
* `openProg_ev` : pushing the eight marker glyphs;
* `discardLoop_ev` / `closeProg_ev` : popping the markers back off;
* `enc_ofBits_product` : the last encoding step (sign + `stripHigh` + `Val.int`).
-/

set_option autoImplicit false
open HvdH

namespace Work.IntLib
open MulS

/-! ## Registers written by a program -/

def cmdRegs : Cmd → Finset Reg
  | .skip => ∅
  | .pop _ r => {r}
  | .peek _ r => {r}
  | .push _ _ => ∅
  | .set r _ => {r}
  | .mov dst _ => {dst}
  | .seq a b => cmdRegs a ∪ cmdRegs b
  | .ite _ _ a b => cmdRegs a ∪ cmdRegs b
  | .loop _ _ a => cmdRegs a
  | .self => Finset.univ

theorem eval_reg_frame {main c : Cmd} {s s' : State} {n : ℕ} (h : Eval main c s s' n)
    {r : Reg} (hr : r ∉ cmdRegs c) : s'.reg r = s.reg r := by
  induction h with
  | skip s => rfl
  | pop k r' s =>
      simp only [cmdRegs, Finset.mem_singleton] at hr
      show Function.update s.reg r' ((s.stk k).headD .eos) r = s.reg r
      exact Function.update_of_ne hr _ _
  | peek k r' s =>
      simp only [cmdRegs, Finset.mem_singleton] at hr
      show Function.update s.reg r' ((s.stk k).headD .eos) r = s.reg r
      exact Function.update_of_ne hr _ _
  | push k r' s => rfl
  | set r' c s =>
      simp only [cmdRegs, Finset.mem_singleton] at hr
      show Function.update s.reg r' c r = s.reg r
      exact Function.update_of_ne hr _ _
  | mov dst src s =>
      simp only [cmdRegs, Finset.mem_singleton] at hr
      show Function.update s.reg dst (s.reg src) r = s.reg r
      exact Function.update_of_ne hr _ _
  | seq h1 h2 ih1 ih2 =>
      simp only [cmdRegs, Finset.mem_union, not_or] at hr
      rw [ih2 hr.2, ih1 hr.1]
  | iteT hr' h ih =>
      simp only [cmdRegs, Finset.mem_union, not_or] at hr
      exact ih hr.1
  | iteF hr' h ih =>
      simp only [cmdRegs, Finset.mem_union, not_or] at hr
      exact ih hr.2
  | loopF hr' => rfl
  | loopT hr' h1 h2 ih1 ih2 =>
      simp only [cmdRegs] at hr
      rw [ih2 hr, ih1 hr]
  | self h ih => exact absurd (Finset.mem_univ r) hr

/-! ## `openProg` -/

theorem openProg_ev (main : Cmd) (s : State) :
    ∃ s' n, Eval main openProg s s' n ∧ n ≤ 20 ∧
      s'.stk 0 = s.stk 0 ∧
      s'.stk sA = [mkA] ++ s.stk sA ∧
      s'.stk sB = [mkB] ++ s.stk sB ∧
      s'.stk sR = [mkR] ++ s.stk sR ∧
      s'.stk sC = [mkC] ++ s.stk sC ∧
      s'.stk sS = [mkS] ++ s.stk sS ∧
      s'.stk sT = [mkT] ++ s.stk sT ∧
      s'.stk sW = [mkW] ++ s.stk sW ∧
      s'.stk sU = [mkU] ++ s.stk sU ∧
      s'.reg rZ = .bit false ∧ s'.reg rIe = .iend ∧
      (∀ k, k ≠ sA → k ≠ sB → k ≠ sR → k ≠ sC → k ≠ sS → k ≠ sT → k ≠ sW → k ≠ sU →
        s'.stk k = s.stk k) := by
  let S1 : State := ⟨Function.update s.reg rTmp mkA, s.stk⟩
  have d1 : Eval main (.set rTmp mkA) s S1 1 := by dsimp only [S1]; exact Eval.set rTmp mkA s
  let S2 : State := ⟨S1.reg, Function.update S1.stk sA (S1.reg rTmp :: S1.stk sA)⟩
  have d2 : Eval main (.push sA rTmp) S1 S2 1 := by dsimp only [S2]; exact Eval.push sA rTmp S1
  let S3 : State := ⟨Function.update S2.reg rTmp mkB, S2.stk⟩
  have d3 : Eval main (.set rTmp mkB) S2 S3 1 := by dsimp only [S3]; exact Eval.set rTmp mkB S2
  let S4 : State := ⟨S3.reg, Function.update S3.stk sB (S3.reg rTmp :: S3.stk sB)⟩
  have d4 : Eval main (.push sB rTmp) S3 S4 1 := by dsimp only [S4]; exact Eval.push sB rTmp S3
  let S5 : State := ⟨Function.update S4.reg rTmp mkR, S4.stk⟩
  have d5 : Eval main (.set rTmp mkR) S4 S5 1 := by dsimp only [S5]; exact Eval.set rTmp mkR S4
  let S6 : State := ⟨S5.reg, Function.update S5.stk sR (S5.reg rTmp :: S5.stk sR)⟩
  have d6 : Eval main (.push sR rTmp) S5 S6 1 := by dsimp only [S6]; exact Eval.push sR rTmp S5
  let S7 : State := ⟨Function.update S6.reg rTmp mkC, S6.stk⟩
  have d7 : Eval main (.set rTmp mkC) S6 S7 1 := by dsimp only [S7]; exact Eval.set rTmp mkC S6
  let S8 : State := ⟨S7.reg, Function.update S7.stk sC (S7.reg rTmp :: S7.stk sC)⟩
  have d8 : Eval main (.push sC rTmp) S7 S8 1 := by dsimp only [S8]; exact Eval.push sC rTmp S7
  let S9 : State := ⟨Function.update S8.reg rTmp mkS, S8.stk⟩
  have d9 : Eval main (.set rTmp mkS) S8 S9 1 := by dsimp only [S9]; exact Eval.set rTmp mkS S8
  let S10 : State := ⟨S9.reg, Function.update S9.stk sS (S9.reg rTmp :: S9.stk sS)⟩
  have d10 : Eval main (.push sS rTmp) S9 S10 1 := by dsimp only [S10]; exact Eval.push sS rTmp S9
  let S11 : State := ⟨Function.update S10.reg rTmp mkT, S10.stk⟩
  have d11 : Eval main (.set rTmp mkT) S10 S11 1 := by dsimp only [S11]; exact Eval.set rTmp mkT S10
  let S12 : State := ⟨S11.reg, Function.update S11.stk sT (S11.reg rTmp :: S11.stk sT)⟩
  have d12 : Eval main (.push sT rTmp) S11 S12 1 := by dsimp only [S12]; exact Eval.push sT rTmp S11
  let S13 : State := ⟨Function.update S12.reg rTmp mkW, S12.stk⟩
  have d13 : Eval main (.set rTmp mkW) S12 S13 1 := by dsimp only [S13]; exact Eval.set rTmp mkW S12
  let S14 : State := ⟨S13.reg, Function.update S13.stk sW (S13.reg rTmp :: S13.stk sW)⟩
  have d14 : Eval main (.push sW rTmp) S13 S14 1 := by dsimp only [S14]; exact Eval.push sW rTmp S13
  let S15 : State := ⟨Function.update S14.reg rTmp mkU, S14.stk⟩
  have d15 : Eval main (.set rTmp mkU) S14 S15 1 := by dsimp only [S15]; exact Eval.set rTmp mkU S14
  let S16 : State := ⟨S15.reg, Function.update S15.stk sU (S15.reg rTmp :: S15.stk sU)⟩
  have d16 : Eval main (.push sU rTmp) S15 S16 1 := by dsimp only [S16]; exact Eval.push sU rTmp S15
  let S17 : State := ⟨Function.update S16.reg rZ (.bit false), S16.stk⟩
  have d17 : Eval main (.set rZ (.bit false)) S16 S17 1 := by dsimp only [S17]; exact Eval.set rZ (.bit false) S16
  let S18 : State := ⟨Function.update S17.reg rIe .iend, S17.stk⟩
  have d18 : Eval main (.set rIe .iend) S17 S18 1 := by dsimp only [S18]; exact Eval.set rIe .iend S17
  have hprog : openProg = (.seq (.set rTmp mkA) (.seq (.push sA rTmp) (.seq (.set rTmp mkB) (.seq (.push sB rTmp) (.seq (.set rTmp mkR) (.seq (.push sR rTmp) (.seq (.set rTmp mkC) (.seq (.push sC rTmp) (.seq (.set rTmp mkS) (.seq (.push sS rTmp) (.seq (.set rTmp mkT) (.seq (.push sT rTmp) (.seq (.set rTmp mkW) (.seq (.push sW rTmp) (.seq (.set rTmp mkU) (.seq (.push sU rTmp) (.seq (.set rZ (.bit false)) (.set rIe .iend)))))))))))))))))) := by simp only [openProg, seqs]
  have hchain : Eval main openProg s S18 18 := by
    rw [hprog]
    exact Eval.seq d1 (Eval.seq d2 (Eval.seq d3 (Eval.seq d4 (Eval.seq d5 (Eval.seq d6 (Eval.seq d7 (Eval.seq d8 (Eval.seq d9 (Eval.seq d10 (Eval.seq d11 (Eval.seq d12 (Eval.seq d13 (Eval.seq d14 (Eval.seq d15 (Eval.seq d16 (Eval.seq d17 (d18)))))))))))))))))
  have c0 : S18.stk 0 = s.stk 0 := by simp +decide [S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18]
  have cA : S18.stk sA = [mkA] ++ s.stk sA := by simp +decide [S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18]
  have cB : S18.stk sB = [mkB] ++ s.stk sB := by simp +decide [S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18]
  have cR : S18.stk sR = [mkR] ++ s.stk sR := by simp +decide [S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18]
  have cC : S18.stk sC = [mkC] ++ s.stk sC := by simp +decide [S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18]
  have cS : S18.stk sS = [mkS] ++ s.stk sS := by simp +decide [S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18]
  have cT : S18.stk sT = [mkT] ++ s.stk sT := by simp +decide [S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18]
  have cW : S18.stk sW = [mkW] ++ s.stk sW := by simp +decide [S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18]
  have cU : S18.stk sU = [mkU] ++ s.stk sU := by simp +decide [S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18]
  have cz : S18.reg rZ = .bit false := by simp +decide [S18, S17]
  have cie : S18.reg rIe = .iend := by simp +decide [S18, S17]
  have cfr : ∀ k, k ≠ sA → k ≠ sB → k ≠ sR → k ≠ sC → k ≠ sS → k ≠ sT → k ≠ sW → k ≠ sU → S18.stk k = s.stk k := by
    intro k h1 h2 h3 h4 h5 h6 h7 h8
    simp +decide [S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
      Function.update_of_ne h6, Function.update_of_ne h7, Function.update_of_ne h8]
  exact ⟨S18, 18, hchain, by norm_num, c0, cA, cB, cR, cC, cS, cT, cW, cU, cz, cie, cfr⟩

/-! ## Discarding the content above a marker -/

theorem discardLoop_ev {main : Cmd} {T : Glyph} {r : Reg} {below : List Glyph}
    (ws : List Glyph) (s : State) (hsrc : s.stk sA = ws ++ T :: below)
    (hws : ∀ g ∈ ws, g ≠ T) (hr : s.reg r = Glyph.eos) :
    ∃ s' n, Eval main (consumeLoop sA T r .skip) s s' n ∧ n ≤ 5 * (ws.length + 1) + 1 ∧
      s'.stk sA = T :: below ∧ (∀ k, k ≠ sA → s'.stk k = s.stk k) ∧ s'.reg r = mkStop := by
  induction ws generalizing s with
  | nil =>
    simp only [List.nil_append] at hsrc
    have hpop : Eval main (.pop sA r) s
        ⟨Function.update s.reg r T, Function.update s.stk sA below⟩ 1 := by
      simpa [hsrc] using Eval.pop sA r s
    have hpush : Ev main (.push sA r)
        ⟨Function.update s.reg r T, Function.update s.stk sA below⟩
        ⟨Function.update s.reg r T,
          Function.update (Function.update s.stk sA below) sA (T :: below)⟩ 1 := by
      have h := ev_push main sA r (⟨Function.update s.reg r T, Function.update s.stk sA below⟩ : State)
      simpa [Function.update_self] using h
    have hset : Ev main (.set r mkStop)
        ⟨Function.update s.reg r T, Function.update (Function.update s.stk sA below) sA (T :: below)⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk sA below) sA (T :: below)⟩ 1 :=
      ev_set main r mkStop _
    have hite : Ev main (.ite r T (.seq (.push sA r) (.set r mkStop)) (.seq .skip (.set r .eos)))
        ⟨Function.update s.reg r T, Function.update s.stk sA below⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk sA below) sA (T :: below)⟩ 3 := by
      refine Ev.iteT ?_ ?_
      · simp
      · exact Ev.seq' hpush hset (by norm_num)
    have hbody : Ev main (consumeStep sA T r .skip) s
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk sA below) sA (T :: below)⟩ 4 :=
      Ev.seq' (ev_of_eval hpop) hite (by norm_num)
    have hloopF : Ev main (consumeLoop sA T r .skip)
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk sA below) sA (T :: below)⟩
        ⟨Function.update (Function.update s.reg r T) r mkStop,
          Function.update (Function.update s.stk sA below) sA (T :: below)⟩ 1 :=
      Ev.loopF (by simp)
    obtain ⟨n, hev, hn⟩ := Ev.loopT hr hbody hloopF
    exact ⟨⟨Function.update (Function.update s.reg r T) r mkStop,
        Function.update (Function.update s.stk sA below) sA (T :: below)⟩,
      n, hev, by omega, by simp [Function.update_self],
      by intro k hk; simp [Function.update_of_ne hk], by simp⟩
  | cons g gs ih =>
    simp only [List.cons_append] at hsrc
    have hg : g ≠ T := hws g (by simp)
    have hws' : ∀ x ∈ gs, x ≠ T := fun x hx => hws x (by simp [hx])
    have hpop : Eval main (.pop sA r) s
        ⟨Function.update s.reg r g, Function.update s.stk sA (gs ++ T :: below)⟩ 1 := by
      simpa [hsrc] using Eval.pop sA r s
    have hskip : Ev main .skip ⟨Function.update s.reg r g, Function.update s.stk sA (gs ++ T :: below)⟩
        ⟨Function.update s.reg r g, Function.update s.stk sA (gs ++ T :: below)⟩ 1 :=
      ev_skip main _
    have hset : Ev main (.set r .eos)
        ⟨Function.update s.reg r g, Function.update s.stk sA (gs ++ T :: below)⟩
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update s.stk sA (gs ++ T :: below)⟩ 1 :=
      ev_set main r .eos _
    have hite : Ev main (.ite r T (.seq (.push sA r) (.set r mkStop)) (.seq .skip (.set r .eos)))
        ⟨Function.update s.reg r g, Function.update s.stk sA (gs ++ T :: below)⟩
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update s.stk sA (gs ++ T :: below)⟩ 3 := by
      refine Ev.iteF ?_ ?_
      · show Function.update s.reg r g r ≠ T
        rw [Function.update_self]; exact hg
      · exact Ev.seq' hskip hset (by norm_num)
    have hbody : Ev main (consumeStep sA T r .skip) s
        ⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update s.stk sA (gs ++ T :: below)⟩ 4 :=
      Ev.seq' (ev_of_eval hpop) hite (by norm_num)
    obtain ⟨s', n', hev', hn', hsrc', hfr', hr'⟩ :=
      ih (⟨Function.update (Function.update s.reg r g) r .eos,
          Function.update s.stk sA (gs ++ T :: below)⟩ : State)
        (by simp [Function.update_self]) hws' (by simp)
    obtain ⟨n, hev, hn⟩ := Ev.loopT hr hbody (ev_of_eval hev')
    refine ⟨s', n, hev, ?_, hsrc', ?_, hr'⟩
    · simp only [List.length_cons]; omega
    · intro k hk
      rw [hfr' k hk]
      simp [Function.update_of_ne hk]

/-! ## `closeProg` -/

theorem closeProg_ev (main : Cmd) (s : State) (WS : List Glyph)
    (belowA belowB belowR belowC belowT belowW belowU : List Glyph)
    (hws : ∀ g ∈ WS, g ≠ mkA)
    (hA : s.stk sA = WS ++ mkA :: belowA)
    (hB : s.stk sB = mkB :: belowB) (hR : s.stk sR = mkR :: belowR)
    (hC : s.stk sC = mkC :: belowC) (hT : s.stk sT = mkT :: belowT)
    (hW : s.stk sW = mkW :: belowW) (hU : s.stk sU = mkU :: belowU) :
    ∃ s' n, Eval main closeProg s s' n ∧ n ≤ 6 * (WS.length + 1) + 20 ∧
      s'.stk 0 = s.stk 0 ∧ s'.stk sA = belowA ∧ s'.stk sB = belowB ∧ s'.stk sR = belowR ∧
      s'.stk sC = belowC ∧ s'.stk sT = belowT ∧ s'.stk sW = belowW ∧ s'.stk sU = belowU ∧
      (∀ k, k ≠ sA → k ≠ sB → k ≠ sR → k ≠ sC → k ≠ sT → k ≠ sW → k ≠ sU →
        s'.stk k = s.stk k) := by
  let S0 : State := ⟨Function.update s.reg rL Glyph.eos, s.stk⟩
  have e0 : Eval main (.set rL Glyph.eos) s S0 1 := by dsimp only [S0]; exact Eval.set rL Glyph.eos s
  have hS0A : S0.stk sA = WS ++ mkA :: belowA := hA
  have hS0eos : S0.reg rL = Glyph.eos := by simp [S0]
  obtain ⟨S1, n1, hev1, hn1, hS1A, hS1fr, -⟩ :=
    discardLoop_ev (main := main) (T := mkA) (r := rL) (below := belowA) WS S0 hS0A hws hS0eos
  have hS1_sB : S1.stk sB = mkB :: belowB := by rw [hS1fr sB (by decide)]; exact hB
  have hS1_sR : S1.stk sR = mkR :: belowR := by rw [hS1fr sR (by decide)]; exact hR
  have hS1_sC : S1.stk sC = mkC :: belowC := by rw [hS1fr sC (by decide)]; exact hC
  have hS1_sT : S1.stk sT = mkT :: belowT := by rw [hS1fr sT (by decide)]; exact hT
  have hS1_sW : S1.stk sW = mkW :: belowW := by rw [hS1fr sW (by decide)]; exact hW
  have hS1_sU : S1.stk sU = mkU :: belowU := by rw [hS1fr sU (by decide)]; exact hU
  let T1 : State := ⟨Function.update S1.reg rTmp mkA, Function.update S1.stk sA belowA⟩
  have f1 : Eval main (.pop sA rTmp) S1 T1 1 := by
    dsimp only [T1]; simpa [hS1A] using Eval.pop sA rTmp S1
  have gp1 : T1.stk sA = belowA := by dsimp only [T1]; simp
  have fr1 : ∀ k, k ≠ sA → T1.stk k = S1.stk k := by
    intro k hk; dsimp only [T1]; rw [Function.update_of_ne hk]
  let T2 : State := ⟨Function.update T1.reg rTmp mkB, Function.update T1.stk sB belowB⟩
  have gpre2 : T1.stk sB = mkB :: belowB := by
    rw [fr1 sB (by decide), hS1_sB]
  have f2 : Eval main (.pop sB rTmp) T1 T2 1 := by
    dsimp only [T2]; simpa [gpre2] using Eval.pop sB rTmp T1
  have gp2 : T2.stk sB = belowB := by dsimp only [T2]; simp
  have fr2 : ∀ k, k ≠ sB → T2.stk k = T1.stk k := by
    intro k hk; dsimp only [T2]; rw [Function.update_of_ne hk]
  let T3 : State := ⟨Function.update T2.reg rTmp mkR, Function.update T2.stk sR belowR⟩
  have gpre3 : T2.stk sR = mkR :: belowR := by
    rw [fr2 sR (by decide), fr1 sR (by decide), hS1_sR]
  have f3 : Eval main (.pop sR rTmp) T2 T3 1 := by
    dsimp only [T3]; simpa [gpre3] using Eval.pop sR rTmp T2
  have gp3 : T3.stk sR = belowR := by dsimp only [T3]; simp
  have fr3 : ∀ k, k ≠ sR → T3.stk k = T2.stk k := by
    intro k hk; dsimp only [T3]; rw [Function.update_of_ne hk]
  let T4 : State := ⟨Function.update T3.reg rTmp mkC, Function.update T3.stk sC belowC⟩
  have gpre4 : T3.stk sC = mkC :: belowC := by
    rw [fr3 sC (by decide), fr2 sC (by decide), fr1 sC (by decide), hS1_sC]
  have f4 : Eval main (.pop sC rTmp) T3 T4 1 := by
    dsimp only [T4]; simpa [gpre4] using Eval.pop sC rTmp T3
  have gp4 : T4.stk sC = belowC := by dsimp only [T4]; simp
  have fr4 : ∀ k, k ≠ sC → T4.stk k = T3.stk k := by
    intro k hk; dsimp only [T4]; rw [Function.update_of_ne hk]
  let T5 : State := ⟨Function.update T4.reg rTmp mkT, Function.update T4.stk sT belowT⟩
  have gpre5 : T4.stk sT = mkT :: belowT := by
    rw [fr4 sT (by decide), fr3 sT (by decide), fr2 sT (by decide), fr1 sT (by decide), hS1_sT]
  have f5 : Eval main (.pop sT rTmp) T4 T5 1 := by
    dsimp only [T5]; simpa [gpre5] using Eval.pop sT rTmp T4
  have gp5 : T5.stk sT = belowT := by dsimp only [T5]; simp
  have fr5 : ∀ k, k ≠ sT → T5.stk k = T4.stk k := by
    intro k hk; dsimp only [T5]; rw [Function.update_of_ne hk]
  let T6 : State := ⟨Function.update T5.reg rTmp mkW, Function.update T5.stk sW belowW⟩
  have gpre6 : T5.stk sW = mkW :: belowW := by
    rw [fr5 sW (by decide), fr4 sW (by decide), fr3 sW (by decide), fr2 sW (by decide), fr1 sW (by decide), hS1_sW]
  have f6 : Eval main (.pop sW rTmp) T5 T6 1 := by
    dsimp only [T6]; simpa [gpre6] using Eval.pop sW rTmp T5
  have gp6 : T6.stk sW = belowW := by dsimp only [T6]; simp
  have fr6 : ∀ k, k ≠ sW → T6.stk k = T5.stk k := by
    intro k hk; dsimp only [T6]; rw [Function.update_of_ne hk]
  let T7 : State := ⟨Function.update T6.reg rTmp mkU, Function.update T6.stk sU belowU⟩
  have gpre7 : T6.stk sU = mkU :: belowU := by
    rw [fr6 sU (by decide), fr5 sU (by decide), fr4 sU (by decide), fr3 sU (by decide), fr2 sU (by decide), fr1 sU (by decide), hS1_sU]
  have f7 : Eval main (.pop sU rTmp) T6 T7 1 := by
    dsimp only [T7]; simpa [gpre7] using Eval.pop sU rTmp T6
  have gp7 : T7.stk sU = belowU := by dsimp only [T7]; simp
  have fr7 : ∀ k, k ≠ sU → T7.stk k = T6.stk k := by
    intro k hk; dsimp only [T7]; rw [Function.update_of_ne hk]
  have hprog : closeProg = .seq (.seq (.set rL Glyph.eos) (consumeLoop sA mkA rL .skip)) (.seq (.pop sA rTmp) (.seq (.pop sB rTmp) (.seq (.pop sR rTmp) (.seq (.pop sC rTmp) (.seq (.pop sT rTmp) (.seq (.pop sW rTmp) (.pop sU rTmp))))))) := by simp only [closeProg, seqs, consume]
  have hchain : Eval main closeProg s T7 ((1 + n1) + (1 + 1 + 1 + 1 + 1 + 1 + 1)) := by
    rw [hprog]
    have c7 : Eval main (.pop sU rTmp) T6 T7 1 := f7
    have c6 : Eval main (.seq (.pop sW rTmp) (.pop sU rTmp)) T5 T7 2 := Eval.seq f6 c7
    have c5 : Eval main (.seq (.pop sT rTmp) (.seq (.pop sW rTmp) (.pop sU rTmp))) T4 T7 3 := Eval.seq f5 c6
    have c4 : Eval main (.seq (.pop sC rTmp) (.seq (.pop sT rTmp) (.seq (.pop sW rTmp) (.pop sU rTmp)))) T3 T7 4 := Eval.seq f4 c5
    have c3 : Eval main (.seq (.pop sR rTmp) (.seq (.pop sC rTmp) (.seq (.pop sT rTmp) (.seq (.pop sW rTmp) (.pop sU rTmp))))) T2 T7 5 := Eval.seq f3 c4
    have c2 : Eval main (.seq (.pop sB rTmp) (.seq (.pop sR rTmp) (.seq (.pop sC rTmp) (.seq (.pop sT rTmp) (.seq (.pop sW rTmp) (.pop sU rTmp)))))) T1 T7 6 := Eval.seq f2 c3
    have c1 : Eval main (.seq (.pop sA rTmp) (.seq (.pop sB rTmp) (.seq (.pop sR rTmp) (.seq (.pop sC rTmp) (.seq (.pop sT rTmp) (.seq (.pop sW rTmp) (.pop sU rTmp))))))) S1 T7 7 := Eval.seq f1 c2
    exact Eval.seq (Eval.seq e0 hev1) c1
  have c0 : T7.stk 0 = s.stk 0 := by
    rw [fr7 0 (by decide), fr6 0 (by decide), fr5 0 (by decide), fr4 0 (by decide),
      fr3 0 (by decide), fr2 0 (by decide), fr1 0 (by decide), hS1fr 0 (by decide)]
  have esA : T7.stk sA = belowA := by rw [fr7 sA (by decide), fr6 sA (by decide), fr5 sA (by decide), fr4 sA (by decide), fr3 sA (by decide), fr2 sA (by decide), gp1]
  have esB : T7.stk sB = belowB := by rw [fr7 sB (by decide), fr6 sB (by decide), fr5 sB (by decide), fr4 sB (by decide), fr3 sB (by decide), gp2]
  have esR : T7.stk sR = belowR := by rw [fr7 sR (by decide), fr6 sR (by decide), fr5 sR (by decide), fr4 sR (by decide), gp3]
  have esC : T7.stk sC = belowC := by rw [fr7 sC (by decide), fr6 sC (by decide), fr5 sC (by decide), gp4]
  have esT : T7.stk sT = belowT := by rw [fr7 sT (by decide), fr6 sT (by decide), gp5]
  have esW : T7.stk sW = belowW := by rw [fr7 sW (by decide), gp6]
  have esU : T7.stk sU = belowU := by rw [gp7]
  have cfr : ∀ k, k ≠ sA → k ≠ sB → k ≠ sR → k ≠ sC → k ≠ sT → k ≠ sW → k ≠ sU →
      T7.stk k = s.stk k := by
    intro k hA' hB' hR' hC' hT' hW' hU'
    rw [fr7 k hU', fr6 k hW', fr5 k hT', fr4 k hC', fr3 k hR', fr2 k hB', fr1 k hA', hS1fr k hA']
  have hcost : (1 + n1) + (1 + 1 + 1 + 1 + 1 + 1 + 1) ≤ 6 * (WS.length + 1) + 20 := by omega
  exact ⟨T7, (1 + n1) + (1 + 1 + 1 + 1 + 1 + 1 + 1), hchain, hcost, c0, esA, esB, esR, esC, esT, esW, esU, cfr⟩

/-! ## The final encoding step -/

theorem enc_ofBits_product {a b : ℤ} {F : List Bool}
    (hF : ofBits F = a.natAbs * b.natAbs) (L : List Glyph) :
    (if stripHigh F = [] then Glyph.pos
      else if (if a < 0 then Glyph.neg else Glyph.pos) = Glyph.neg
        then (if (if b < 0 then Glyph.neg else Glyph.pos) = Glyph.neg then Glyph.pos else Glyph.neg)
        else (if (if b < 0 then Glyph.neg else Glyph.pos) = Glyph.neg then Glyph.neg else Glyph.pos))
      :: (stripHigh F).map Glyph.bit ++ [Glyph.iend] ++ L
    = (Val.int (a * b)).enc ++ L := by
  have hbits : (stripHigh F).map Glyph.bit
      = (Computability.encodeNat (a * b).natAbs).map Glyph.bit := by
    rw [stripHigh_eq_bits, hF, ← Int.natAbs_mul, ← encodeNat_eq_bits]
  have hz : stripHigh F = [] ↔ a * b = 0 := by
    rw [stripHigh_eq_nil_iff, hF, Nat.mul_eq_zero, Int.natAbs_eq_zero, Int.natAbs_eq_zero,
      ← Int.mul_eq_zero]
  have hsign : (if stripHigh F = [] then Glyph.pos
      else if (if a < 0 then Glyph.neg else Glyph.pos) = Glyph.neg
        then (if (if b < 0 then Glyph.neg else Glyph.pos) = Glyph.neg then Glyph.pos else Glyph.neg)
        else (if (if b < 0 then Glyph.neg else Glyph.pos) = Glyph.neg then Glyph.neg else Glyph.pos))
      = (if a * b < 0 then Glyph.neg else Glyph.pos) := by
    have hsa : ((if a < 0 then Glyph.neg else Glyph.pos) = Glyph.neg) ↔ a < 0 := by
      by_cases h : a < 0 <;> simp [h]
    have hsb : ((if b < 0 then Glyph.neg else Glyph.pos) = Glyph.neg) ↔ b < 0 := by
      by_cases h : b < 0 <;> simp [h]
    by_cases h0 : a * b = 0
    · have hne : stripHigh F = [] := hz.mpr h0
      have hlt : ¬ (a * b < 0) := by rw [h0]; norm_num
      rw [if_pos hne, if_neg hlt]
    · have hne : stripHigh F ≠ [] := fun hc => h0 (hz.mp hc)
      rw [if_neg hne]
      by_cases hlt : a * b < 0
      · rcases Int.mul_neg_iff.mp hlt with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
        · rw [if_neg (by rw [hsa]; omega), if_pos (hsb.mpr (by omega)), if_pos hlt]
        · rw [if_pos (hsa.mpr (by omega)), if_neg (by rw [hsb]; omega), if_pos hlt]
      · have hpos : 0 < a * b := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm h0)
        rcases Int.mul_pos_iff.mp hpos with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
        · rw [if_neg (by rw [hsa]; omega), if_neg (by rw [hsb]; omega), if_neg hlt]
        · rw [if_pos (hsa.mpr (by omega)), if_pos (hsb.mpr (by omega)), if_neg hlt]
  rw [hsign, hbits, enc_int, List.cons_append]


end Work.IntLib
