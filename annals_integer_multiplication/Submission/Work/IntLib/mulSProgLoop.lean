import Submission.Work.IntLib.mulSDefs
import Submission.Work.IntLib.mulSEv

/-!
# The serial-multiplier loop `mainLoopProg`

`mainLoopProg = consume sB mkB rL mainBody` with `mainBody = mov rBit rL; addAProg`: for each bit
`β` of the multiplier (which sits on `sB`, least significant bit on top) it transfers the low bit of
`ρ + β·α` to `sC` and halves `ρ`.  The scratch stacks `sA`, `sW`, `sT` are restored, `sB` is emptied
down to its marker, and the result is the paper's `run`.
-/

set_option autoImplicit false
open HvdH

namespace Work.IntLib
open MulS

private theorem bit_ne_mkB (b : Bool) : Glyph.bit b ≠ mkB := by intro h; cases h

/-- The stopping case of the loop: `sB` holds only its marker. -/
private theorem mainLoopNil {main : Cmd} {s : State} {alpha acc rho : List Bool}
    {belowA belowB belowR belowC belowT belowW : List Glyph}
    (hB : s.stk sB = [mkB] ++ belowB)
    (hA : s.stk sA = alpha.map Glyph.bit ++ [mkA] ++ belowA)
    (hR : s.stk sR = rho.map Glyph.bit ++ [mkR] ++ belowR)
    (hC : s.stk sC = acc.map Glyph.bit ++ [mkC] ++ belowC)
    (hW : s.stk sW = [mkW] ++ belowW) (hT : s.stk sT = [mkT] ++ belowT)
    (hrL : s.reg rL = Glyph.eos) :
    ∃ s' n, Eval main (consumeLoop sB mkB rL mainBody) s s' n ∧ n ≤ 6 ∧
      s'.stk sB = [mkB] ++ belowB ∧ s'.stk sA = alpha.map Glyph.bit ++ [mkA] ++ belowA ∧
      s'.stk sR = rho.map Glyph.bit ++ [mkR] ++ belowR ∧
      s'.stk sC = acc.map Glyph.bit ++ [mkC] ++ belowC ∧
      s'.stk sW = [mkW] ++ belowW ∧ s'.stk sT = [mkT] ++ belowT ∧ s'.reg rL = mkStop ∧
      (∀ k, k ≠ sA → k ≠ sB → k ≠ sR → k ≠ sC → k ≠ sW → k ≠ sT → s'.stk k = s.stk k) := by
  have hB' : s.stk sB = mkB :: belowB := by rw [hB, List.singleton_append]
  let S1 : State := ⟨Function.update s.reg rL mkB, Function.update s.stk sB belowB⟩
  have e1 : Eval main (.pop sB rL) s S1 1 := by
    dsimp only [S1]; simpa [hB'] using Eval.pop sB rL s
  let S2 : State := ⟨S1.reg, Function.update S1.stk sB (S1.reg rL :: S1.stk sB)⟩
  have e2 : Eval main (.push sB rL) S1 S2 1 := by dsimp only [S2]; exact Eval.push sB rL S1
  let S3 : State := ⟨Function.update S2.reg rL mkStop, S2.stk⟩
  have e3 : Eval main (.set rL mkStop) S2 S3 1 := by dsimp only [S3]; exact Eval.set rL mkStop S2
  have hite : Eval main (.ite rL mkB (.seq (.push sB rL) (.set rL mkStop))
      (.seq mainBody (.set rL Glyph.eos))) S1 S3 3 := by
    refine Eval.iteT ?_ (Eval.seq e2 e3)
    simp only [S1, Function.update_self]
  have hbody : Eval main (consumeStep sB mkB rL mainBody) s S3 4 := Eval.seq e1 hite
  have hstop : S3.reg rL ≠ Glyph.eos := by simp +decide [S3, S2]
  have hloopF : Eval main (consumeLoop sB mkB rL mainBody) S3 S3 1 :=
    Eval.loopF hstop
  have hloop : Eval main (consumeLoop sB mkB rL mainBody) s S3 6 := Eval.loopT hrL hbody hloopF
  have gB : S3.stk sB = [mkB] ++ belowB := by
    show mkB :: belowB = [mkB] ++ belowB
    rw [List.singleton_append]
  have gA : S3.stk sA = alpha.map Glyph.bit ++ [mkA] ++ belowA := by
    dsimp only [S3, S2, S1]
    rw [Function.update_of_ne (by decide : (sA : Stk) ≠ sB)]
    exact hA
  have gR : S3.stk sR = rho.map Glyph.bit ++ [mkR] ++ belowR := by
    dsimp only [S3, S2, S1]
    rw [Function.update_of_ne (by decide : (sR : Stk) ≠ sB)]
    exact hR
  have gC : S3.stk sC = acc.map Glyph.bit ++ [mkC] ++ belowC := by
    dsimp only [S3, S2, S1]
    rw [Function.update_of_ne (by decide : (sC : Stk) ≠ sB)]
    exact hC
  have gW : S3.stk sW = [mkW] ++ belowW := by
    dsimp only [S3, S2, S1]
    rw [Function.update_of_ne (by decide : (sW : Stk) ≠ sB)]
    exact hW
  have gT : S3.stk sT = [mkT] ++ belowT := by
    dsimp only [S3, S2, S1]
    rw [Function.update_of_ne (by decide : (sT : Stk) ≠ sB)]
    exact hT
  have gL : S3.reg rL = mkStop := by simp +decide [S3, S2]
  have gfr : ∀ k, k ≠ sA → k ≠ sB → k ≠ sR → k ≠ sC → k ≠ sW → k ≠ sT →
      S3.stk k = s.stk k := by
    intro k h1 h2 h3 h4 h5 h6
    dsimp only [S3, S2, S1]
    rw [Function.update_of_ne (show k ≠ sB from h2), Function.update_of_ne (show k ≠ sB from h2)]
  exact ⟨S3, 6, hloop, le_rfl, gB, gA, gR, gC, gW, gT, gL, gfr⟩

theorem mulSProgLoop {main : Cmd} {s : State} {alpha bbits rho0 acc : List Bool}
    {belowA belowB belowR belowC belowT belowW : List Glyph}
    (hB : s.stk sB = bbits.map Glyph.bit ++ [mkB] ++ belowB)
    (hA : s.stk sA = alpha.map Glyph.bit ++ [mkA] ++ belowA)
    (hR : s.stk sR = rho0.map Glyph.bit ++ [mkR] ++ belowR)
    (hC : s.stk sC = acc.map Glyph.bit ++ [mkC] ++ belowC)
    (hW : s.stk sW = [mkW] ++ belowW) (hT : s.stk sT = [mkT] ++ belowT)
    (hlen : rho0.length = alpha.length) :
    ∃ s' n, Eval main mainLoopProg s s' n ∧
      n ≤ 200 * (bbits.length + 1) * (alpha.length + 1) + 200 ∧
      s'.stk sB = [mkB] ++ belowB ∧
      s'.stk sA = alpha.map Glyph.bit ++ [mkA] ++ belowA ∧
      s'.stk sR = (run alpha bbits acc rho0).2.map Glyph.bit ++ [mkR] ++ belowR ∧
      s'.stk sC = (run alpha bbits acc rho0).1.map Glyph.bit ++ [mkC] ++ belowC ∧
      s'.stk sW = [mkW] ++ belowW ∧ s'.stk sT = [mkT] ++ belowT ∧
      (∀ k : Stk, k ≠ sA → k ≠ sB → k ≠ sR → k ≠ sC → k ≠ sW → k ≠ sT →
        s'.stk k = s.stk k) := by
  have haux : ∀ (m : ℕ) (bbits acc rho : List Bool) (s : State), bbits.length ≤ m →
      s.reg rL = Glyph.eos →
      s.stk sB = bbits.map Glyph.bit ++ [mkB] ++ belowB →
      s.stk sA = alpha.map Glyph.bit ++ [mkA] ++ belowA →
      s.stk sR = rho.map Glyph.bit ++ [mkR] ++ belowR →
      s.stk sC = acc.map Glyph.bit ++ [mkC] ++ belowC →
      s.stk sW = [mkW] ++ belowW → s.stk sT = [mkT] ++ belowT →
      rho.length = alpha.length →
      ∃ s' n, Eval main (consumeLoop sB mkB rL mainBody) s s' n ∧
        n ≤ 200 * (bbits.length + 1) * (alpha.length + 1) + 150 ∧
        s'.stk sB = [mkB] ++ belowB ∧
        s'.stk sA = alpha.map Glyph.bit ++ [mkA] ++ belowA ∧
        s'.stk sR = (run alpha bbits acc rho).2.map Glyph.bit ++ [mkR] ++ belowR ∧
        s'.stk sC = (run alpha bbits acc rho).1.map Glyph.bit ++ [mkC] ++ belowC ∧
        s'.stk sW = [mkW] ++ belowW ∧ s'.stk sT = [mkT] ++ belowT ∧
        s'.reg rL = mkStop ∧
        (∀ k : Stk, k ≠ sA → k ≠ sB → k ≠ sR → k ≠ sC → k ≠ sW → k ≠ sT →
          s'.stk k = s.stk k) := by
    intro m
    induction m with
    | zero =>
      intro bbits acc rho s hle hrL hB hA hR hC hW hT hlen
      have hbbits : bbits = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hle)
      subst hbbits
      simp only [List.map_nil, List.nil_append] at hB
      obtain ⟨s', n, hev, hn, gB, gA, gR, gC, gW, gT, gL, gfr⟩ :=
        mainLoopNil (main := main) (alpha := alpha) (acc := acc) (rho := rho)
          hB hA hR hC hW hT hrL
      refine ⟨s', n, hev, ?_, gB, gA, ?_, ?_, gW, gT, gL, gfr⟩
      · simp only [List.length_nil, Nat.zero_add, Nat.mul_one]; omega
      · exact gR
      · exact gC
    | succ m ih =>
      intro bbits acc rho s hle hrL hB hA hR hC hW hT hlen
      cases bbits with
      | nil =>
        simp only [List.map_nil, List.nil_append] at hB
        obtain ⟨s', n, hev, hn, gB, gA, gR, gC, gW, gT, gL, gfr⟩ :=
          mainLoopNil (main := main) (alpha := alpha) (acc := acc) (rho := rho)
            hB hA hR hC hW hT hrL
        refine ⟨s', n, hev, ?_, gB, gA, ?_, ?_, gW, gT, gL, gfr⟩
        · simp only [List.length_nil, Nat.zero_add, Nat.mul_one]; omega
        · exact gR
        · exact gC
      | cons β bbits' =>
        have hB' : s.stk sB = Glyph.bit β :: (bbits'.map Glyph.bit ++ [mkB] ++ belowB) := by
          simp only [hB, List.map_cons, List.cons_append, List.append_assoc]
        let S1 : State := ⟨Function.update s.reg rL (Glyph.bit β),
          Function.update s.stk sB (bbits'.map Glyph.bit ++ [mkB] ++ belowB)⟩
        have e1 : Eval main (.pop sB rL) s S1 1 := by
          dsimp only [S1]; simpa [hB'] using Eval.pop sB rL s
        have hS1rL : S1.reg rL = Glyph.bit β := by simp +decide [S1]
        have hS1B : S1.stk sB = bbits'.map Glyph.bit ++ [mkB] ++ belowB := by simp [S1]
        have hS1A : S1.stk sA = alpha.map Glyph.bit ++ [mkA] ++ belowA := by
          dsimp only [S1]
          rw [Function.update_of_ne (by decide : (sA : Stk) ≠ sB)]; exact hA
        have hS1R : S1.stk sR = rho.map Glyph.bit ++ [mkR] ++ belowR := by
          dsimp only [S1]
          rw [Function.update_of_ne (by decide : (sR : Stk) ≠ sB)]; exact hR
        have hS1C : S1.stk sC = acc.map Glyph.bit ++ [mkC] ++ belowC := by
          dsimp only [S1]
          rw [Function.update_of_ne (by decide : (sC : Stk) ≠ sB)]; exact hC
        have hS1W : S1.stk sW = [mkW] ++ belowW := by
          dsimp only [S1]
          rw [Function.update_of_ne (by decide : (sW : Stk) ≠ sB)]; exact hW
        have hS1T : S1.stk sT = [mkT] ++ belowT := by
          dsimp only [S1]
          rw [Function.update_of_ne (by decide : (sT : Stk) ≠ sB)]; exact hT
        -- `mov rBit rL`
        let S2 : State := ⟨Function.update S1.reg rBit (S1.reg rL), S1.stk⟩
        have e2 : Eval main (.mov rBit rL) S1 S2 1 := by dsimp only [S2]; exact Eval.mov rBit rL S1
        have hS2bit : S2.reg rBit = Glyph.bit β := by simp +decide [S2, S1]
        -- `addAProg`
        obtain ⟨S3, n3, hev3, hn3, g3A, g3R, g3C, g3W, g3T, g3fr⟩ :=
          addA_ev (main := main) (s := S2) (alp := alpha) (rho0 := rho) (acc := acc) (bb := β)
            (belowA := belowA) (belowR := belowR) (belowC := belowC) (belowT := belowT)
            (belowW := belowW) hS1A hS1R hS1W hS1T hS1C hS2bit hlen.symm
        -- `set rL eos`
        let S4 : State := ⟨Function.update S3.reg rL Glyph.eos, S3.stk⟩
        have e4 : Eval main (.set rL Glyph.eos) S3 S4 1 := by
          dsimp only [S4]; exact Eval.set rL Glyph.eos S3
        have hS4rL : S4.reg rL = Glyph.eos := by simp [S4]
        have hne : S1.reg rL ≠ mkB := by rw [hS1rL]; exact bit_ne_mkB β
        have ebody : Ev main mainBody S1 S3 (1 + (40 * (alpha.length + 1) + 60)) := by
          unfold mainBody
          exact Ev.seq' (ev_of_eval e2) (Ev.mono (ev_of_eval hev3) hn3) (by omega)
        have e5 : Ev main (.seq mainBody (.set rL Glyph.eos)) S1 S4
            ((1 + (40 * (alpha.length + 1) + 60)) + 1) := Ev.seq ebody (ev_of_eval e4)
        have hite : Ev main (.ite rL mkB (.seq (.push sB rL) (.set rL mkStop))
            (.seq mainBody (.set rL Glyph.eos))) S1 S4 (((1 + (40 * (alpha.length + 1) + 60)) + 1) + 1) :=
          Ev.iteF hne e5
        have hbody : Ev main (consumeStep sB mkB rL mainBody) s S4
            (1 + (((1 + (40 * (alpha.length + 1) + 60)) + 1) + 1)) :=
          Ev.seq' (ev_of_eval e1) hite (by omega)
        -- the induction hypothesis
        have hlen' : ((stepR alpha rho β).2).length = alpha.length :=
          (stepR_val alpha rho hlen β).2.2
        have hle' : bbits'.length ≤ m := by simp only [List.length_cons] at hle; omega
        have hS4B : S4.stk sB = bbits'.map Glyph.bit ++ [mkB] ++ belowB := by
          dsimp only [S4]
          rw [g3fr sB (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hS1B
        have hS4A : S4.stk sA = alpha.map Glyph.bit ++ [mkA] ++ belowA := by
          dsimp only [S4]; exact g3A
        have hS4R : S4.stk sR = (stepR alpha rho β).2.map Glyph.bit ++ [mkR] ++ belowR := by
          dsimp only [S4]; exact g3R
        have hS4C : S4.stk sC = ((stepR alpha rho β).1 :: acc).map Glyph.bit
            ++ [mkC] ++ belowC := by
          dsimp only [S4]
          rw [show ((stepR alpha rho β).1 :: acc).map Glyph.bit
              = Glyph.bit (stepR alpha rho β).1 :: acc.map Glyph.bit from List.map_cons ..]
          exact g3C
        have hS4W : S4.stk sW = [mkW] ++ belowW := by dsimp only [S4]; exact g3W
        have hS4T : S4.stk sT = [mkT] ++ belowT := by dsimp only [S4]; exact g3T
        obtain ⟨S5, n5, hev5, hn5, g5B, g5A, g5R, g5C, g5W, g5T, g5L, g5fr⟩ :=
          ih bbits' ((stepR alpha rho β).1 :: acc) (stepR alpha rho β).2 S4 hle'
            hS4rL hS4B hS4A hS4R hS4C hS4W hS4T hlen'
        obtain ⟨n, hev, hn⟩ := Ev.loopT hrL hbody (ev_of_eval hev5)
        refine ⟨S5, n, hev, ?_, g5B, g5A, ?_, ?_, g5W, g5T, g5L, ?_⟩
        · -- cost
          have h4 : 200 * ((β :: bbits').length + 1) * (alpha.length + 1)
              = 200 * (bbits'.length + 1 + 1) * (alpha.length + 1) := by
            simp only [List.length_cons]
          rw [h4]
          nlinarith [hn, hn5]
        · exact g5R
        · exact g5C
        · intro k h1 h2 h3 h4 h5 h6
          rw [g5fr k h1 h2 h3 h4 h5 h6,
            g3fr k h1 h3 h4 h5 h6]
          dsimp only [S2, S1]
          rw [Function.update_of_ne (show k ≠ sB from h2)]
  -- mainLoopProg = set rL eos; consumeLoop
  have hset : Ev main (.set rL Glyph.eos) s ⟨Function.update s.reg rL Glyph.eos, s.stk⟩ 1 :=
    ev_set main rL Glyph.eos s
  have h0rL : (⟨Function.update s.reg rL Glyph.eos, s.stk⟩ : State).reg rL = Glyph.eos := by simp
  obtain ⟨s', n', hev', hn', gB, gA, gR, gC, gW, gT, gL, gfr⟩ :=
    haux bbits.length bbits acc rho0 ⟨Function.update s.reg rL Glyph.eos, s.stk⟩ le_rfl h0rL
      hB hA hR hC hW hT hlen
  have hloop : Ev main mainLoopProg s s' (1 + (200 * (bbits.length + 1) * (alpha.length + 1) + 150)) := by
    unfold mainLoopProg consume
    exact Ev.seq' hset (Ev.mono (ev_of_eval hev') hn') (by omega)
  obtain ⟨n, hev, hn⟩ := hloop
  refine ⟨s', n, hev, ?_, gB, gA, gR, gC, gW, gT, gfr⟩
  nlinarith [hn, hn']

end Work.IntLib
