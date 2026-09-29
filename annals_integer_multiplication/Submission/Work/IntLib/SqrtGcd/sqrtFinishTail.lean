import Mathlib
import Submission.Work.IntLib.SqrtGcd.SqrtProg
import Submission.Work.IntLib.eval_stripZeros
import Submission.Work.IntLib.dropWhile_rev_padBits_bits

/-!
# The tail of the square-root program that emits the root

`Work.IntLib.SG.sqrtFinish` emits the root (region of stack `sP`, delimited by its marker) as an
integer value on stack 0.  The step before that (`rLoop sC …` moving `sC` to `sP`) supplies the
region: at the point of interest, stack `sP` carries the **canonical** bits of `ofBits rl`
(least significant bit first, i.e. the reverse of `rl.map Glyph.bit`) above its marker, and
nothing else is known about the state.

This file proves the corresponding `Eval` statement directly, for an arbitrary `main`: running
`stripZeros sP`, pushing `iend`, moving the region onto stack 0 and pushing the sign `pos` turns
the region into exactly `(Val.int (ofBits rl)).enc` on top of stack 0, in at most
`12 * rl.length + 30` steps, leaving stack `sP` and every stack other than `0` and `sP` untouched.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH

theorem sqrtFinishTail (main : HvdH.Cmd) (rl : List Bool) (R : List HvdH.Glyph)
    (bP : List HvdH.Glyph) (s : HvdH.State)
    (h0 : s.stk 0 = R)
    (hP : s.stk Work.IntLib.SG.sP
      = (rl.map HvdH.Glyph.bit).reverse ++ HvdH.Glyph.mk Work.IntLib.SG.sP :: bP) :
    ∃ s' m, HvdH.Eval main (Work.Layout.seqs [
        Work.IntLib.SG.stripZeros Work.IntLib.SG.sP Work.IntLib.SG.rgT,
        HvdH.Cmd.set Work.IntLib.SG.rgU HvdH.Glyph.iend,
        HvdH.Cmd.push 0 Work.IntLib.SG.rgU,
        Work.IntLib.SG.rLoop Work.IntLib.SG.sP (HvdH.Glyph.mk Work.IntLib.SG.sP) (some 0)
          Work.IntLib.SG.rgT,
        HvdH.Cmd.set Work.IntLib.SG.rgU HvdH.Glyph.pos,
        HvdH.Cmd.push 0 Work.IntLib.SG.rgU]) s s' m ∧
      m ≤ 12 * rl.length + 30 ∧
      s'.stk 0 = (HvdH.Val.int ((Work.IntLib.ofBits rl : ℕ) : ℤ)).enc ++ R ∧
      s'.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP ∧
      (∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.SG.sP → s'.stk j = s.stk j) := by
  have hTe : (HvdH.Glyph.mk Work.IntLib.SG.sP : HvdH.Glyph) ≠ HvdH.Glyph.eos := by decide
  have hbT : ∀ b : Bool, HvdH.Glyph.bit b ≠ (HvdH.Glyph.mk Work.IntLib.SG.sP : HvdH.Glyph) := by
    intro b h; cases h
  have hPne0 : Work.IntLib.SG.sP ≠ (0 : HvdH.Stk) := by decide
  have h0neP : (0 : HvdH.Stk) ≠ Work.IntLib.SG.sP := by decide
  -- stack `sP` carries the bits of `ofBits rl` (least significant first)
  have hstkP : s.stk Work.IntLib.SG.sP
      = Work.IntLib.bitsG rl.reverse ++ HvdH.Glyph.mk Work.IntLib.SG.sP :: bP := by
    rw [hP]
    simp only [Work.IntLib.bitsG, List.map_reverse]
  -- the canonical form of the region: `stripHigh` of the bit list, read as glyphs, reversed
  set gs : List HvdH.Glyph := ((Work.IntLib.MulS.stripHigh rl).map HvdH.Glyph.bit).reverse with hgs_def
  have hgs_eq : List.dropWhile (fun g => decide (g = HvdH.Glyph.bit false))
      (Work.IntLib.bitsG rl.reverse) = gs := by
    rw [hgs_def]
    simp only [Work.IntLib.bitsG]
    exact Work.IntLib.dropWhile_map_bit_rev_eq rl
  obtain ⟨s1, n1, he1, hle1, hs1P, hs1fr⟩ :=
    Work.IntLib.eval_stripZeros main Work.IntLib.SG.sP (HvdH.Glyph.mk Work.IntLib.SG.sP)
      Work.IntLib.SG.rgT rl.reverse bP s hTe hbT hstkP
  have hs1P' : s1.stk Work.IntLib.SG.sP = gs ++ HvdH.Glyph.mk Work.IntLib.SG.sP :: bP := by
    rw [hs1P, hgs_eq]
  have hs1_0 : s1.stk 0 = R := (hs1fr 0 h0neP).trans h0
  have he1' : HvdH.Eval main (Work.IntLib.SG.stripZeros Work.IntLib.SG.sP Work.IntLib.SG.rgT)
      s s1 n1 := by
    simpa only [Work.IntLib.stripZeros, Work.IntLib.SG.stripZeros] using he1
  have hle1' : n1 ≤ 2 * (rl.length + 1) + 6 := by simpa [List.length_reverse] using hle1
  -- the intermediate states
  let s2 : HvdH.State := ⟨Function.update s1.reg Work.IntLib.SG.rgU HvdH.Glyph.iend, s1.stk⟩
  let s3 : HvdH.State := ⟨s2.reg, Function.update s2.stk 0 (s2.reg Work.IntLib.SG.rgU :: s2.stk 0)⟩
  let s4 : HvdH.State := Work.IntLib.SG.mSt Work.IntLib.SG.sP (HvdH.Glyph.mk Work.IntLib.SG.sP)
    (0 : HvdH.Stk) Work.IntLib.SG.rgT gs bP s3
  let s5 : HvdH.State := ⟨Function.update s4.reg Work.IntLib.SG.rgU HvdH.Glyph.pos, s4.stk⟩
  let s6 : HvdH.State := ⟨s5.reg, Function.update s5.stk 0 (s5.reg Work.IntLib.SG.rgU :: s5.stk 0)⟩
  have ev1 : Work.Layout.Ev main (Work.IntLib.SG.stripZeros Work.IntLib.SG.sP Work.IntLib.SG.rgT)
      s s1 (2 * (rl.length + 1) + 6) := ⟨n1, he1', hle1'⟩
  have ev2 : Work.Layout.Ev main (HvdH.Cmd.set Work.IntLib.SG.rgU HvdH.Glyph.iend) s1 s2 1 :=
    ⟨1, Eval.set _ _ s1, le_rfl⟩
  have ev3 : Work.Layout.Ev main (HvdH.Cmd.push 0 Work.IntLib.SG.rgU) s2 s3 1 :=
    ⟨1, Eval.push (0 : HvdH.Stk) Work.IntLib.SG.rgU s2, le_rfl⟩
  have ev4 : Work.Layout.Ev main
      (Work.IntLib.SG.rLoop Work.IntLib.SG.sP (HvdH.Glyph.mk Work.IntLib.SG.sP) (some 0)
        Work.IntLib.SG.rgT) s3 s4 (7 + gs.length * 5) := by
    have hgsT : ∀ g ∈ gs, g ≠ HvdH.Glyph.mk Work.IntLib.SG.sP := by
      intro g hg hcon
      have h1 : g ∈ ((Work.IntLib.MulS.stripHigh rl).map HvdH.Glyph.bit) := by
        rw [hgs_def] at hg
        exact List.mem_reverse.mp hg
      obtain ⟨b, -, hb⟩ := List.mem_map.mp h1
      exact hbT b (hb.trans hcon)
    have hs3P : s3.stk Work.IntLib.SG.sP = gs ++ HvdH.Glyph.mk Work.IntLib.SG.sP :: bP := by
      dsimp only [s3, s2]
      rw [Function.update_of_ne hPne0]
      exact hs1P'
    exact ⟨_, Work.IntLib.SG.mLoop_eval main Work.IntLib.SG.sP _ (0 : HvdH.Stk)
      Work.IntLib.SG.rgT hTe h0neP gs bP s3 hs3P hgsT, le_rfl⟩
  have ev5 : Work.Layout.Ev main (HvdH.Cmd.set Work.IntLib.SG.rgU HvdH.Glyph.pos) s4 s5 1 :=
    ⟨1, Eval.set _ _ s4, le_rfl⟩
  have ev6 : Work.Layout.Ev main (HvdH.Cmd.push 0 Work.IntLib.SG.rgU) s5 s6 1 :=
    ⟨1, Eval.push (0 : HvdH.Stk) Work.IntLib.SG.rgU s5, le_rfl⟩
  -- the program unfolds to the right-nested sequence of the six steps
  have hprog : Work.Layout.seqs [
      Work.IntLib.SG.stripZeros Work.IntLib.SG.sP Work.IntLib.SG.rgT,
      HvdH.Cmd.set Work.IntLib.SG.rgU HvdH.Glyph.iend,
      HvdH.Cmd.push 0 Work.IntLib.SG.rgU,
      Work.IntLib.SG.rLoop Work.IntLib.SG.sP (HvdH.Glyph.mk Work.IntLib.SG.sP) (some 0)
        Work.IntLib.SG.rgT,
      HvdH.Cmd.set Work.IntLib.SG.rgU HvdH.Glyph.pos,
      HvdH.Cmd.push 0 Work.IntLib.SG.rgU] =
    HvdH.Cmd.seq (Work.IntLib.SG.stripZeros Work.IntLib.SG.sP Work.IntLib.SG.rgT)
      (HvdH.Cmd.seq (HvdH.Cmd.set Work.IntLib.SG.rgU HvdH.Glyph.iend)
        (HvdH.Cmd.seq (HvdH.Cmd.push 0 Work.IntLib.SG.rgU)
          (HvdH.Cmd.seq (Work.IntLib.SG.rLoop Work.IntLib.SG.sP
              (HvdH.Glyph.mk Work.IntLib.SG.sP) (some 0) Work.IntLib.SG.rgT)
            (HvdH.Cmd.seq (HvdH.Cmd.set Work.IntLib.SG.rgU HvdH.Glyph.pos)
              (HvdH.Cmd.push 0 Work.IntLib.SG.rgU))))) := rfl
  have e56 := Work.Layout.Ev.seq ev5 ev6
  have e456 := Work.Layout.Ev.seq ev4 e56
  have e3456 := Work.Layout.Ev.seq ev3 e456
  have e23456 := Work.Layout.Ev.seq ev2 e3456
  have eall := Work.Layout.Ev.seq ev1 e23456
  rw [← hprog] at eall
  -- cost bound
  have hgslen : gs.length ≤ rl.length := by
    rw [hgs_def, List.length_reverse, List.length_map, Work.IntLib.MulS.stripHigh,
      List.length_reverse]
    simpa [List.length_reverse] using List.length_dropWhile_le (fun b : Bool => !b) rl.reverse
  -- the region is the canonical bits of `ofBits rl`
  have hcore : gs.reverse = (Computability.encodeNat (Work.IntLib.ofBits rl)).map HvdH.Glyph.bit := by
    rw [hgs_def, List.reverse_reverse, Work.IntLib.MulS.stripHigh_eq_bits,
      Work.IntLib.encodeNat_eq_bits]
  -- the encoding of the value that is emitted
  have henc : (HvdH.Val.int ((Work.IntLib.ofBits rl : ℕ) : ℤ)).enc ++ R
      = HvdH.Glyph.pos :: ((Computability.encodeNat (Work.IntLib.ofBits rl)).map HvdH.Glyph.bit
          ++ HvdH.Glyph.iend :: R) := by
    rw [Work.IntLib.enc_int]
    rw [ite_eq_right (by simp : ¬ (((Work.IntLib.ofBits rl : ℕ) : ℤ) < 0))]
    rw [Int.natAbs_natCast]
    simp only [List.cons_append, List.append_assoc, List.nil_append]
  have hs6_0 : s6.stk 0 = HvdH.Glyph.pos :: (gs.reverse ++ HvdH.Glyph.iend :: R) := by
    have e : s6.stk 0 = s5.reg Work.IntLib.SG.rgU :: s5.stk 0 := by
      dsimp only [s6]; exact Function.update_self _ _ _
    have e5 : s5.reg Work.IntLib.SG.rgU = HvdH.Glyph.pos := by
      dsimp only [s5]; exact Function.update_self _ _ _
    have e530 : s5.stk 0 = s4.stk 0 := rfl
    have e40 : s4.stk 0 = gs.reverse ++ s3.stk 0 := by
      dsimp only [s4, Work.IntLib.SG.mSt]; exact Function.update_self _ _ _
    have e30 : s3.stk 0 = HvdH.Glyph.iend :: R := by
      have f1 : s3.stk 0 = s2.reg Work.IntLib.SG.rgU :: s2.stk 0 := by
        dsimp only [s3]; exact Function.update_self _ _ _
      have f2 : s2.reg Work.IntLib.SG.rgU = HvdH.Glyph.iend := by
        dsimp only [s2]; exact Function.update_self _ _ _
      have f3 : s2.stk 0 = R := hs1_0
      rw [f1, f2, f3]
    rw [e, e5, e530, e40, e30]
  have hs6_P : s6.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP := by
    have h1 : s6.stk Work.IntLib.SG.sP = s5.stk Work.IntLib.SG.sP := by
      dsimp only [s6]; exact Function.update_of_ne hPne0 _ _
    have h2 : s5.stk Work.IntLib.SG.sP = s4.stk Work.IntLib.SG.sP := rfl
    have h3 : s4.stk Work.IntLib.SG.sP = HvdH.Glyph.mk Work.IntLib.SG.sP :: bP := by
      dsimp only [s4, Work.IntLib.SG.mSt]
      rw [Function.update_of_ne hPne0, Function.update_self]
    rw [h1, h2, h3]
  have hframe : ∀ j : HvdH.Stk, j ≠ 0 → j ≠ Work.IntLib.SG.sP → s6.stk j = s.stk j := by
    intro j hj0 hjP
    have h1 : s6.stk j = s5.stk j := by
      dsimp only [s6]; exact Function.update_of_ne hj0 _ _
    have h2 : s5.stk j = s4.stk j := rfl
    have h3 : s4.stk j = s3.stk j := by
      dsimp only [s4, Work.IntLib.SG.mSt]
      rw [Function.update_of_ne hj0, Function.update_of_ne hjP]
    have h4 : s3.stk j = s2.stk j := by
      dsimp only [s3]; exact Function.update_of_ne hj0 _ _
    have h5 : s2.stk j = s1.stk j := rfl
    have h6 : s1.stk j = s.stk j := hs1fr j hjP
    rw [h1, h2, h3, h4, h5, h6]
  obtain ⟨m, hev, hm⟩ := eall
  exact ⟨s6, m, hev, by omega, by rw [henc, hs6_0, hcore], hs6_P, hframe⟩

end Work.IntLib.SqrtGcd
