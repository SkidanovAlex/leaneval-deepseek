import Mathlib
import Submission.Work.Resample.MulNW.Defs
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.Kernel.Raw

/-!
# `Work.Resample.MulNW.peel_ev`

`peelProg` peels the two integers `int a :: int b :: rest` off the value stack: the two sign glyphs
go to `sS`, the bits of `a` (least significant first) to `sA`, the bits of `b` to `sB`, and `rest`
is left on stack 0.  This file proves the phase specification `PeelSpec main a b rest R`, with the
linear cost bound `40 * (size a + size b + 2)`.

The four `consume` drains are instances of the shared library lemma
`Work.IntLib.consume_push_rev`, which is stated for the raw `Work.IntLib.consume` (loop sentinel
`Glyph.mk 0`) that `Work.Resample.MulNW` uses -- *not* the `MulS` copy of `mulSPeel`, whose stop
glyph is `mkStop`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Resample.MulNW

open HvdH
open Work.IntLib.MulS (Ev ev_pop ev_push ev_set)

/-! ## Small facts about the layout -/

/-- the encoding of `int n` for a natural number `n` -/
theorem pos_enc_ofNat (n : ℕ) :
    (Val.int (n : ℤ)).enc = Glyph.pos :: (natBits n ++ [Glyph.iend]) := by
  rw [Work.IntLib.enc_int, Work.IntLib.encodeNat_eq_bits, Int.natAbs_natCast,
    ite_eq_right (by omega : ¬ ((n : ℤ) < 0))]

private theorem natBits_length (n : ℕ) : (natBits n).length = n.size := by
  simp [natBits, bitsG, Nat.size_eq_bits_len]

theorem natBits_ne_iend (n : ℕ) : ∀ g ∈ natBits n, g ≠ Glyph.iend :=
  fun g hg => bitsG_ne_iend n.bits g hg

theorem reverse_natBits_ne_mk (n : ℕ) (i : Fin 16) :
    ∀ g ∈ (natBits n).reverse, g ≠ Glyph.mk i := by
  intro g hg
  rw [List.mem_reverse] at hg
  exact bitsG_ne_mkA n.bits g hg i

/-- `peelProg` as its ten primitive steps, right-nested. -/
theorem peelProg_eq : peelProg = .seq (.pop 0 rSign) (.seq (.push sS rSign)
    (.seq (consume 0 Glyph.iend rL (.push sW rL)) (.seq (.pop 0 rTmp)
    (.seq (consume sW mkW rL (.push sA rL)) (.seq (.pop 0 rSign) (.seq (.push sS rSign)
    (.seq (consume 0 Glyph.iend rL (.push sT rL)) (.seq (.pop 0 rTmp)
      (consume sT mkT rL (.push sB rL)))))))))) := rfl

/-! ## The phase lemma -/

theorem peel_ev (main : HvdH.Cmd) (a b : ℕ) (rest : List HvdH.Val) (R : List HvdH.Glyph) : Work.Resample.MulNW.PeelSpec main a b rest R := by
  intro bkT bkW s h0 hW hT
  -- ## the decomposed value stack
  set GA : List Glyph := natBits a with hGA
  set GB : List Glyph := natBits b with hGB
  set RR : List Glyph := encs rest ++ R with hRR
  have hAenc : (Val.int (a : ℤ)).enc = Glyph.pos :: (GA ++ [Glyph.iend]) := by
    rw [hGA]; exact pos_enc_ofNat a
  have hBenc : (Val.int (b : ℤ)).enc = Glyph.pos :: (GB ++ [Glyph.iend]) := by
    rw [hGB]; exact pos_enc_ofNat b
  have h0' : s.stk 0 = Glyph.pos :: (GA ++ Glyph.iend ::
      (Glyph.pos :: (GB ++ Glyph.iend :: RR))) := by
    rw [Work.Kernel.encs_cons, Work.Kernel.encs_cons, hAenc, hBenc] at h0
    simp only [List.append_assoc] at h0
    rw [← hRR] at h0
    rw [h0]
    simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  -- ## the drain hypotheses
  have hGAi : ∀ g ∈ GA, g ≠ Glyph.iend := by
    intro g hg; rw [hGA] at hg; exact natBits_ne_iend a g hg
  have hGAim : ∀ g ∈ GA.reverse, g ≠ mkW := by
    intro g hg; rw [hGA] at hg
    simpa [mkW] using reverse_natBits_ne_mk a 7 g hg
  have hGBi : ∀ g ∈ GB, g ≠ Glyph.iend := by
    intro g hg; rw [hGB] at hg; exact natBits_ne_iend b g hg
  have hGBim : ∀ g ∈ GB.reverse, g ≠ mkT := by
    intro g hg; rw [hGB] at hg
    simpa [mkT] using reverse_natBits_ne_mk b 6 g hg
  -- ## step 1: pop the sign of `a`
  let S1 : State := ⟨Function.update s.reg rSign Glyph.pos,
    Function.update s.stk 0 (GA ++ Glyph.iend :: (Glyph.pos :: (GB ++ Glyph.iend :: RR)))⟩
  have h1 : Ev main (.pop 0 rSign) s S1 1 := by
    dsimp only [S1]; simpa [h0'] using ev_pop main 0 rSign s
  have h1_0 : S1.stk 0 = GA ++ Glyph.iend :: (Glyph.pos :: (GB ++ Glyph.iend :: RR)) := by
    simp [S1]
  have h1_A : S1.stk sA = s.stk sA := by
    dsimp only [S1]; rw [Function.update_of_ne (show (sA : Stk) ≠ 0 by decide)]
  have h1_B : S1.stk sB = s.stk sB := by
    dsimp only [S1]; rw [Function.update_of_ne (show (sB : Stk) ≠ 0 by decide)]
  have h1_S : S1.stk sS = s.stk sS := by
    dsimp only [S1]; rw [Function.update_of_ne (show (sS : Stk) ≠ 0 by decide)]
  have h1_W : S1.stk sW = mkW :: bkW := by
    dsimp only [S1]; rw [Function.update_of_ne (show (sW : Stk) ≠ 0 by decide)]; exact hW
  have h1_T : S1.stk sT = mkT :: bkT := by
    dsimp only [S1]; rw [Function.update_of_ne (show (sT : Stk) ≠ 0 by decide)]; exact hT
  have h1_r : S1.reg rSign = Glyph.pos := by simp [S1]
  -- ## step 2: push it on `sS`
  let S2 : State := ⟨S1.reg, Function.update S1.stk sS (Glyph.pos :: S1.stk sS)⟩
  have h2 : Ev main (.push sS rSign) S1 S2 1 := by
    dsimp only [S2]; simpa [h1_r] using ev_push main sS rSign S1
  have h2_0 : S2.stk 0 = GA ++ Glyph.iend :: (Glyph.pos :: (GB ++ Glyph.iend :: RR)) := by
    dsimp only [S2]; rw [Function.update_of_ne (show (0 : Stk) ≠ sS by decide)]; exact h1_0
  have h2_A : S2.stk sA = s.stk sA := by
    dsimp only [S2]; rw [Function.update_of_ne (show (sA : Stk) ≠ sS by decide)]; exact h1_A
  have h2_B : S2.stk sB = s.stk sB := by
    dsimp only [S2]; rw [Function.update_of_ne (show (sB : Stk) ≠ sS by decide)]; exact h1_B
  have h2_S : S2.stk sS = Glyph.pos :: s.stk sS := by
    dsimp only [S2]; rw [Function.update_self, h1_S]
  have h2_T : S2.stk sT = mkT :: bkT := by
    dsimp only [S2]; rw [Function.update_of_ne (show (sT : Stk) ≠ sS by decide)]; exact h1_T
  have h2_W : S2.stk sW = mkW :: bkW := by
    dsimp only [S2]; rw [Function.update_of_ne (show (sW : Stk) ≠ sS by decide)]; exact h1_W
  -- ## step 3: drain the bits of `a` from stack 0 to `sW`
  obtain ⟨S3, n3, hev3, hle3, h3_0, h3_W, h3_fr⟩ :=
    Work.IntLib.consume_push_rev main 0 Glyph.iend sW rL GA
      (Glyph.pos :: (GB ++ Glyph.iend :: RR)) (mkW :: bkW) (by decide) hGAi S2 h2_0 h2_W
  have h3 : Ev main (consume 0 Glyph.iend rL (.push sW rL)) S2 S3 (5 * GA.length + 8) :=
    ⟨n3, hev3, hle3⟩
  have h3_A : S3.stk sA = s.stk sA := (h3_fr sA (by decide) (by decide)).trans h2_A
  have h3_B : S3.stk sB = s.stk sB := (h3_fr sB (by decide) (by decide)).trans h2_B
  have h3_S : S3.stk sS = Glyph.pos :: s.stk sS := (h3_fr sS (by decide) (by decide)).trans h2_S
  have h3_T : S3.stk sT = mkT :: bkT := (h3_fr sT (by decide) (by decide)).trans h2_T
  -- ## step 4: drop the `iend` of `a`
  let S4 : State := ⟨Function.update S3.reg rTmp Glyph.iend,
    Function.update S3.stk 0 (Glyph.pos :: (GB ++ Glyph.iend :: RR))⟩
  have h4 : Ev main (.pop 0 rTmp) S3 S4 1 := by
    dsimp only [S4]; simpa [h3_0] using ev_pop main 0 rTmp S3
  have h4_0 : S4.stk 0 = Glyph.pos :: (GB ++ Glyph.iend :: RR) := by simp [S4]
  have h4_A : S4.stk sA = s.stk sA := by
    dsimp only [S4]; rw [Function.update_of_ne (show (sA : Stk) ≠ 0 by decide)]; exact h3_A
  have h4_B : S4.stk sB = s.stk sB := by
    dsimp only [S4]; rw [Function.update_of_ne (show (sB : Stk) ≠ 0 by decide)]; exact h3_B
  have h4_S : S4.stk sS = Glyph.pos :: s.stk sS := by
    dsimp only [S4]; rw [Function.update_of_ne (show (sS : Stk) ≠ 0 by decide)]; exact h3_S
  have h4_T : S4.stk sT = mkT :: bkT := by
    dsimp only [S4]; rw [Function.update_of_ne (show (sT : Stk) ≠ 0 by decide)]; exact h3_T
  have h4_W : S4.stk sW = GA.reverse ++ mkW :: bkW := by
    dsimp only [S4]; rw [Function.update_of_ne (show (sW : Stk) ≠ 0 by decide)]; exact h3_W
  -- ## step 5: drain `sW` back to `sA`
  obtain ⟨S5, n5, hev5, hle5, h5_W, h5_A, h5_fr⟩ :=
    Work.IntLib.consume_push_rev main sW mkW sA rL GA.reverse bkW (s.stk sA)
      (by decide) hGAim S4 h4_W h4_A
  have h5 : Ev main (consume sW mkW rL (.push sA rL)) S4 S5 (5 * GA.length + 8) :=
    ⟨n5, hev5, by simpa [List.length_reverse] using hle5⟩
  have h5_0 : S5.stk 0 = Glyph.pos :: (GB ++ Glyph.iend :: RR) :=
    (h5_fr 0 (by decide) (by decide)).trans h4_0
  have h5_B : S5.stk sB = s.stk sB := (h5_fr sB (by decide) (by decide)).trans h4_B
  have h5_S : S5.stk sS = Glyph.pos :: s.stk sS :=
    (h5_fr sS (by decide) (by decide)).trans h4_S
  have h5_T : S5.stk sT = mkT :: bkT := (h5_fr sT (by decide) (by decide)).trans h4_T
  -- ## step 6: pop the sign of `b`
  let S6 : State := ⟨Function.update S5.reg rSign Glyph.pos,
    Function.update S5.stk 0 (GB ++ Glyph.iend :: RR)⟩
  have h6 : Ev main (.pop 0 rSign) S5 S6 1 := by
    dsimp only [S6]; simpa [h5_0] using ev_pop main 0 rSign S5
  have h6_0 : S6.stk 0 = GB ++ Glyph.iend :: RR := by simp [S6]
  have h6_B : S6.stk sB = s.stk sB := by
    dsimp only [S6]; rw [Function.update_of_ne (show (sB : Stk) ≠ 0 by decide)]; exact h5_B
  have h6_T : S6.stk sT = mkT :: bkT := by
    dsimp only [S6]; rw [Function.update_of_ne (show (sT : Stk) ≠ 0 by decide)]; exact h5_T
  have h6_r : S6.reg rSign = Glyph.pos := by simp [S6]
  have h6_S : S6.stk sS = Glyph.pos :: s.stk sS := by
    dsimp only [S6]; rw [Function.update_of_ne (show (sS : Stk) ≠ 0 by decide)]; exact h5_S
  -- ## step 7: push the sign of `b`
  let S7 : State := ⟨S6.reg, Function.update S6.stk sS (Glyph.pos :: S6.stk sS)⟩
  have h7 : Ev main (.push sS rSign) S6 S7 1 := by
    dsimp only [S7]; simpa [h6_r] using ev_push main sS rSign S6
  have h7_0 : S7.stk 0 = GB ++ Glyph.iend :: RR := by
    dsimp only [S7]; rw [Function.update_of_ne (show (0 : Stk) ≠ sS by decide)]; exact h6_0
  have h7_B : S7.stk sB = s.stk sB := by
    dsimp only [S7]; rw [Function.update_of_ne (show (sB : Stk) ≠ sS by decide)]; exact h6_B
  have h7_T : S7.stk sT = mkT :: bkT := by
    dsimp only [S7]; rw [Function.update_of_ne (show (sT : Stk) ≠ sS by decide)]; exact h6_T
  have h7_S : S7.stk sS = Glyph.pos :: Glyph.pos :: s.stk sS := by
    dsimp only [S7]; rw [Function.update_self, h6_S]
  -- ## step 8: drain the bits of `b` from stack 0 to `sT`
  obtain ⟨S8, n8, hev8, hle8, h8_0, h8_T, h8_fr⟩ :=
    Work.IntLib.consume_push_rev main 0 Glyph.iend sT rL GB (encs rest ++ R) (mkT :: bkT)
      (by decide) hGBi S7 h7_0 h7_T
  have h8 : Ev main (consume 0 Glyph.iend rL (.push sT rL)) S7 S8 (5 * GB.length + 8) :=
    ⟨n8, hev8, hle8⟩
  have h8_B : S8.stk sB = s.stk sB := (h8_fr sB (by decide) (by decide)).trans h7_B
  -- ## step 9: drop the `iend` of `b`
  let S9 : State := ⟨Function.update S8.reg rTmp Glyph.iend, Function.update S8.stk 0 RR⟩
  have h9 : Ev main (.pop 0 rTmp) S8 S9 1 := by
    dsimp only [S9]; simpa [h8_0] using ev_pop main 0 rTmp S8
  have h9_0 : S9.stk 0 = RR := by simp [S9]
  have h9_B : S9.stk sB = s.stk sB := by
    dsimp only [S9]; rw [Function.update_of_ne (show (sB : Stk) ≠ 0 by decide)]; exact h8_B
  have h9_T : S9.stk sT = GB.reverse ++ mkT :: bkT := by
    dsimp only [S9]; rw [Function.update_of_ne (show (sT : Stk) ≠ 0 by decide)]; exact h8_T
  -- ## step 10: drain `sT` to `sB`
  obtain ⟨S10, n10, hev10, hle10, h10_T, h10_B, h10_fr⟩ :=
    Work.IntLib.consume_push_rev main sT mkT sB rL GB.reverse bkT (s.stk sB)
      (by decide) hGBim S9 h9_T h9_B
  have h10 : Ev main (consume sT mkT rL (.push sB rL)) S9 S10 (5 * GB.length + 8) :=
    ⟨n10, hev10, by simpa [List.length_reverse] using hle10⟩
  -- ## the composite runs
  have e910 := Ev.seq h9 h10
  have e810 := Ev.seq h8 e910
  have e710 := Ev.seq h7 e810
  have e610 := Ev.seq h6 e710
  have e510 := Ev.seq h5 e610
  have e410 := Ev.seq h4 e510
  have e310 := Ev.seq h3 e410
  have e210 := Ev.seq h2 e310
  have e110 := Ev.seq h1 e210
  -- ## the frame fact (before `e110` is consumed by `obtain`)
  have hfrm : ∀ j : Stk, j ∉ ({0, sA, sB, sS, sT, sW} : Finset Stk) → S10.stk j = s.stk j :=
    fun j hj => Ev.frame e110 (S := ({0, sA, sB, sS, sT, sW} : Finset Stk)) (by decide) hj
  -- ## conclusion
  obtain ⟨n, hev, hle⟩ := e110
  rw [← peelProg_eq] at hev
  refine ⟨S10, n, hev, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    have hl1 : GA.length = a.size := by rw [hGA]; exact natBits_length a
    have hl2 : GB.length = b.size := by rw [hGB]; exact natBits_length b
    rw [hl1, hl2] at hle
    omega
  · -- stack 0
    rw [h10_fr 0 (by decide) (by decide), h9_0]
  · -- sA
    have h : S10.stk sA = S5.stk sA :=
      Ev.frame e610 (S := ({0, sS, sT, sB} : Finset Stk)) (by decide) (by decide)
    rw [h, h5_A, List.reverse_reverse]
  · -- sB
    rw [h10_B, List.reverse_reverse]
  · -- sS
    have h : S10.stk sS = S7.stk sS :=
      Ev.frame e810 (S := ({0, sT, sB} : Finset Stk)) (by decide) (by decide)
    rw [h, h7_S]
  · -- sW
    have h : S10.stk sW = S5.stk sW :=
      Ev.frame e610 (S := ({0, sS, sT, sB} : Finset Stk)) (by decide) (by decide)
    rw [h, h5_W, hW]
  · -- sT
    rw [h10_T, hT]
  · -- the frame
    exact hfrm

end Work.Resample.MulNW
