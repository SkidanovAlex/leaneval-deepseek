import Mathlib
import Submission.Work.IntLib.mulSDefs
import Submission.Work.IntLib.mulSEv
import Submission.Work.IntLib.encodeNatBridge

/-!
# `peelProg`, strengthened with content below the markers

`Work.IntLib.MulS.peelProg` reads the two values `int a :: int b :: rest` off stack 0, storing the
two sign glyphs on `sS`, the bits of `|a|` (least significant first) on `sA` and the bits of `|b|`
on `sB`, and leaving `encs rest ++ R0` behind on stack 0.

This file proves the version in which each scratch stack may carry arbitrary content `below` its
marker, and that content is preserved.  The proof is the generalisation of the marker-only
statement: every drain is already stated with a `below` parameter, so the ten phases of `peelProg`
are replayed verbatim with the markers replaced by `marker :: below`.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH
open MulS

/-! ## Local list bookkeeping -/

/-- Unfolding of the encoding of an integer value, in terms of `bitsG`. -/
private theorem enc_int_eq_bitsG (z : ℤ) : (Val.int z).enc =
    (if z < 0 then Glyph.neg else Glyph.pos) :: (bitsG z.natAbs ++ [Glyph.iend]) := by
  rw [enc_int, encodeNat_eq_bits]; rfl

private theorem mem_bitsG_ne (n : ℕ) {T : Glyph} (hT : ∀ c : Bool, (Glyph.bit c : Glyph) ≠ T) :
    ∀ g ∈ bitsG n, g ≠ T := by
  intro g hg
  simp only [bitsG, List.mem_map] at hg
  obtain ⟨c, -, rfl⟩ := hg
  exact hT c

private theorem mem_bitsG_rev_ne (n : ℕ) {T : Glyph}
    (hT : ∀ c : Bool, (Glyph.bit c : Glyph) ≠ T) :
    ∀ g ∈ (bitsG n).reverse, g ≠ T := by
  intro g hg
  simp only [bitsG, List.mem_reverse, List.mem_map] at hg
  obtain ⟨c, -, rfl⟩ := hg
  exact hT c

/-- `peelProg` decomposed into its ten primitive steps, right-nested. -/
private theorem peelProg_eq : peelProg = .seq (.pop 0 rSign) (.seq (.push sS rSign)
    (.seq (consume 0 Glyph.iend rL (.push sW rL)) (.seq (.pop 0 rTmp)
    (.seq (consume sW mkW rL (.push sA rL)) (.seq (.pop 0 rSign) (.seq (.push sS rSign)
    (.seq (consume 0 Glyph.iend rL (.push sT rL)) (.seq (.pop 0 rTmp)
      (consume sT mkT rL (.push sB rL)))))))))) := rfl

/-- `peelProg`, strengthened with the content `below` the marker on each scratch stack: it reads
`int a :: int b :: rest` off stack 0 and leaves the sign glyphs on `sS`, the bits of `|a|` (least
significant first) on `sA` and of `|b|` on `sB`, restoring stack 0 to `encs rest ++ R0` and keeping
the content below each marker. -/
theorem mulSPeelEv {main : Cmd} {s : State} {a b : ℤ} {rest : List Val} {R0 : List Glyph}
    {belowA belowB belowS belowT belowW : List Glyph}
    (h0 : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ encs rest ++ R0)
    (hA : s.stk sA = [mkA] ++ belowA) (hB : s.stk sB = [mkB] ++ belowB)
    (hS : s.stk sS = [mkS] ++ belowS)
    (hT : s.stk sT = [mkT] ++ belowT) (hW : s.stk sW = [mkW] ++ belowW) :
    ∃ s' n, Eval main peelProg s s' n ∧
      n ≤ 30 * ((Val.int a).enc.length + (Val.int b).enc.length + 1) + 60 ∧
      s'.stk 0 = encs rest ++ R0 ∧
      s'.stk sA = bitsG a.natAbs ++ [mkA] ++ belowA ∧
      s'.stk sB = bitsG b.natAbs ++ [mkB] ++ belowB ∧
      s'.stk sS = (if b < 0 then Glyph.neg else Glyph.pos)
          :: (if a < 0 then Glyph.neg else Glyph.pos) :: [mkS] ++ belowS ∧
      s'.stk sT = [mkT] ++ belowT ∧ s'.stk sW = [mkW] ++ belowW ∧
      (∀ k : Stk, k ≠ 0 → k ≠ sA → k ≠ sB → k ≠ sS → k ≠ sT → k ≠ sW →
        s'.stk k = s.stk k) := by
  set sa : Glyph := if a < 0 then Glyph.neg else Glyph.pos with hsa
  set sb : Glyph := if b < 0 then Glyph.neg else Glyph.pos with hsb
  set GA : List Glyph := bitsG a.natAbs with hGA
  set GB : List Glyph := bitsG b.natAbs with hGB
  set RR : List Glyph := encs rest ++ R0 with hRR
  have hAenc : (Val.int a).enc = sa :: (GA ++ [Glyph.iend]) := by
    rw [hsa, hGA]; exact enc_int_eq_bitsG a
  have hBenc : (Val.int b).enc = sb :: (GB ++ [Glyph.iend]) := by
    rw [hsb, hGB]; exact enc_int_eq_bitsG b
  rw [hAenc, hBenc] at h0
  simp only [List.cons_append, List.append_assoc, List.nil_append] at h0
  rw [← hRR] at h0
  have h0' : s.stk 0 = sa :: (GA ++ Glyph.iend :: (sb :: (GB ++ Glyph.iend :: RR))) := h0
  have hwsA : ∀ g ∈ GA, g ≠ Glyph.iend := by
    rw [hGA]; exact mem_bitsG_ne a.natAbs (fun c => by simp)
  have hwsAr : ∀ g ∈ GA.reverse, g ≠ mkW := by
    rw [hGA]; exact mem_bitsG_rev_ne a.natAbs (fun c => by simp)
  have hwsB : ∀ g ∈ GB, g ≠ Glyph.iend := by
    rw [hGB]; exact mem_bitsG_ne b.natAbs (fun c => by simp)
  have hwsBr : ∀ g ∈ GB.reverse, g ≠ mkT := by
    rw [hGB]; exact mem_bitsG_rev_ne b.natAbs (fun c => by simp)
  -- step 1: pop the sign of `a`
  let S1 : State := ⟨Function.update s.reg rSign sa,
    Function.update s.stk 0 (GA ++ Glyph.iend :: (sb :: (GB ++ Glyph.iend :: RR)))⟩
  have h1 : Ev main (.pop 0 rSign) s S1 1 := by
    dsimp only [S1]; simpa [h0'] using ev_pop main 0 rSign s
  have h1_0 : S1.stk 0 = GA ++ Glyph.iend :: (sb :: (GB ++ Glyph.iend :: RR)) := by simp [S1]
  have h1_W : S1.stk sW = [mkW] ++ belowW := by
    dsimp only [S1]; rw [Function.update_of_ne (show (sW:Stk) ≠ 0 by decide)]; exact hW
  have h1_S : S1.stk sS = [mkS] ++ belowS := by
    dsimp only [S1]; rw [Function.update_of_ne (show (sS:Stk) ≠ 0 by decide)]; exact hS
  have h1_T : S1.stk sT = [mkT] ++ belowT := by
    dsimp only [S1]; rw [Function.update_of_ne (show (sT:Stk) ≠ 0 by decide)]; exact hT
  have h1_A : S1.stk sA = [mkA] ++ belowA := by
    dsimp only [S1]; rw [Function.update_of_ne (show (sA:Stk) ≠ 0 by decide)]; exact hA
  have h1_B : S1.stk sB = [mkB] ++ belowB := by
    dsimp only [S1]; rw [Function.update_of_ne (show (sB:Stk) ≠ 0 by decide)]; exact hB
  -- step 2: push the sign of `a` on `sS`
  let S2 : State := ⟨S1.reg, Function.update S1.stk sS (sa :: [mkS] ++ belowS)⟩
  have h2 : Ev main (.push sS rSign) S1 S2 1 := by
    dsimp only [S2]
    have hR : S1.reg rSign = sa := by simp [S1]
    simpa [hR, h1_S] using ev_push main sS rSign S1
  have h2_0 : S2.stk 0 = GA ++ Glyph.iend :: (sb :: (GB ++ Glyph.iend :: RR)) := by
    dsimp only [S2]; rw [Function.update_of_ne (show (0:Stk) ≠ sS by decide)]; exact h1_0
  have h2_S : S2.stk sS = sa :: [mkS] ++ belowS := by simp [S2]
  have h2_W : S2.stk sW = [mkW] ++ belowW := by
    dsimp only [S2]; rw [Function.update_of_ne (show (sW:Stk) ≠ sS by decide)]; exact h1_W
  have h2_A : S2.stk sA = [mkA] ++ belowA := by
    dsimp only [S2]; rw [Function.update_of_ne (show (sA:Stk) ≠ sS by decide)]; exact h1_A
  have h2_T : S2.stk sT = [mkT] ++ belowT := by
    dsimp only [S2]; rw [Function.update_of_ne (show (sT:Stk) ≠ sS by decide)]; exact h1_T
  have h2_B : S2.stk sB = [mkB] ++ belowB := by
    dsimp only [S2]; rw [Function.update_of_ne (show (sB:Stk) ≠ sS by decide)]; exact h1_B
  -- step 3: drain stack 0 down to `sW`
  obtain ⟨S3, n3, hev3, hle3, h3_0, h3_W, h3_fr⟩ :=
    drain_ev' (main := main) (src := (0:Stk)) (dst := sW)
      (hne := (by decide : (0:Stk) ≠ sW))
      (T := Glyph.iend) (r := rL) (below := sb :: (GB ++ Glyph.iend :: RR))
      GA ([mkW] ++ belowW) S2 h2_0 h2_W hwsA
  have h3 : Ev main (consume 0 Glyph.iend rL (.push sW rL)) S2 S3 (5 * (GA.length + 1) + 2) :=
    ⟨n3, hev3, hle3⟩
  -- step 4: pop the `iend` of `a`
  let S4 : State := ⟨Function.update S3.reg rTmp Glyph.iend,
    Function.update S3.stk 0 (sb :: (GB ++ Glyph.iend :: RR))⟩
  have h4 : Ev main (.pop 0 rTmp) S3 S4 1 := by
    dsimp only [S4]; simpa [h3_0] using ev_pop main 0 rTmp S3
  have h4_0 : S4.stk 0 = sb :: (GB ++ Glyph.iend :: RR) := by simp [S4]
  have h4_W : S4.stk sW = GA.reverse ++ mkW :: belowW := by
    dsimp only [S4]; rw [Function.update_of_ne (show (sW:Stk) ≠ 0 by decide)]; exact h3_W
  have h4_A : S4.stk sA = [mkA] ++ belowA := by
    dsimp only [S4]; rw [Function.update_of_ne (show (sA:Stk) ≠ 0 by decide)]
    rw [h3_fr sA (by decide) (by decide)]; exact h2_A
  have h4_S : S4.stk sS = sa :: [mkS] ++ belowS := by
    dsimp only [S4]; rw [Function.update_of_ne (show (sS:Stk) ≠ 0 by decide)]
    rw [h3_fr sS (by decide) (by decide)]; exact h2_S
  have h4_T : S4.stk sT = [mkT] ++ belowT := by
    dsimp only [S4]; rw [Function.update_of_ne (show (sT:Stk) ≠ 0 by decide)]
    rw [h3_fr sT (by decide) (by decide)]; exact h2_T
  have h4_B : S4.stk sB = [mkB] ++ belowB := by
    dsimp only [S4]; rw [Function.update_of_ne (show (sB:Stk) ≠ 0 by decide)]
    rw [h3_fr sB (by decide) (by decide)]; exact h2_B
  -- step 5: drain `sW` back onto `sA`
  obtain ⟨S5, n5, hev5, hle5, h5_W, h5_A, h5_fr⟩ :=
    drain_ev' (main := main) (src := sW) (dst := sA) (hne := (by decide : sW ≠ sA))
      (T := mkW) (r := rL) (below := belowW)
      GA.reverse ([mkA] ++ belowA) S4 h4_W h4_A hwsAr
  have h5 : Ev main (consume sW mkW rL (.push sA rL)) S4 S5 (5 * (GA.length + 1) + 2) :=
    ⟨n5, hev5, by simpa [List.length_reverse] using hle5⟩
  have h5_0 : S5.stk 0 = sb :: (GB ++ Glyph.iend :: RR) := by
    rw [h5_fr 0 (by decide) (by decide)]; exact h4_0
  have h5_S : S5.stk sS = sa :: [mkS] ++ belowS := by
    rw [h5_fr sS (by decide) (by decide)]; exact h4_S
  have h5_T : S5.stk sT = [mkT] ++ belowT := by
    rw [h5_fr sT (by decide) (by decide)]; exact h4_T
  have h5_B : S5.stk sB = [mkB] ++ belowB := by
    rw [h5_fr sB (by decide) (by decide)]; exact h4_B
  -- step 6: pop the sign of `b`
  let S6 : State := ⟨Function.update S5.reg rSign sb,
    Function.update S5.stk 0 (GB ++ Glyph.iend :: RR)⟩
  have h6 : Ev main (.pop 0 rSign) S5 S6 1 := by
    dsimp only [S6]; simpa [h5_0] using ev_pop main 0 rSign S5
  have h6_0 : S6.stk 0 = GB ++ Glyph.iend :: RR := by simp [S6]
  have h6_A : S6.stk sA = GA.reverse.reverse ++ [mkA] ++ belowA := by
    dsimp only [S6]; rw [Function.update_of_ne (show (sA:Stk) ≠ 0 by decide)]
    simpa [List.append_assoc] using h5_A
  have h6_S : S6.stk sS = sa :: [mkS] ++ belowS := by
    dsimp only [S6]; rw [Function.update_of_ne (show (sS:Stk) ≠ 0 by decide)]; exact h5_S
  have h6_W : S6.stk sW = [mkW] ++ belowW := by
    dsimp only [S6]; rw [Function.update_of_ne (show (sW:Stk) ≠ 0 by decide)]
    simpa using h5_W
  have h6_T : S6.stk sT = [mkT] ++ belowT := by
    dsimp only [S6]; rw [Function.update_of_ne (show (sT:Stk) ≠ 0 by decide)]; exact h5_T
  have h6_B : S6.stk sB = [mkB] ++ belowB := by
    dsimp only [S6]; rw [Function.update_of_ne (show (sB:Stk) ≠ 0 by decide)]; exact h5_B
  -- step 7: push the sign of `b`
  let S7 : State := ⟨S6.reg, Function.update S6.stk sS (sb :: sa :: [mkS] ++ belowS)⟩
  have h7 : Ev main (.push sS rSign) S6 S7 1 := by
    dsimp only [S7]
    have hR : S6.reg rSign = sb := by simp [S6]
    simpa [hR, h6_S] using ev_push main sS rSign S6
  have h7_0 : S7.stk 0 = GB ++ Glyph.iend :: RR := by
    dsimp only [S7]; rw [Function.update_of_ne (show (0:Stk) ≠ sS by decide)]; exact h6_0
  have h7_S : S7.stk sS = sb :: sa :: [mkS] ++ belowS := by simp [S7]
  have h7_A : S7.stk sA = GA.reverse.reverse ++ [mkA] ++ belowA := by
    dsimp only [S7]; rw [Function.update_of_ne (show (sA:Stk) ≠ sS by decide)]; exact h6_A
  have h7_W : S7.stk sW = [mkW] ++ belowW := by
    dsimp only [S7]; rw [Function.update_of_ne (show (sW:Stk) ≠ sS by decide)]; exact h6_W
  have h7_T : S7.stk sT = [mkT] ++ belowT := by
    dsimp only [S7]; rw [Function.update_of_ne (show (sT:Stk) ≠ sS by decide)]; exact h6_T
  have h7_B : S7.stk sB = [mkB] ++ belowB := by
    dsimp only [S7]; rw [Function.update_of_ne (show (sB:Stk) ≠ sS by decide)]; exact h6_B
  -- step 8: drain stack 0 down to `sT`
  obtain ⟨S8, n8, hev8, hle8, h8_0, h8_T, h8_fr⟩ :=
    drain_ev' (main := main) (src := (0:Stk)) (dst := sT)
      (hne := (by decide : (0:Stk) ≠ sT))
      (T := Glyph.iend) (r := rL) (below := RR)
      GB ([mkT] ++ belowT) S7 h7_0 h7_T hwsB
  have h8 : Ev main (consume 0 Glyph.iend rL (.push sT rL)) S7 S8 (5 * (GB.length + 1) + 2) :=
    ⟨n8, hev8, hle8⟩
  -- step 9: pop the `iend` of `b`
  let S9 : State := ⟨Function.update S8.reg rTmp Glyph.iend, Function.update S8.stk 0 RR⟩
  have h9 : Ev main (.pop 0 rTmp) S8 S9 1 := by
    dsimp only [S9]; simpa [h8_0] using ev_pop main 0 rTmp S8
  have h9_0 : S9.stk 0 = RR := by simp [S9]
  -- step 10: drain `sT` back onto `sB`
  obtain ⟨S10, n10, hev10, hle10, h10_T, h10_B, h10_fr⟩ :=
    drain_ev' (main := main) (src := sT) (dst := sB) (hne := (by decide : sT ≠ sB))
      (T := mkT) (r := rL) (below := belowT)
      GB.reverse ([mkB] ++ belowB) S9
      (by
        dsimp only [S9]; rw [Function.update_of_ne (show (sT:Stk) ≠ 0 by decide)]
        exact h8_T)
      (by
        dsimp only [S9]; rw [Function.update_of_ne (show (sB:Stk) ≠ 0 by decide)]
        rw [h8_fr sB (by decide) (by decide)]; exact h7_B)
      hwsBr
  have h10 : Ev main (consume sT mkT rL (.push sB rL)) S9 S10 (5 * (GB.length + 1) + 2) :=
    ⟨n10, hev10, by simpa [List.length_reverse] using hle10⟩
  -- ## Composition
  have e910 : Ev main (.seq (.pop 0 rTmp) (consume sT mkT rL (.push sB rL))) S8 S10
      (1 + (5 * (GB.length + 1) + 2)) := Ev.seq h9 h10
  have e810 : Ev main (.seq (consume 0 Glyph.iend rL (.push sT rL))
      (.seq (.pop 0 rTmp) (consume sT mkT rL (.push sB rL)))) S7 S10
      ((5 * (GB.length + 1) + 2) + (1 + (5 * (GB.length + 1) + 2))) := Ev.seq h8 e910
  have e710 : Ev main (.seq (.push sS rSign) (.seq (consume 0 Glyph.iend rL (.push sT rL))
      (.seq (.pop 0 rTmp) (consume sT mkT rL (.push sB rL))))) S6 S10
      (1 + ((5 * (GB.length + 1) + 2) + (1 + (5 * (GB.length + 1) + 2)))) := Ev.seq h7 e810
  have e610 : Ev main (.seq (.pop 0 rSign) (.seq (.push sS rSign)
      (.seq (consume 0 Glyph.iend rL (.push sT rL))
      (.seq (.pop 0 rTmp) (consume sT mkT rL (.push sB rL)))))) S5 S10
      (1 + (1 + ((5 * (GB.length + 1) + 2) + (1 + (5 * (GB.length + 1) + 2))))) :=
    Ev.seq h6 e710
  have e510 : Ev main (.seq (consume sW mkW rL (.push sA rL)) (.seq (.pop 0 rSign)
      (.seq (.push sS rSign) (.seq (consume 0 Glyph.iend rL (.push sT rL))
      (.seq (.pop 0 rTmp) (consume sT mkT rL (.push sB rL))))))) S4 S10
      ((5 * (GA.length + 1) + 2)
        + (1 + (1 + ((5 * (GB.length + 1) + 2) + (1 + (5 * (GB.length + 1) + 2)))))) :=
    Ev.seq h5 e610
  have e410 : Ev main (.seq (.pop 0 rTmp) (.seq (consume sW mkW rL (.push sA rL))
      (.seq (.pop 0 rSign) (.seq (.push sS rSign) (.seq (consume 0 Glyph.iend rL (.push sT rL))
      (.seq (.pop 0 rTmp) (consume sT mkT rL (.push sB rL)))))))) S3 S10
      (1 + ((5 * (GA.length + 1) + 2)
        + (1 + (1 + ((5 * (GB.length + 1) + 2) + (1 + (5 * (GB.length + 1) + 2))))))) :=
    Ev.seq h4 e510
  have e310 : Ev main (.seq (consume 0 Glyph.iend rL (.push sW rL))
      (.seq (.pop 0 rTmp) (.seq (consume sW mkW rL (.push sA rL))
      (.seq (.pop 0 rSign) (.seq (.push sS rSign) (.seq (consume 0 Glyph.iend rL (.push sT rL))
      (.seq (.pop 0 rTmp) (consume sT mkT rL (.push sB rL))))))))) S2 S10
      ((5 * (GA.length + 1) + 2) + (1 + ((5 * (GA.length + 1) + 2)
        + (1 + (1 + ((5 * (GB.length + 1) + 2) + (1 + (5 * (GB.length + 1) + 2)))))))) :=
    Ev.seq h3 e410
  have e210 : Ev main (.seq (.push sS rSign) (.seq (consume 0 Glyph.iend rL (.push sW rL))
      (.seq (.pop 0 rTmp) (.seq (consume sW mkW rL (.push sA rL))
      (.seq (.pop 0 rSign) (.seq (.push sS rSign) (.seq (consume 0 Glyph.iend rL (.push sT rL))
      (.seq (.pop 0 rTmp) (consume sT mkT rL (.push sB rL)))))))))) S1 S10
      (1 + ((5 * (GA.length + 1) + 2) + (1 + ((5 * (GA.length + 1) + 2)
        + (1 + (1 + ((5 * (GB.length + 1) + 2) + (1 + (5 * (GB.length + 1) + 2))))))))) :=
    Ev.seq h2 e310
  have e1 : Ev main peelProg s S10
      (1 + (1 + ((5 * (GA.length + 1) + 2) + (1 + ((5 * (GA.length + 1) + 2)
        + (1 + (1 + ((5 * (GB.length + 1) + 2) + (1 + (5 * (GB.length + 1) + 2)))))))))) := by
    rw [peelProg_eq]
    exact Ev.seq h1 e210
  have hframe : ∀ k : Stk, k ≠ 0 → k ≠ sA → k ≠ sB → k ≠ sS → k ≠ sT → k ≠ sW →
      S10.stk k = s.stk k := by
    intro k hk0 hkA hkB hkS hkT hkW
    refine Ev.frame e1 (S := ({0, sA, sB, sS, sT, sW} : Finset Stk)) (by decide) ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hk0, hkA, hkB, hkS, hkT, hkW⟩
  obtain ⟨n, hev, hle⟩ := e1
  refine ⟨S10, n, hev, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hframe⟩
  · have hlenA : (Val.int a).enc.length = GA.length + 2 := by
      rw [vsz_int, isz_eq, hGA, bitsG_length]
    have hlenB : (Val.int b).enc.length = GB.length + 2 := by
      rw [vsz_int, isz_eq, hGB, bitsG_length]
    omega
  · rw [h10_fr 0 (by decide) (by decide)]; exact h9_0
  · rw [show S10.stk sA = S5.stk sA from
      Ev.frame e610 (S := ({0, sS, sT, sB} : Finset Stk)) (by decide) (by decide)]
    rw [h5_A, List.reverse_reverse]
    simp only [List.append_assoc]
  · rw [h10_B, List.reverse_reverse]
    simp only [List.append_assoc]
  · rw [show S10.stk sS = S7.stk sS from
      Ev.frame e810 (S := ({0, sT, sB} : Finset Stk)) (by decide) (by decide)]
    exact h7_S
  · simpa using h10_T
  · rw [show S10.stk sW = S5.stk sW from
      Ev.frame e610 (S := ({0, sS, sT, sB} : Finset Stk)) (by decide) (by decide)]
    simpa using h5_W

end Work.IntLib
