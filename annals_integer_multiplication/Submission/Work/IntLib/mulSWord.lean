import Mathlib
import Submission.Work.IntLib.mulSDefs
import Submission.Work.IntLib.mulSArith
import Submission.Work.IntLib.mulSEv
import Submission.Work.IntLib.mulSProgEv
import Submission.Work.IntLib.mulSInitEv
import Submission.Work.IntLib.mulSPeelEv
import Submission.Work.IntLib.mulSProgLoop
import Submission.Work.IntLib.mulSProgFinal

/-!
# `Work.IntLib.mulSWord` : schoolbook integer multiplication in `O(isz a * isz b)`

The word `mulSProg` multiplies the two integers on top of the value stack in quadratic time.
The proof chains the six phases of `mulSProg`:

* `openProg`   (marker bookkeeping, `mulSProgEv.openProg_ev`),
* `peelProg`   (read the operands: `mulSPeelEv`),
* `initRProg`  (lay down the initial remainder: `mulSInitEv`),
* `mainLoopProg` (the serial multiplier: `mulSMainLoopEv`),
* `finalizeProg` (assemble the product: `mulSFinalizeEv`),
* `closeProg`  (pop the markers: `mulSProgEv.closeProg_ev`),

and finishes with the encoding arithmetic (`mulSProgEv.enc_ofBits_product`).
-/

set_option autoImplicit false
open HvdH

namespace Work.IntLib
open MulS

theorem mulSWord : ∃ (p : HvdH.Cmd) (K : ℕ), ∀ main, HvdH.BinOp main p (fun _ _ => True) (· * ·) (fun a b => K * HvdH.isz a * HvdH.isz b) := by
  refine ⟨mulSProg, 1000, ?_⟩
  intro main vs hpre s R h0
  obtain ⟨a, b, rest, hvs, -⟩ := hpre
  subst hvs
  have h0a : s.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ encs rest ++ R := by
    rw [h0]
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]
  -- phase 1: markers
  obtain ⟨S1, n1, hE1, hn1, h1_0, h1A, h1B, h1R, h1C, h1S, h1T, h1W, h1U, h1z, h1ie, h1fr⟩ :=
    openProg_ev main s
  -- phase 2: peel
  have h1_0p : S1.stk 0 = (Val.int a).enc ++ (Val.int b).enc ++ encs rest ++ R := by
    rw [h1_0]; exact h0a
  obtain ⟨S2, n2, hE2, hn2, h2_0, h2A, h2B, h2S, h2T, h2W, h2fr⟩ :=
    mulSPeelEv (main := main) (s := S1) (a := a) (b := b) (rest := rest) (R0 := R)
      (belowA := s.stk sA) (belowB := s.stk sB) (belowS := s.stk sS)
      (belowT := s.stk sT) (belowW := s.stk sW) h1_0p h1A h1B h1S h1T h1W
  have h2R : S2.stk sR = [mkR] ++ s.stk sR := by
    rw [h2fr sR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1R]
  have h2C : S2.stk sC = [mkC] ++ s.stk sC := by
    rw [h2fr sC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1C]
  have h2U : S2.stk sU = [mkU] ++ s.stk sU := by
    rw [h2fr sU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1U]
  have h2z : S2.reg rZ = Glyph.bit false := by
    rw [eval_reg_frame hE2 (by decide : rZ ∉ cmdRegs peelProg)]; exact h1z
  have h2ie : S2.reg rIe = Glyph.iend := by
    rw [eval_reg_frame hE2 (by decide : rIe ∉ cmdRegs peelProg)]; exact h1ie
  -- phase 3: initialise the remainder
  have h2Abits : S2.stk sA = (a.natAbs.bits).map Glyph.bit ++ [mkA] ++ s.stk sA := by
    rw [h2A]; rfl
  obtain ⟨S3, n3, hE3, hn3, h3A, h3R, h3W, h3fr⟩ :=
    mulSInitEv (main := main) (s := S2) (α := a.natAbs.bits)
      (belowA := s.stk sA) (belowW := s.stk sW) (bR := [mkR] ++ s.stk sR)
      h2Abits h2W h2R h2z
  have h3R' : S3.stk sR = (List.replicate (a.natAbs.bits).length false).map Glyph.bit
      ++ [mkR] ++ s.stk sR := by
    rw [h3R, List.append_assoc]
  have h3B : S3.stk sB = (b.natAbs.bits).map Glyph.bit ++ [mkB] ++ s.stk sB := by
    rw [h3fr sB (by decide) (by decide) (by decide), h2B]; rfl
  have h3C : S3.stk sC = ([] : List Bool).map Glyph.bit ++ [mkC] ++ s.stk sC := by
    rw [h3fr sC (by decide) (by decide) (by decide), h2C]; rfl
  have h3T : S3.stk sT = [mkT] ++ s.stk sT := by
    rw [h3fr sT (by decide) (by decide) (by decide), h2T]
  have h3ie : S3.reg rIe = Glyph.iend := by
    rw [eval_reg_frame hE3 (by decide : rIe ∉ cmdRegs initRProg)]; exact h2ie
  -- phase 4: the multiplier loop
  obtain ⟨S4, n4, hE4, hn4, h4B, h4A, h4R, h4C, h4W, h4T, h4fr⟩ :=
    mulSProgLoop (main := main) (s := S3) (alpha := a.natAbs.bits) (bbits := b.natAbs.bits)
      (rho0 := List.replicate (a.natAbs.bits).length false) (acc := [])
      (belowA := s.stk sA) (belowB := s.stk sB) (belowR := s.stk sR) (belowC := s.stk sC)
      (belowT := s.stk sT) (belowW := s.stk sW)
      h3B h3A h3R' h3C h3W h3T (by simp [List.length_replicate])
  have h4S : S4.stk sS = (if b < 0 then Glyph.neg else Glyph.pos)
      :: (if a < 0 then Glyph.neg else Glyph.pos) :: [mkS] ++ s.stk sS := by
    rw [h4fr sS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [h3fr sS (by decide) (by decide) (by decide)]
    exact h2S
  have h4U : S4.stk sU = [mkU] ++ s.stk sU := by
    rw [h4fr sU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [h3fr sU (by decide) (by decide) (by decide)]
    exact h2U
  have h4_0 : S4.stk 0 = encs rest ++ R := by
    rw [h4fr 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    rw [h3fr 0 (by decide) (by decide) (by decide)]
    exact h2_0
  have h4ie : S4.reg rIe = Glyph.iend := by
    rw [eval_reg_frame hE4 (by decide : rIe ∉ cmdRegs mainLoopProg)]; exact h3ie
  -- phase 5: finalize
  obtain ⟨S5, n5, hE5, hn5, h5_0, h5R, h5C, h5S, h5T, h5U, h5fr⟩ :=
    mulSProgFinal (main := main) (s := S4)
      (acc := (run (a.natAbs.bits) (b.natAbs.bits) []
        (List.replicate (a.natAbs.bits).length false)).1)
      (rho := (run (a.natAbs.bits) (b.natAbs.bits) []
        (List.replicate (a.natAbs.bits).length false)).2)
      (sa := (if a < 0 then Glyph.neg else Glyph.pos))
      (sb := (if b < 0 then Glyph.neg else Glyph.pos))
      (below0 := encs rest ++ R) (belowR := s.stk sR) (belowC := s.stk sC)
      (belowS := s.stk sS) (belowT := s.stk sT) (belowU := s.stk sU)
      h4_0 h4R h4C h4S h4T h4U h4ie
  -- phase 6: cleanup
  have h5A : S5.stk sA = (a.natAbs.bits).map Glyph.bit ++ [mkA] ++ s.stk sA := by
    rw [h5fr sA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h4A
  have h5B : S5.stk sB = [mkB] ++ s.stk sB := by
    rw [h5fr sB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h4B
  have h5W : S5.stk sW = [mkW] ++ s.stk sW := by
    rw [h5fr sW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h4W
  have h5A' : S5.stk sA = (a.natAbs.bits).map Glyph.bit ++ mkA :: s.stk sA := by
    rw [h5A, List.append_assoc, List.singleton_append]
  have h5B' : S5.stk sB = mkB :: s.stk sB := by rw [h5B, List.singleton_append]
  have h5R' : S5.stk sR = mkR :: s.stk sR := by rw [h5R, List.singleton_append]
  have h5C' : S5.stk sC = mkC :: s.stk sC := by rw [h5C, List.singleton_append]
  have h5T' : S5.stk sT = mkT :: s.stk sT := by rw [h5T, List.singleton_append]
  have h5W' : S5.stk sW = mkW :: s.stk sW := by rw [h5W, List.singleton_append]
  have h5U' : S5.stk sU = mkU :: s.stk sU := by rw [h5U, List.singleton_append]
  have h5ws : ∀ g ∈ (a.natAbs.bits).map Glyph.bit, g ≠ mkA := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hg
    intro h; cases h
  obtain ⟨S6, n6, hE6, hn6, h6_0, h6A, h6B, h6R, h6C, h6T, h6W, h6U, h6fr⟩ :=
    closeProg_ev (main := main) (s := S5) ((a.natAbs.bits).map Glyph.bit)
      (s.stk sA) (s.stk sB) (s.stk sR) (s.stk sC) (s.stk sT) (s.stk sW) (s.stk sU)
      h5ws h5A' h5B' h5R' h5C' h5T' h5W' h5U'
  -- the run
  have hEv : Ev main mulSProg s S6 (n1 + (n2 + (n3 + (n4 + (n5 + n6))))) := by
    have hprog : mulSProg = .seq openProg (.seq peelProg (.seq initRProg
        (.seq mainLoopProg (.seq finalizeProg closeProg)))) := by
      simp only [mulSProg, seqs]
    rw [hprog]
    exact Ev.seq (ev_of_eval hE1) (Ev.seq (ev_of_eval hE2) (Ev.seq (ev_of_eval hE3)
      (Ev.seq (ev_of_eval hE4) (Ev.seq (ev_of_eval hE5) (ev_of_eval hE6)))))
  obtain ⟨ntot, hEv', hntot⟩ := hEv
  -- length bookkeeping
  have hacc : ((run (a.natAbs.bits) (b.natAbs.bits) []
      (List.replicate (a.natAbs.bits).length false)).1).length = (b.natAbs.bits).length := by
    obtain ⟨h1, -, -⟩ := run_spec (a.natAbs.bits) (b.natAbs.bits) []
      (List.replicate (a.natAbs.bits).length false) (by simp [List.length_replicate])
    rw [h1, List.length_append, List.length_reverse, mbits_length, List.length_nil, Nat.add_zero]
  have hrho : ((run (a.natAbs.bits) (b.natAbs.bits) []
      (List.replicate (a.natAbs.bits).length false)).2).length = (a.natAbs.bits).length := by
    obtain ⟨-, -, h3⟩ := run_spec (a.natAbs.bits) (b.natAbs.bits) []
      (List.replicate (a.natAbs.bits).length false) (by simp [List.length_replicate])
    exact h3
  have hcost : ntot ≤ 1000 * isz a * isz b := by
    have b1 : n1 ≤ 20 := hn1
    have b2 : n2 ≤ 30 * (isz a + isz b + 1) + 60 := by
      rw [vsz_int a, vsz_int b] at hn2; exact hn2
    have b3 : n3 ≤ 14 * (a.natAbs.size + 1) + 14 := by
      rw [Nat.size_eq_bits_len] at hn3; exact hn3
    have b4 : n4 ≤ 200 * (b.natAbs.size + 1) * (a.natAbs.size + 1) + 200 := by
      rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hn4; exact hn4
    have b5 : n5 ≤ 60 * (b.natAbs.size + a.natAbs.size + 1) + 60 := by
      rw [hacc, hrho, Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hn5; exact hn5
    have b6 : n6 ≤ 6 * (a.natAbs.size + 1) + 20 := by
      rw [List.length_map, Nat.size_eq_bits_len] at hn6; exact hn6
    have hia : isz a = a.natAbs.size + 2 := isz_eq a
    have hib : isz b = b.natAbs.size + 2 := isz_eq b
    rw [hia, hib] at b2
    rw [hia, hib]
    nlinarith [hntot, b1, b2, b3, b4, b5, b6]
  refine ⟨Val.int (a * b) :: rest, S6, ntot, ⟨a, b, rest, rfl, rfl⟩, hEv', hcost, ?_, ?_⟩
  · rw [h6_0, h5_0]
    have hF : ofBits (((run (a.natAbs.bits) (b.natAbs.bits) []
          (List.replicate (a.natAbs.bits).length false)).1.reverse
        ++ (run (a.natAbs.bits) (b.natAbs.bits) []
          (List.replicate (a.natAbs.bits).length false)).2)) = a.natAbs * b.natAbs := by
      rw [run_final_val (a.natAbs.bits) b.natAbs, ofBits_bits]
    rw [enc_ofBits_product hF]
    rw [show encs (Val.int (a * b) :: rest) = (Val.int (a * b)).enc ++ encs rest from by
      simp [encs, List.map_cons, List.flatten_cons]]
    rw [List.append_assoc]
  · intro k hk0
    by_cases hmem : k ∈ ({sA, sB, sR, sC, sS, sT, sW, sU} : Finset Stk)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h6A
      · exact h6B
      · exact h6R
      · exact h6C
      · rw [h6fr sS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
        exact h5S
      · exact h6T
      · exact h6W
      · exact h6U
    · have hkA : k ≠ sA := fun h => hmem (by simp [h])
      have hkB : k ≠ sB := fun h => hmem (by simp [h])
      have hkR : k ≠ sR := fun h => hmem (by simp [h])
      have hkC : k ≠ sC := fun h => hmem (by simp [h])
      have hkS : k ≠ sS := fun h => hmem (by simp [h])
      have hkT : k ≠ sT := fun h => hmem (by simp [h])
      have hkW : k ≠ sW := fun h => hmem (by simp [h])
      have hkU : k ≠ sU := fun h => hmem (by simp [h])
      rw [h6fr k hkA hkB hkR hkC hkT hkW hkU, h5fr k hk0 hkR hkC hkS hkT hkU,
        h4fr k hkA hkB hkR hkC hkW hkT, h3fr k hkA hkR hkW,
        h2fr k hk0 hkA hkB hkS hkT hkW, h1fr k hkA hkB hkR hkC hkS hkT hkW hkU]


end Work.IntLib
