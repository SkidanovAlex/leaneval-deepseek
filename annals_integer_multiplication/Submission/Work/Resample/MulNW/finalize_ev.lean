import Mathlib
import Submission.Work.Resample.MulNW.Defs
import Submission.Work.Kernel.Raw
import Submission.Work.IntLib.eval_mvRevOnto
import Submission.Work.IntLib.ofBits_bits
import Submission.Work.Resample.MulNW.finalizeKit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.Resample.MulNW

open HvdH

/-! ## Elementary state lemmas -/

theorem stk_tPush_self (s : State) (k : Stk) (r : Reg) :
    (State.tPush s k r).stk k = s.reg r :: s.stk k := by
  show (s.updStk k (s.reg r :: s.stk k)).stk k = s.reg r :: s.stk k
  rw [State.updStk_same]

theorem stk_tPush_ne (s : State) (k : Stk) (r : Reg) {j : Stk} (hj : j ≠ k) :
    (State.tPush s k r).stk j = s.stk j := by
  show (s.updStk k (s.reg r :: s.stk k)).stk j = s.stk j
  rw [State.updStk_apply, if_neg hj]

theorem stk_tSet (s : State) (r : Reg) (g : Glyph) (j : Stk) :
    (State.tSet s r g).stk j = s.stk j := by
  show (s.updReg r g).stk j = s.stk j
  rw [State.updReg_stk]

theorem reg_tSet (s : State) (r : Reg) (g : Glyph) : (State.tSet s r g).reg r = g := by
  show (s.updReg r g).reg r = g
  rw [State.updReg_apply, if_pos rfl]

theorem stk_tPeek (s : State) (k : Stk) (r : Reg) (j : Stk) :
    (State.tPeek s k r).stk j = s.stk j := rfl

/-! ## The arithmetic facts about the multiplier loop -/

theorem finArith (a b : ℕ) :
    (Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).1
      = (Work.IntLib.MulS.mbits b.size (a * b)).reverse ∧
    ((Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).1).length = b.size ∧
    ((Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).2).length = a.size ∧
    Work.IntLib.ofBits (((Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).1).reverse
      ++ (Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).2) = a * b := by
  have hlen : ((zeros a.size) : List Bool).length = a.bits.length := by
    simp [zeros, Nat.size_eq_bits_len]
  obtain ⟨h1, h2, h3⟩ := Work.IntLib.MulS.run_spec a.bits b.bits [] (zeros a.size) hlen
  have hz : Work.IntLib.ofBits (zeros a.size) = 0 := by
    simp only [zeros]
    exact Work.IntLib.MulS.ofBits_replicate_false a.size
  have h1' : (Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).1
      = (Work.IntLib.MulS.mbits b.size (a * b)).reverse := by
    rw [h1, List.append_nil, hz, Work.IntLib.ofBits_bits, Work.IntLib.ofBits_bits,
      Nat.size_eq_bits_len, Nat.zero_add]
  have hremv : Work.IntLib.ofBits (Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).2
      = a * b / 2 ^ b.size := by
    rw [h2, hz, Work.IntLib.ofBits_bits, Work.IntLib.ofBits_bits, Nat.zero_add,
      Nat.size_eq_bits_len]
  have hof : Work.IntLib.ofBits
      (((Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).1).reverse
        ++ (Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).2) = a * b := by
    have hrev : ((Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).1).reverse
        = (Work.IntLib.MulS.mbits b.size (a * b)).reverse.reverse := by rw [h1']
    rw [hrev, List.reverse_reverse]
    exact Work.IntLib.MulS.finalize_val b.size (a * b) _ hremv
  refine ⟨h1', ?_, ?_, hof⟩
  · rw [h1', List.length_reverse, Work.IntLib.MulS.mbits_length]
  · rw [h3, Nat.size_eq_bits_len]

/-! ## Assembling the value on stack 0 -/

theorem finEncEq (k : ℕ) (rest : List Val) (R : List Glyph) :
    Glyph.pos :: (bitsG k.bits ++ (Glyph.iend :: (encs rest ++ R)))
      = encs (.int ((k : ℕ) : ℤ) :: rest) ++ R := by
  rw [Work.Kernel.encs_cons, Work.IntLib.enc_int, Work.IntLib.encodeNat_eq_bits]
  simp only [Int.natAbs_natCast]
  rw [if_neg (show ¬ (((k : ℕ) : ℤ) < 0) from by omega)]
  simp [bitsG, List.append_assoc]

/-! ## The finalisation phase -/

theorem finalize_ev (main : HvdH.Cmd) (a b : ℕ) (rest : List HvdH.Val) (R : List HvdH.Glyph) : Work.Resample.MulNW.FinalizeSpec main a b rest R := by
  intro ha hb bkS bkR bkC bkT bkW bkU s h0 hS hR hC hW hT hU
  let out : List Bool := (Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).1
  let rem : List Bool := (Work.IntLib.MulS.run a.bits b.bits [] (zeros a.size)).2
  have hR' : s.stk sR = bitsG rem ++ mkR :: bkR := hR
  have hC' : s.stk sC = bitsG out ++ mkC :: bkC := hC
  obtain ⟨houtv, houtlen, hremlen, hofbits⟩ := finArith a b
  have houtlen' : out.length = b.size := houtlen
  have hremlen' : rem.length = a.size := hremlen
  have hofbits' : Work.IntLib.ofBits (out.reverse ++ rem) = a * b := hofbits
  -- length bookkeeping
  have hL1 : (bitsG rem).length = a.size := by simp [bitsG, hremlen']
  have hL2 : ((bitsG rem).reverse).length = a.size := by simp [hL1]
  have hL3 : (bitsG out).length = b.size := by simp [bitsG, houtlen']
  have hL4 : ((bitsG out).reverse ++ bitsG rem).length = a.size + b.size := by
    rw [List.length_append, List.length_reverse, hL1, hL3]
    omega
  have hL5 : ((out.reverse ++ rem).reverse).length = a.size + b.size := by
    rw [List.length_reverse, List.length_append, List.length_reverse, houtlen', hremlen']
    omega
  have hL11 : (bitsG (((a * b).bits).reverse)).length = (a * b).size := by
    simp [bitsG, Nat.size_eq_bits_len]
  have hsz : (a * b).size ≤ a.size + b.size := by
    apply Nat.size_le.mpr
    have ha' : a < 2 ^ a.size := Nat.size_le.mp (le_refl a.size)
    have hb' : b < 2 ^ b.size := Nat.size_le.mp (le_refl b.size)
    calc a * b < 2 ^ a.size * 2 ^ b.size :=
          Nat.mul_lt_mul_of_lt_of_le ha' (le_of_lt hb') (by positivity)
      _ = 2 ^ (a.size + b.size) := by rw [pow_add]
  -- (1) move the remainder bits sR -> sT
  obtain ⟨s1, n1, hev1, hn1, hR1, hT1, hfr1⟩ :=
    Work.IntLib.consume_push_rev main sR mkR sT rL (bitsG rem) bkR (mkT :: bkT)
      (by decide) (fun g hg => bitsG_ne_mk rem 3 g hg) s hR' hT
  have he1 : Work.IntLib.MulS.Ev main (consume sR mkR rL (.push sT rL)) s s1
      (5 * (a.size + 1) + 8) := by
    refine ⟨n1, hev1, ?_⟩
    have h := hn1
    rw [hL1] at h
    omega
  have hU1 : s1.stk sU = mkU :: bkU := by
    rw [hfr1 sU (by decide) (by decide)]
    exact hU
  have hC1 : s1.stk sC = bitsG out ++ mkC :: bkC := by
    rw [hfr1 sC (by decide) (by decide)]
    exact hC'
  -- (2) sT -> sU
  obtain ⟨s2, n2, hev2, hn2, hT2, hU2raw, hfr2⟩ :=
    Work.IntLib.consume_push_rev main sT mkT sU rL ((bitsG rem).reverse) bkT (mkU :: bkU)
      (by decide) (fun g hg => bitsG_ne_mk rem 6 g (List.mem_reverse.mp hg)) s1 hT1 hU1
  have hU2 : s2.stk sU = bitsG rem ++ mkU :: bkU := by rw [hU2raw, List.reverse_reverse]
  have hC2 : s2.stk sC = bitsG out ++ mkC :: bkC := by
    rw [hfr2 sC (by decide) (by decide)]
    exact hC1
  have he2 : Work.IntLib.MulS.Ev main (consume sT mkT rL (.push sU rL)) s1 s2
      (5 * (a.size + 1) + 8) := by
    refine ⟨n2, hev2, ?_⟩
    have h := hn2
    rw [hL2] at h
    omega
  -- (3) sC -> sU
  obtain ⟨s3, n3, hev3, hn3, hC3, hU3raw, hfr3⟩ :=
    Work.IntLib.consume_push_rev main sC mkC sU rL (bitsG out) bkC (bitsG rem ++ mkU :: bkU)
      (by decide) (fun g hg => bitsG_ne_mk out 4 g hg) s2 hC2 hU2
  have hU3 : s3.stk sU = ((bitsG out).reverse ++ bitsG rem) ++ mkU :: bkU := by
    rw [hU3raw, ← List.append_assoc]
  have he3 : Work.IntLib.MulS.Ev main (consume sC mkC rL (.push sU rL)) s2 s3
      (5 * (b.size + 1) + 8) := by
    refine ⟨n3, hev3, ?_⟩
    have h := hn3
    rw [hL3] at h
    omega
  -- (4) sU -> sC
  obtain ⟨s4, n4, hev4, hn4, hU4, hC4raw, hfr4⟩ :=
    Work.IntLib.consume_push_rev main sU mkU sC rL ((bitsG out).reverse ++ bitsG rem) bkU
      (mkC :: bkC)
      (by decide)
      (fun g hg => (List.mem_append.mp hg).elim
        (fun h1 => bitsG_ne_mk out 8 g (List.mem_reverse.mp h1))
        (fun h2 => bitsG_ne_mk rem 8 g h2))
      s3 hU3 hC3
  have hC4 : s4.stk sC = bitsG ((out.reverse ++ rem).reverse) ++ mkC :: bkC := by
    rw [hC4raw, ← bitsG_reverse out, ← bitsG_append, ← bitsG_reverse]
  have he4 : Work.IntLib.MulS.Ev main (consume sU mkU rL (.push sC rL)) s3 s4
      (5 * (a.size + b.size + 1) + 8) := by
    refine ⟨n4, hev4, ?_⟩
    have h := hn4
    rw [hL4] at h
    omega
  -- (5) strip the leading zero glyphs
  obtain ⟨s5, n5, hev5, hn5, hC5raw, hfr5⟩ :=
    Work.IntLib.eval_stripZeros main sC mkC rTmp ((out.reverse ++ rem).reverse) bkC s4
      (by decide) (fun bb => by intro hh; cases hh) hC4
  have hC5 : s5.stk sC = bitsG (((a * b).bits).reverse) ++ mkC :: bkC := by
    rw [hC5raw, bitsG_dropWhile, hofbits']
  have he5 : Work.IntLib.MulS.Ev main stripProg s4 s5 (2 * (a.size + b.size + 1) + 6) := by
    refine ⟨n5, hev5, ?_⟩
    have h := hn5
    rw [hL5] at h
    omega
  have h05 : s5.stk 0 = encs rest ++ R := by
    rw [hfr5 0 (by decide), hfr4 0 (by decide) (by decide), hfr3 0 (by decide) (by decide),
      hfr2 0 (by decide) (by decide), hfr1 0 (by decide) (by decide)]
    exact h0
  -- (6) set the terminator register
  let s6 : State := State.tSet s5 rIe Glyph.iend
  have hev6 : Eval main (.set rIe Glyph.iend) s5 s6 1 := Work.Kernel.eval_set main rIe Glyph.iend s5
  have he6 : Work.IntLib.MulS.Ev main (.set rIe Glyph.iend) s5 s6 1 := ⟨1, hev6, le_rfl⟩
  -- (7) push the terminator
  let s7 : State := State.tPush s6 0 rIe
  have hev7 : Eval main (.push 0 rIe) s6 s7 1 := Work.Kernel.eval_push main 0 rIe s6
  have he7 : Work.IntLib.MulS.Ev main (.push 0 rIe) s6 s7 1 := ⟨1, hev7, le_rfl⟩
  have h07 : s7.stk 0 = Glyph.iend :: (encs rest ++ R) := by
    show (State.tPush s6 0 rIe).stk 0 = Glyph.iend :: (encs rest ++ R)
    rw [show (State.tPush s6 0 rIe).stk 0 = s6.reg rIe :: s6.stk 0 from
      stk_tPush_self s6 0 rIe]
    have hreg : s6.reg rIe = Glyph.iend := by
      show (State.tSet s5 rIe Glyph.iend).reg rIe = Glyph.iend
      exact reg_tSet s5 rIe Glyph.iend
    have hstk : s6.stk 0 = encs rest ++ R := by
      show (State.tSet s5 rIe Glyph.iend).stk 0 = encs rest ++ R
      rw [stk_tSet]
      exact h05
    rw [hreg, hstk]
  -- (8) the sign of the product
  have hS7 : s7.stk sS = Glyph.pos :: Glyph.pos :: mkS :: bkS := by
    rw [show s7.stk sS = s6.stk sS from stk_tPush_ne s6 0 rIe (by decide : sS ≠ (0 : Stk)),
      show s6.stk sS = s5.stk sS from stk_tSet s5 rIe Glyph.iend sS,
      hfr5 sS (by decide), hfr4 sS (by decide) (by decide), hfr3 sS (by decide) (by decide),
      hfr2 sS (by decide) (by decide), hfr1 sS (by decide) (by decide)]
    exact hS
  obtain ⟨s8, n8, hev8, hn8, hS8, hr8, hfr8⟩ := sgnProg_spec main bkS s7 hS7
  have he8 : Work.IntLib.MulS.Ev main sgnProg s7 s8 8 := ⟨n8, hev8, by omega⟩
  -- (9) look at the top of sC
  let s9 : State := State.tPeek s8 sC rTmp
  have hev9 : Eval main (.peek sC rTmp) s8 s9 1 := Work.Kernel.eval_peek main sC rTmp s8
  have he9 : Work.IntLib.MulS.Ev main (.peek sC rTmp) s8 s9 1 := ⟨1, hev9, le_rfl⟩
  have hC9 : s9.stk sC = bitsG (((a * b).bits).reverse) ++ mkC :: bkC := by
    rw [show s9.stk sC = s8.stk sC from stk_tPeek s8 sC rTmp sC,
      hfr8 sC (by decide),
      show s7.stk sC = s6.stk sC from stk_tPush_ne s6 0 rIe (by decide : sC ≠ (0 : Stk)),
      show s6.stk sC = s5.stk sC from stk_tSet s5 rIe Glyph.iend sC]
    exact hC5
  have h09 : s9.stk 0 = Glyph.iend :: (encs rest ++ R) := by
    rw [show s9.stk 0 = s8.stk 0 from stk_tPeek s8 sC rTmp 0, hfr8 0 (by decide)]
    exact h07
  -- (10) the "is the product zero" test (the sign is overwritten in (12) anyway)
  have hc10 : ∃ (s10 : State),
      Work.IntLib.MulS.Ev main (.ite rTmp (Glyph.bit false) (.set rSign Glyph.pos) .skip)
        s9 s10 2 ∧ s10.stk = s9.stk := by
    by_cases hb : s9.reg rTmp = Glyph.bit false
    · refine ⟨State.tSet s9 rSign Glyph.pos, ?_, ?_⟩
      · exact Work.IntLib.MulS.Ev.iteT hb
          ⟨1, Work.Kernel.eval_set main rSign Glyph.pos s9, le_rfl⟩
      · funext j
        exact stk_tSet s9 rSign Glyph.pos j
    · exact ⟨s9, Work.IntLib.MulS.Ev.iteF hb
          ⟨1, Work.Kernel.eval_skip main s9, le_rfl⟩, rfl⟩
  obtain ⟨s10, hev10, h10stk⟩ := hc10
  have hC10 : s10.stk sC = bitsG (((a * b).bits).reverse) ++ mkC :: bkC := by
    rw [h10stk]
    exact hC9
  have h010 : s10.stk 0 = Glyph.iend :: (encs rest ++ R) := by
    rw [h10stk]
    exact h09
  -- (11) move the assembled magnitude onto stack 0
  obtain ⟨s11, n11, hev11, hn11, hC11, h011raw, hfr11⟩ :=
    Work.IntLib.consume_push_rev main sC mkC 0 rL (bitsG (((a * b).bits).reverse)) bkC
      (Glyph.iend :: (encs rest ++ R))
      (by decide) (fun g hg => bitsG_ne_mk (((a * b).bits).reverse) 4 g hg) s10 hC10 h010
  have he11 : Work.IntLib.MulS.Ev main (consume sC mkC rL (.push 0 rL)) s10 s11
      (5 * ((a * b).size + 1) + 8) := by
    refine ⟨n11, hev11, ?_⟩
    have h := hn11
    rw [hL11] at h
    omega
  -- (12) the sign is positive
  let s12 : State := State.tSet s11 rSign Glyph.pos
  have hev12 : Eval main (.set rSign Glyph.pos) s11 s12 1 :=
    Work.Kernel.eval_set main rSign Glyph.pos s11
  have he12 : Work.IntLib.MulS.Ev main (.set rSign Glyph.pos) s11 s12 1 := ⟨1, hev12, le_rfl⟩
  -- (13) push the sign
  let s13 : State := State.tPush s12 0 rSign
  have hev13 : Eval main (.push 0 rSign) s12 s13 1 := Work.Kernel.eval_push main 0 rSign s12
  have he13 : Work.IntLib.MulS.Ev main (.push 0 rSign) s12 s13 1 := ⟨1, hev13, le_rfl⟩
  -- assemble the program
  have T13 : Work.IntLib.MulS.Ev main (Work.IntLib.MulS.seqs [.push 0 rSign]) s12 s13 1 := he13
  have T12 := Work.IntLib.MulS.Ev.seq he12 T13
  have T11 := Work.IntLib.MulS.Ev.seq he11 T12
  have T10 := Work.IntLib.MulS.Ev.seq hev10 T11
  have T9 := Work.IntLib.MulS.Ev.seq he9 T10
  have T8 := Work.IntLib.MulS.Ev.seq he8 T9
  have T7 := Work.IntLib.MulS.Ev.seq he7 T8
  have T6 := Work.IntLib.MulS.Ev.seq he6 T7
  have T5 := Work.IntLib.MulS.Ev.seq he5 T6
  have T4 := Work.IntLib.MulS.Ev.seq he4 T5
  have T3 := Work.IntLib.MulS.Ev.seq he3 T4
  have T2 := Work.IntLib.MulS.Ev.seq he2 T3
  have T1 := Work.IntLib.MulS.Ev.seq he1 T2
  have hfinal : Work.IntLib.MulS.Ev main finalizeProg s s13 (60 * (a.size + b.size + 4)) :=
    T1.mono (by omega)
  obtain ⟨ntot, hevAll, hntot⟩ := hfinal
  -- frame facts via the suffix programs
  obtain ⟨_, hevT2, _⟩ := T2
  obtain ⟨_, hevT3, _⟩ := T3
  obtain ⟨_, hevT5, _⟩ := T5
  obtain ⟨_, hevT9, _⟩ := T9
  obtain ⟨_, hevT12, _⟩ := T12
  have hR13 : s13.stk sR = mkR :: bkR := by
    rw [Work.IntLib.MulS.Eval.stk_frame hevT2 (k := sR) (by decide)]
    exact hR1
  have hT13 : s13.stk sT = mkT :: bkT := by
    rw [Work.IntLib.MulS.Eval.stk_frame hevT3 (k := sT) (by decide)]
    exact hT2
  have hU13 : s13.stk sU = mkU :: bkU := by
    rw [Work.IntLib.MulS.Eval.stk_frame hevT5 (k := sU) (by decide)]
    exact hU4
  have hC13 : s13.stk sC = mkC :: bkC := by
    rw [Work.IntLib.MulS.Eval.stk_frame hevT12 (k := sC) (by decide)]
    exact hC11
  have hS13 : s13.stk sS = bkS := by
    rw [Work.IntLib.MulS.Eval.stk_frame hevT9 (k := sS) (by decide)]
    exact hS8
  have hW13 : s13.stk sW = mkW :: bkW := by
    rw [Work.IntLib.MulS.Eval.stk_frame hevAll (k := sW) (by decide)]
    exact hW
  have hS0 : s13.stk 0 = encs (.int ((a * b : ℕ) : ℤ) :: rest) ++ R := by
    have e1 : s13.stk 0 = Glyph.pos :: s11.stk 0 := by
      rw [show s13.stk 0 = s12.reg rSign :: s12.stk 0 from stk_tPush_self s12 0 rSign,
        show s12.stk 0 = s11.stk 0 from stk_tSet s11 rSign Glyph.pos 0,
        reg_tSet s11 rSign Glyph.pos]
    rw [e1, h011raw, ← bitsG_reverse, List.reverse_reverse]
    exact finEncEq (a * b) rest R
  have hsub : Work.IntLib.MulS.cmdTouches finalizeProg ⊆
      ({0, sR, sC, sS, sT, sW, sU} : Finset Stk) := by decide
  refine ⟨s13, ntot, ?_, hntot, hS0, hS13, hR13, hC13, hT13, hW13, hU13, ?_⟩
  · exact hevAll
  · intro j hj
    exact Work.IntLib.MulS.Eval.stk_frame hevAll (fun hc => hj (hsub hc))

end Work.Resample.MulNW
