import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pb2Defs
import Submission.Work.Resample.pb2eDefs
import Submission.Work.Resample.pb2eBrFacts
import Submission.Work.Resample.pb2ECostBd
import Submission.Work.Resample.paWords
import Submission.Work.Resample.pbW6f
import Submission.Work.Resample.paBasic
import Submission.Work.Resample.pbRndDefs
import Submission.Work.Resample.paTabSz

/-! Guidance from the project lead (the requester):

LEAD (endgame: Resample's B half is the LAST open piece of the whole problem — speed matters). This statement is the
MIRROR of the already PROVED `Work.Resample.paStageE` (Submission/Work/Resample/). Start by COPYING that file's proof and
adapting it; do not design anything new. Mirror dictionary (definitions in Submission/Work/Resample/pb2Defs.lean):
PAVec/PAInv/PAMid/PABr/PAIterBrF ↦ PB2Vec/PB2Inv/PB2Mid/PB2Br/PB2IterBrF; the array flows from shape ts (input,
ts.prod entries) to shape ss (output); list iteration is `axisIter ts ss Φ` with Φ j : (Fin t_j → ℤ×ℤ) → (Fin s_j → ℤ×ℤ);
applyAlong arguments per axis j are A = (ss.take j).prod, m = t_j, n = s_j, B = (ts.drop (j+1)).prod; stack 2 holds the
remaining INPUT dims (ts.drop j), stack 3 the remaining OUTPUT dims (ss.drop j), stack 6 (ss.take j).prod, stack 7 s_j;
SliceSpecAtA Kb p α s t prep q Φ P ↦ SliceSpecAt prep q Kb p α s t Φ P (argument order differs; its q cost has the extra
Kb(t+1)(p+1)² term, already in PB2Br); resAop/rA ↦ resBop/rB. Size bounds keep ts.prod (sᵢ < tᵢ, so every intermediate
array has ≤ ts.prod entries: (ss.take j).prod ≤ (ts.take j).prod). NEVER import pbSetupF, pbRoundF, pbIterGo*, pbIterF*
(obsolete route; pbSetupF needs 17 GB). Split into children only where the A-side proof was split.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-- The body of `Work.Resample.pb2StageE`: the mirror of the proof of `Work.Resample.paStageE`,
with the aggregate cost bound `pb2ECostBd` (proved separately in
`Submission/Work/Resample/pb2ECostBd.lean`) passed in as a hypothesis. -/
private theorem pb2EStageCore
    (hCostBd : ∀ (K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f
        Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) (arr : Val),
      ResParams p α ss ts → j < D → vsz arr ≤ ts.prod * (2 * p + 8) + ts.prod + 1 →
        pb2ECost K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f Kb
          Cm p α ss ts j arr ≤
          pb2EKc K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f Kb *
            PB2Br Kb Cm p α ss ts j)
    (Kb : ℕ) (prep q : Cmd) :
    ∃ (stage : Cmd) (Kc : ℕ),
      ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ)
        (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
        (zs0 : List (ℤ × ℤ)) (Pj : List Val),
      ResParams p α ss ts → Monotone Cm → MulBelow main N Cm → Kc * p < N → Kb * p < N →
      j < D →
      SliceSpecAt prep q Kb p α (ss.getD j 0) (ts.getD j 0) (Φ j) Pj →
      WordP main stage
        (fun vs rest a => PB2Inv p α ss ts Φ zs0 j vs rest a)
        (fun vs rest a out b => PB2Mid Kb p α ss ts Φ zs0 j Pj out rest b)
        (fun _ _ _ => Kc * PB2Br Kb Cm p α ss ts j) := by
  obtain ⟨park1, K1, hPark1⟩ := paW2 1 (by decide)
  obtain ⟨peel3, K5a, hPeel3⟩ := paW5 3 (by decide)
  obtain ⟨mv7, K7, hmv7⟩ := paW2 7 (by decide)
  obtain ⟨peel2, K5b, hPeel2⟩ := paW5 2 (by decide)
  obtain ⟨mv11, K11, hmv11⟩ := paW2 11 (by decide)
  obtain ⟨push1, Kpv, hPush1⟩ := Work.Kernel.kernelLib_pushVal
  obtain ⟨prod6, K6, hProd6⟩ := pbW6f
  obtain ⟨mv10, Kn10, hmv10⟩ := paW2 10 (by decide)
  obtain ⟨cp11, Kc4b, hCp11⟩ := paW4 11 (by decide)
  obtain ⟨cp7, Kc4a, hCp7⟩ := paW4 7 (by decide)
  obtain ⟨cp4, Kc4c, hCp4⟩ := paW4 4 (by decide)
  obtain ⟨cp5, Kc4d, hCp5⟩ := paW4 5 (by decide)
  obtain ⟨unpark1, Ku1, hUnpark1⟩ := paW1 1 (by decide)
  obtain ⟨mvB10, Kb10, hmvB10⟩ := paW1 10 (by decide)
  obtain ⟨cp7b, Kc4e, hCp7b⟩ := paW4 7 (by decide)
  obtain ⟨mv11b, Kb11, hmv11b⟩ := paW1 11 (by decide)
  obtain ⟨cp6, Kc4f, hCp6⟩ := paW4 6 (by decide)
  have hCost := hCostBd K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11
    Kc4f Kb
  refine ⟨Cmd.seq park1 (Cmd.seq peel3 (Cmd.seq mv7 (Cmd.seq peel2 (Cmd.seq mv11 (Cmd.seq (push1 (Val.int
  1)) (Cmd.seq prod6 (Cmd.seq mv10 (Cmd.seq cp11 (Cmd.seq cp7 (Cmd.seq cp4 (Cmd.seq cp5 (Cmd.seq
  prep (Cmd.seq unpark1 (Cmd.seq mvB10 (Cmd.seq cp7b (Cmd.seq mv11b (cp6))))))))))))))))),
    pb2EKc K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f Kb, ?_⟩
  intro main N Cm p α ss ts j Φ zs0 Pj hRes hMon hMul hKN hKbN hjD hSlice
  intro vs rest a hPre s R0 Bg h0 hk
  obtain ⟨arr, hVec, hvs, hp1, hp2, hp3, hp4, hp5, hp6, hpRest⟩ := hPre
  have hp7 : a 7 = [] := hpRest 7 (by decide) (by decide)
  obtain ⟨harr, hlen0, hdisc0, hsz0⟩ := hVec
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := hRes
  have hRes' : ResParams p α ss ts := ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩
  have hjts : j < ts.length := by rw [htslen]; exact hjD
  have hjss : j < ss.length := by rw [hsslen]; exact hjD
  have hKbpN : Kb * p < N := hKbN
  have hKb1 : 1 ≤ Kb := by
    rcases Nat.eq_zero_or_pos Kb with h0' | h0'
    · exact (pb2EKb0False h0' hSlice main N Cm hMon hMul hKbpN).elim
    · exact h0'
  have hstj : ss.getD j 0 < ts.getD j 0 := (hdim j hjD).2.1
  have hs2 : 2 ≤ ss.getD j 0 := (hdim j hjD).1
  have h3split : intList (ss.drop j) =
      Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1))) :=
    pa_intList_drop_cons hjss
  have h2split : intList (ts.drop j) =
      Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1))) :=
    pa_intList_drop_cons hjts
  have hts_ge : ∀ x ∈ ts.drop (j + 1), 2 ≤ x := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    rw [← hix, ← List.getD_eq_getElem (ts.drop (j + 1)) 0 hi]
    rw [pa_getD_drop ts (j + 1) i (by simpa using hi)]
    have hi2 : i < (ts.drop (j + 1)).length := hi
    rw [List.length_drop, htslen] at hi2
    have h1 := (hdim (i + (j + 1)) (by omega)).1
    have h2 := (hdim (i + (j + 1)) (by omega)).2.1
    omega
  -- ## phase 1: park the array on stack 1
  obtain ⟨vs1, a1, s1, n1, ⟨hv1, e1⟩, hev1, hc1, h01, hk1⟩ :=
    hPark1 main arr [] (a 1) vs a ⟨by simp [hvs], rfl⟩ s (paMark :: (encs rest ++ R0)) Bg h0 hk
  -- ## phase 2: peel `s_j` off stack 3
  have h2a : a1 3 = Val.cons (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1))) :: [] := by
    rw [e1, Function.update_of_ne (by decide : (3 : Stk) ≠ 1), hp3, h3split]
  obtain ⟨vs2, a2, s2, n2, ⟨hv2, e2⟩, hev2, hc2, h02, hk2⟩ :=
    hPeel3 main (Val.int (ss.getD j 0 : ℤ)) (intList (ss.drop (j + 1))) [] [] vs1 a1 ⟨hv1, h2a⟩ s1 (paMark :: (encs rest ++ R0)) Bg h01 hk1
  -- ## phase 3: stash `s_j` on stack 7
  have h3a : a2 7 = [] := by
    rw [e2, Function.update_of_ne (by decide : (7 : Stk) ≠ 3), e1, Function.update_of_ne (by
      decide : (7 : Stk) ≠ 1), hp7]
  obtain ⟨vs3, a3, s3, n3, ⟨hv3, e3⟩, hev3, hc3, h03, hk3⟩ :=
    hmv7 main (Val.int (ss.getD j 0 : ℤ)) [] [] vs2 a2 ⟨by rw [hv2, hv1], h3a⟩ s2 (paMark :: (encs rest ++ R0)) Bg h02 hk2
  -- ## phase 4: peel `t_j` off stack 2
  have h4a : a3 2 = Val.cons (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1))) :: [] := by
    rw [e3, Function.update_of_ne (by decide : (2 : Stk) ≠ 7), e2, Function.update_of_ne (by
      decide : (2 : Stk) ≠ 3), e1, Function.update_of_ne (by decide : (2 : Stk) ≠ 1), hp2,
      h2split]
  obtain ⟨vs4, a4, s4, n4, ⟨hv4, e4⟩, hev4, hc4, h04, hk4⟩ :=
    hPeel2 main (Val.int (ts.getD j 0 : ℤ)) (intList (ts.drop (j + 1))) [] [] vs3 a3 ⟨hv3, h4a⟩ s3 (paMark :: (encs rest ++ R0)) Bg h03 hk3
  -- ## phase 5: stash `t_j` on stack 11
  have h5a : a4 11 = [] := by
    rw [e4, Function.update_of_ne (by decide : (11 : Stk) ≠ 2), e3, Function.update_of_ne (by
      decide : (11 : Stk) ≠ 7), e2, Function.update_of_ne (by decide : (11 : Stk) ≠ 3), e1,
      Function.update_of_ne (by decide : (11 : Stk) ≠ 1), hpRest 11 (by decide) (by decide)]
  obtain ⟨vs5, a5, s5, n5, ⟨hv5, e5⟩, hev5, hc5, h05, hk5⟩ :=
    hmv11 main (Val.int (ts.getD j 0 : ℤ)) [] [] vs4 a4 ⟨by rw [hv4, hv3], h5a⟩ s4 (paMark :: (encs rest ++ R0)) Bg h04 hk4
  -- ## phase 6: push `int 1`
  obtain ⟨vs6, s6, n6, hpost6, hev6, hc6, h06, hk6⟩ :=
    hPush1 main (Val.int 1) vs5 trivial s5 (paMark :: (encs rest ++ R0)) h05
  have hv6 : vs6 = Val.int 1 :: [] := by rw [hpost6, hv5]
  have hk6' : ∀ k : Stk, k ≠ 0 → s6.stk k = encs (a5 k) ++ Bg k := by
    intro k hk0; rw [hk6 k hk0]; exact hk5 k hk0
  -- ## phase 7: multiply `ts.drop (j+1)` into the accumulator
  have h7a : a5 2 = intList (ts.drop (j + 1)) :: [] := by
    rw [e5, Function.update_of_ne (by decide : (2 : Stk) ≠ 11), e4, Function.update_self]
  obtain ⟨vs7, a6, s7, n7, ⟨hv7, e6⟩, hev7, hc7, h07, hk7⟩ :=
    hProd6 main (ts.drop (j + 1)) [] [] hts_ge vs6 a5 ⟨hv6, h7a⟩ s6 (paMark :: (encs rest ++ R0)) Bg h06 hk6'
  -- ## phase 8: stash `B_j` on stack 10
  have h8a : a6 10 = [] := by
    rw [e6, e5, Function.update_of_ne (by decide : (10 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (10 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (10 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (10 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (10 : Stk) ≠ 1), hpRest 10 (by decide) (by decide)]
  obtain ⟨vs8, a7, s8, n8, ⟨hv8, e7⟩, hev8, hc8, h08, hk8⟩ :=
    hmv10 main (Val.int ((ts.drop (j + 1)).prod)) [] [] vs7 a6 ⟨hv7, h8a⟩ s7 (paMark :: (encs rest ++ R0)) Bg h07 hk7
  -- ## phase 9: copy `t_j` from stack 11 onto the value stack
  have h9a : a7 11 = [Val.int (ts.getD j 0 : ℤ)] := by
    rw [e7, Function.update_of_ne (by decide : (11 : Stk) ≠ 10), e6, e5, Function.update_self]
  obtain ⟨vs9, a8, s9, n9, ⟨hv9, e8⟩, hev9, hc9, h09, hk9⟩ :=
    hCp11 main (Val.int (ts.getD j 0 : ℤ)) vs8 vs8 a7 ⟨rfl, h9a⟩ s8 (paMark :: (encs rest ++ R0)) Bg h08 hk8
  -- ## phase 10: copy `s_j` from stack 7 onto the value stack
  have h10a : a8 7 = [Val.int (ss.getD j 0 : ℤ)] := by
    rw [e8, e7, Function.update_of_ne (by decide : (7 : Stk) ≠ 10), e6, e5, Function.update_of_ne
      (by decide : (7 : Stk) ≠ 11), e4, Function.update_of_ne (by decide : (7 : Stk) ≠ 2), e3,
      Function.update_self]
  obtain ⟨vs10, a9, s10, n10, ⟨hv10, e9⟩, hev10, hc10, h010, hk10⟩ :=
    hCp7 main (Val.int (ss.getD j 0 : ℤ)) vs9 vs9 a8 ⟨rfl, h10a⟩ s9 (paMark :: (encs rest ++ R0)) Bg h09 hk9
  -- ## phase 11: copy `α` onto the value stack
  have h11a : a9 4 = [Val.int α] := by
    rw [e9, e8, e7, Function.update_of_ne (by decide : (4 : Stk) ≠ 10), e6, e5,
      Function.update_of_ne (by decide : (4 : Stk) ≠ 11), e4, Function.update_of_ne (by decide :
      (4 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (4 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (4 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (4 : Stk) ≠ 1), hp4]
  obtain ⟨vs11, a10, s11, n11, ⟨hv11, e10⟩, hev11, hc11, h011, hk11⟩ :=
    hCp4 main (Val.int α) vs10 vs10 a9 ⟨rfl, h11a⟩ s10 (paMark :: (encs rest ++ R0)) Bg h010 hk10
  -- ## phase 12: copy `p` onto the value stack
  have h12a : a10 5 = [Val.int p] := by
    rw [e10, e9, e8, e7, Function.update_of_ne (by decide : (5 : Stk) ≠ 10), e6, e5,
      Function.update_of_ne (by decide : (5 : Stk) ≠ 11), e4, Function.update_of_ne (by decide :
      (5 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (5 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (5 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (5 : Stk) ≠ 1), hp5]
  obtain ⟨vs12, a11, s12, n12, ⟨hv12, e11⟩, hev12, hc12, h012, hk12⟩ :=
    hCp5 main (Val.int p) vs11 vs11 a10 ⟨rfl, h12a⟩ s11 (paMark :: (encs rest ++ R0)) Bg h011 hk11
  -- ## phase 13: `prep`
  have hv12' : vs12 = Val.int p :: Val.int α :: Val.int (ss.getD j 0) ::
      Val.int (ts.getD j 0) :: [] := by
    rw [hv12, hv11, hv10, hv9, hv8]
  obtain ⟨out13, s13, n13, hpost13, hev13, hc13, h013, hk13⟩ :=
    (hSlice.1 main N Cm hMon hMul hKbpN) vs12 ⟨[], by rw [hv12']⟩ s12
      (paMark :: (encs rest ++ R0)) h012
  obtain ⟨rest13, hvs13, hout13⟩ := hpost13
  have hrest13 : rest13 = [] := by
    have hlen : vs12.length = (Val.int p :: Val.int α :: Val.int (ss.getD j 0) ::
        Val.int (ts.getD j 0) :: rest13).length := congrArg List.length hvs13
    rw [hv12'] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    have h0 : rest13.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero h0
  have hout13' : out13 = Pj := by rw [hout13, hrest13, List.append_nil]
  have hk13' : ∀ k : Stk, k ≠ 0 → s13.stk k = encs (a11 k) ++ Bg k := by
    intro k hk0; rw [hk13 k hk0]; exact hk12 k hk0
  -- ## phase 14: unpark the array on top of the table
  have h14a : a11 1 = [arr] := by
    rw [e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (1 : Stk) ≠ 10), e6, e5,
      Function.update_of_ne (by decide : (1 : Stk) ≠ 11), e4, Function.update_of_ne (by decide :
      (1 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (1 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (1 : Stk) ≠ 3), e1, Function.update_self, hp1]
  obtain ⟨vs14, a12, s14, n14, ⟨hv14, e12⟩, hev14, hc14, h014, hk14⟩ :=
    hUnpark1 main arr Pj out13 a11 ⟨hout13', h14a⟩ s13 (paMark :: (encs rest ++ R0)) Bg h013 hk13'
  -- ## phase 15: move `B_j` from stack 10 to the value stack
  have h15a : a12 10 = [Val.int ((ts.drop (j + 1)).prod)] := by
    rw [e12, Function.update_of_ne (by decide : (10 : Stk) ≠ 1), e11, e10, e9, e8, e7,
      Function.update_self]
  obtain ⟨vs15, a13, s15, n15, ⟨hv15, e13⟩, hev15, hc15, h015, hk15⟩ :=
    hmvB10 main (Val.int ((ts.drop (j + 1)).prod)) vs14 vs14 a12 ⟨rfl, h15a⟩ s14 (paMark :: (encs rest ++ R0)) Bg h014 hk14
  -- ## phase 16: copy `s_j` onto the value stack
  have h16a : a13 7 = [Val.int (ss.getD j 0 : ℤ)] := by
    rw [e13, Function.update_of_ne (by decide : (7 : Stk) ≠ 10), e12, Function.update_of_ne (by
      decide : (7 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (7 :
      Stk) ≠ 10), e6, e5, Function.update_of_ne (by decide : (7 : Stk) ≠ 11), e4,
      Function.update_of_ne (by decide : (7 : Stk) ≠ 2), e3, Function.update_self]
  obtain ⟨vs16, a14, s16, n16, ⟨hv16, e14⟩, hev16, hc16, h016, hk16⟩ :=
    hCp7b main (Val.int (ss.getD j 0 : ℤ)) vs15 vs15 a13 ⟨rfl, h16a⟩ s15 (paMark :: (encs rest ++ R0)) Bg h015 hk15
  -- ## phase 17: move `t_j` from stack 11 to the value stack
  have h17a : a14 11 = [Val.int (ts.getD j 0 : ℤ)] := by
    rw [e14, e13, Function.update_of_ne (by decide : (11 : Stk) ≠ 10), e12,
      Function.update_of_ne (by decide : (11 : Stk) ≠ 1), e11, e10, e9, e8, e7,
      Function.update_of_ne (by decide : (11 : Stk) ≠ 10), e6, e5, Function.update_self]
  obtain ⟨vs17, a15, s17, n17, ⟨hv17, e15⟩, hev17, hc17, h017, hk17⟩ :=
    hmv11b main (Val.int (ts.getD j 0 : ℤ)) vs16 vs16 a14 ⟨rfl, h17a⟩ s16 (paMark :: (encs rest ++ R0)) Bg h016 hk16
  -- ## phase 18: copy `A_j` onto the value stack
  have h18a : a15 6 = [Val.int ((ss.take j).prod)] := by
    rw [e15, Function.update_of_ne (by decide : (6 : Stk) ≠ 11), e14, e13, Function.update_of_ne
      (by decide : (6 : Stk) ≠ 10), e12, Function.update_of_ne (by decide : (6 : Stk) ≠ 1), e11,
      e10, e9, e8, e7, Function.update_of_ne (by decide : (6 : Stk) ≠ 10), e6, e5,
      Function.update_of_ne (by decide : (6 : Stk) ≠ 11), e4, Function.update_of_ne (by decide :
      (6 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (6 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (6 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (6 : Stk) ≠ 1), hp6]
  obtain ⟨vs18, a16, s18, n18, ⟨hv18, e16⟩, hev18, hc18, h018, hk18⟩ :=
    hCp6 main (Val.int ((ss.take j).prod)) vs17 vs17 a15 ⟨rfl, h18a⟩ s17 (paMark :: (encs rest ++ R0)) Bg h017 hk17
  -- ## the final value list
  have hvs18' : vs18 = Val.int ((ss.take j).prod) :: Val.int (ts.getD j 0 : ℤ) ::
      Val.int (ss.getD j 0 : ℤ) :: Val.int ((ts.drop (j + 1)).prod) :: arr :: Pj := by
    rw [hv18, hv17, hv16, hv15, hv14, hout13']
  -- ## the table size bound
  have hPjsum : (Pj.map vsz).sum ≤ 8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) :=
    paTabSz hSlice.1 main N Cm hMon hMul hKbpN hKb1 hp100 hα2 hαp hs2 hstj
  -- ## the components of the final stack description
  have ha1F : a16 1 = [] := by
    rw [e16, e15, Function.update_of_ne (by decide : (1 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (1 : Stk) ≠ 10), e12, Function.update_self]
  have ha2F : a16 2 = [intList (ts.drop (j + 1))] := by
    rw [e16, e15, Function.update_of_ne (by decide : (2 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (2 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (2 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (2 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (2 : Stk) ≠ 11), e4, Function.update_self]
  have ha3F : a16 3 = [intList (ss.drop (j + 1))] := by
    rw [e16, e15, Function.update_of_ne (by decide : (3 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (3 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (3 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (3 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (3 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (3 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (3 : Stk) ≠ 7), e2,
      Function.update_self]
  have ha4F : a16 4 = [Val.int α] := by
    rw [e16, e15, Function.update_of_ne (by decide : (4 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (4 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (4 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (4 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (4 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (4 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (4 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (4 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (4 : Stk) ≠ 1), hp4]
  have ha5F : a16 5 = [Val.int p] := by
    rw [e16, e15, Function.update_of_ne (by decide : (5 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (5 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (5 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (5 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (5 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (5 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (5 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (5 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (5 : Stk) ≠ 1), hp5]
  have ha6F : a16 6 = [Val.int ((ss.take j).prod)] := by
    rw [e16, e15, Function.update_of_ne (by decide : (6 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (6 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (6 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (6 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (6 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (6 : Stk) ≠ 2), e3, Function.update_of_ne (by decide : (6 : Stk) ≠ 7), e2,
      Function.update_of_ne (by decide : (6 : Stk) ≠ 3), e1, Function.update_of_ne (by decide :
      (6 : Stk) ≠ 1), hp6]
  have ha7F : a16 7 = [Val.int (ss.getD j 0 : ℤ)] := by
    rw [e16, e15, Function.update_of_ne (by decide : (7 : Stk) ≠ 11), e14, e13,
      Function.update_of_ne (by decide : (7 : Stk) ≠ 10), e12, Function.update_of_ne (by decide
      : (7 : Stk) ≠ 1), e11, e10, e9, e8, e7, Function.update_of_ne (by decide : (7 : Stk) ≠
      10), e6, e5, Function.update_of_ne (by decide : (7 : Stk) ≠ 11), e4, Function.update_of_ne
      (by decide : (7 : Stk) ≠ 2), e3, Function.update_self]
  have haRestF : ∀ k : Stk, k ≠ 0 → (k : ℕ) ∉ ({2, 3, 4, 5, 6, 7} : Finset ℕ) →
      a16 k = [] := by
    intro k hk0 hkF
    have hkF6 : (k : ℕ) ∉ ({2, 3, 4, 5, 6} : Finset ℕ) := by
      intro h
      exact hkF (by simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; tauto)
    have hk2 : k ≠ 2 := by intro h; exact hkF (by rw [h]; decide)
    have hk3 : k ≠ 3 := by intro h; exact hkF (by rw [h]; decide)
    have hk7 : k ≠ 7 := by intro h; exact hkF (by rw [h]; decide)
    by_cases hk1 : k = 1
    · rw [hk1]; exact ha1F
    by_cases hk10 : k = 10
    · rw [hk10, e16, e15, Function.update_of_ne (by decide : (10 : Stk) ≠ 11), e14, e13,
        Function.update_self]
    by_cases hk11 : k = 11
    · rw [hk11, e16, e15, Function.update_self]
    rw [e16, e15, Function.update_of_ne hk11, e14, e13, Function.update_of_ne hk10, e12,
      Function.update_of_ne hk1, e11, e10, e9, e8, e7, Function.update_of_ne hk10, e6, e5,
      Function.update_of_ne hk11, e4, Function.update_of_ne hk2, e3, Function.update_of_ne hk7,
      e2, Function.update_of_ne hk3, e1, Function.update_of_ne hk1, hpRest k hk0 hkF6]
  -- ## assembly
  refine ⟨vs18, a16, s18, n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + (n12 + (n13 + (n14 + (n15 +
  (n16 + (n17 + (n18))))))))))))))))), ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨arr, ⟨harr, hlen0, hdisc0, hsz0⟩, hvs18', hPjsum, ha1F, ha2F, ha3F, ha4F, ha5F, ha6F, ha7F, haRestF⟩
  · exact Eval.seq hev1 (Eval.seq hev2 (Eval.seq hev3 (Eval.seq hev4 (Eval.seq hev5 (Eval.seq hev6
  (Eval.seq hev7 (Eval.seq hev8 (Eval.seq hev9 (Eval.seq hev10 (Eval.seq hev11 (Eval.seq hev12
  (Eval.seq hev13 (Eval.seq hev14 (Eval.seq hev15 (Eval.seq hev16 (Eval.seq hev17
  hev18))))))))))))))))
  · have hc13' : n13 ≤ 1 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) := by simpa using hc13
    have hbound : n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + (n9 + (n10 + (n11 + (n12 + (n13 + (n14 + (n15 +
  (n16 + (n17 + (n18))))))))))))))))) ≤
        pb2ECost K1 K5a K7 K5b K11 Kpv K6 Kn10 Kc4a Kc4b Kc4c Kc4d Ku1 Kb10 Kc4e Kb11 Kc4f Kb
          Cm p α ss ts j arr := by
      unfold pb2ECost
      exact Nat.add_le_add hc1 (Nat.add_le_add hc2 (Nat.add_le_add hc3 (Nat.add_le_add hc4
        (Nat.add_le_add hc5 (Nat.add_le_add hc6 (Nat.add_le_add hc7 (Nat.add_le_add hc8
        (Nat.add_le_add hc9 (Nat.add_le_add hc10 (Nat.add_le_add hc11 (Nat.add_le_add hc12
        (Nat.add_le_add hc13' (Nat.add_le_add hc14 (Nat.add_le_add hc15 (Nat.add_le_add hc16
        (Nat.add_le_add hc17 hc18))))))))))))))))
    exact le_trans hbound (hCost Cm p α ss ts j arr hRes' hjD hsz0)
  · exact h018
  · exact hk18

/-- Mirror of paStageE for the B half: peel the axis data, build the table Pj with prep, push the applyAlong arguments. -/
theorem pb2StageE (Kb : ℕ) (prep q : HvdH.Cmd) :
    ∃ (stage : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ)
        (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
        (zs0 : List (ℤ × ℤ)) (Pj : List HvdH.Val),
      HvdH.ResParams p α ss ts → Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N → Kb * p < N →
      j < HvdH.D →
      Work.Resample.SliceSpecAt prep q Kb p α (ss.getD j 0) (ts.getD j 0) (Φ j) Pj →
      Work.Resample.WordP main stage
        (fun vs rest a => Work.Resample.PB2Inv p α ss ts Φ zs0 j vs rest a)
        (fun vs rest a out b => Work.Resample.PB2Mid Kb p α ss ts Φ zs0 j Pj out rest b)
        (fun _ _ _ => Kc * Work.Resample.PB2Br Kb Cm p α ss ts j) :=
  pb2EStageCore pb2ECostBd Kb prep q

end Work.Resample
