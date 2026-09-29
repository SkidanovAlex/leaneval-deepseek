import Mathlib
import Submission.Work.Resample.MulNW.Defs
import Submission.Work.Resample.MulNW.Setup
import Submission.Work.Resample.MulNW.peel_ev
import Submission.Work.Resample.MulNW.initR_ev
import Submission.Work.Resample.MulNW.addA_ev
import Submission.Work.Resample.MulNW.MainLoop
import Submission.Work.Resample.MulNW.finalize_ev

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH
open Work.Resample.MulNW

/-- There is a StackLang word replacing the two natural-number values on top of the value stack by
their product, at the schoolbook cost `K * (size a + 1) * (size b + 1)`.

The workspace already contains a complete schoolbook multiplier to build on:
`Work.IntLib.MulS.mulSProg` (`Submission/Work/IntLib/mulSDefs.lean`) with all of its bit-level
arithmetic (`Submission/Work/IntLib/mulSArith.lean`: `run_spec`, `run_final_val`, `stripHigh_eq_bits`,
`finalize_val`, `mbits`) and the beginnings of the `Ev`-level simulation of its phases
(`Submission/Work/IntLib/mulSEv.lean`: `fullAdd_ev`, `drain_ev`, `drain_ev'`).  Either finish that
simulation, or write an independent word.  Note the `WordR` frame: stack 0 holds `int a :: int b ::
rest` and every other stack must come back exactly as it was (the multiplier's scratch markers must
be popped), while registers are free.  It is enough to handle `a, b ≥ 1` (the two zero-bit cases
`a = 0` or `b = 0` — empty bit lists — are excluded by the hypotheses). -/
theorem mulNatWord : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a b : ℕ), 1 ≤ a → 1 ≤ b →
    ∀ rest : List HvdH.Val,
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int (a : ℤ) :: HvdH.Val.int (b : ℤ) :: rest)
        (fun _ out => out = HvdH.Val.int ((a * b : ℕ) : ℤ) :: rest)
        (fun _ => K * (a.size + 1) * (b.size + 1)) := by
  refine ⟨MulNW.mulProg, 300, ?_⟩
  intro main a b ha hb rest vs hvs s R hs
  subst hvs
  -- phase 1: push the frame markers
  obtain ⟨s1, n1, e1, hn1, h01, hA1, hB1, hR1, hC1, hS1, hT1, hW1, hU1, hf1⟩ :=
    MulNW.open_ev main s
  -- phase 2: peel the two values off stack 0
  obtain ⟨s2, n2, e2, hn2, h02, hA2, hB2, hS2, hW2, hT2, hf2⟩ :=
    MulNW.peel_ev main a b rest R (s.stk sT) (s.stk sW) s1 (h01.trans hs) hW1 hT1
  -- phase 3: initialise the remainder
  have hR2 : s2.stk sR = s1.stk sR := hf2 sR (by decide)
  obtain ⟨s3, n3, e3, hn3, hA3, hW3, hR3, hf3⟩ :=
    MulNW.initR_ev main a (s.stk sA) (s.stk sW) (s1.stk sR) s2
      (by rw [hA2, hA1]) (by rw [hW2, hW1]) hR2
  -- phase 4: the serial multiplier loop
  have hB3 : s3.stk sB = natBits b ++ mkB :: s.stk sB := by
    rw [hf3 sB (by decide), hB2, hB1]
  have hR3' : s3.stk sR = bitsG (zeros a.size) ++ mkR :: s.stk sR := by
    rw [hR3, hR1]
  have hC3 : s3.stk sC = mkC :: s.stk sC := by
    rw [hf3 sC (by decide), hf2 sC (by decide), hC1]
  have hT3 : s3.stk sT = mkT :: s.stk sT := by
    rw [hf3 sT (by decide), hT2, hT1]
  obtain ⟨s4, n4, e4, hn4, hB4, hR4, hC4, hA4, hW4, hT4, hf4⟩ :=
    MulNW.mainLoop_ev main (MulNW.addA_ev main) a b (s.stk sA) (s.stk sB) (s.stk sR) (s.stk sC)
      (s.stk sW) (s.stk sT) s3 hA3 hB3 hR3' hC3 hW3 hT3
  -- phase 5: assemble the product
  have h04 : s4.stk 0 = encs rest ++ R := by
    rw [hf4 0 (by decide), hf3 0 (by decide)]
    exact h02
  have hS4 : s4.stk sS = Glyph.pos :: Glyph.pos :: mkS :: s.stk sS := by
    rw [hf4 sS (by decide), hf3 sS (by decide), hS2, hS1]
  have hU4 : s4.stk sU = mkU :: s.stk sU := by
    rw [hf4 sU (by decide), hf3 sU (by decide), hf2 sU (by decide), hU1]
  obtain ⟨s5, n5, e5, hn5, h05, hS5, hR5, hC5, hT5, hW5, hU5, hf5⟩ :=
    MulNW.finalize_ev main a b rest R ha hb (s.stk sS) (s.stk sR) (s.stk sC) (s.stk sT)
      (s.stk sW) (s.stk sU) s4 h04 hS4 hR4 hC4 hW4 hT4 hU4
  -- phase 6: pop the markers again
  obtain ⟨s6, n6, e6, hn6, hs6A, hs6B, hs6R, hs6C, hs6T, hs6W, hs6U, hf6⟩ :=
    MulNW.close_ev main a (s.stk sA) (s.stk sB) (s.stk sR) (s.stk sC) (s.stk sT) (s.stk sW)
      (s.stk sU) s5 ((hf5 sA (by decide)).trans hA4) ((hf5 sB (by decide)).trans hB4)
      hR5 hC5 hT5 hW5 hU5
  -- the composed program
  have eall : Eval main MulNW.mulProg s s6 (n1 + (n2 + (n3 + (n4 + (n5 + n6))))) := by
    have h := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))
    simpa [MulNW.mulProg] using h
  have hstk0 : s6.stk 0 = encs (.int ((a * b : ℕ) : ℤ) :: rest) ++ R := by
    rw [hf6 0 (by decide)]
    exact h05
  -- every other stack is restored
  have hrestore : ∀ k : Stk, k ≠ 0 → s6.stk k = s.stk k := by
    intro k hk
    by_cases hmem : k ∈ ({MulNW.sA, MulNW.sB, MulNW.sR, MulNW.sC, MulNW.sS, MulNW.sT, MulNW.sW,
      MulNW.sU} : Finset Stk)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hh | hh | hh | hh | hh | hh | hh | hh
      · rw [hh]; exact hs6A
      · rw [hh]; exact hs6B
      · rw [hh]; exact hs6R
      · rw [hh]; exact hs6C
      · rw [hh]
        exact (hf6 MulNW.sS (by decide)).trans hS5
      · rw [hh]; exact hs6T
      · rw [hh]; exact hs6W
      · rw [hh]; exact hs6U
    · have hkA : k ≠ MulNW.sA := fun hh => hmem (by simp [hh])
      have hkB : k ≠ MulNW.sB := fun hh => hmem (by simp [hh])
      have hkR : k ≠ MulNW.sR := fun hh => hmem (by simp [hh])
      have hkC : k ≠ MulNW.sC := fun hh => hmem (by simp [hh])
      have hkS : k ≠ MulNW.sS := fun hh => hmem (by simp [hh])
      have hkT : k ≠ MulNW.sT := fun hh => hmem (by simp [hh])
      have hkW : k ≠ MulNW.sW := fun hh => hmem (by simp [hh])
      have hkU : k ≠ MulNW.sU := fun hh => hmem (by simp [hh])
      have hm6 : k ∉ ({MulNW.sA, MulNW.sB, MulNW.sR, MulNW.sC, MulNW.sT, MulNW.sW,
          MulNW.sU} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hkA, hkB, hkR, hkC, hkT, hkW, hkU⟩
      have hm5 : k ∉ ({0, MulNW.sR, MulNW.sC, MulNW.sS, MulNW.sT, MulNW.sW,
          MulNW.sU} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hk, hkR, hkC, hkS, hkT, hkW, hkU⟩
      have hm4 : k ∉ ({MulNW.sA, MulNW.sB, MulNW.sC, MulNW.sR, MulNW.sT,
          MulNW.sW} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hkA, hkB, hkC, hkR, hkT, hkW⟩
      have hm3 : k ∉ ({MulNW.sA, MulNW.sR, MulNW.sW} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hkA, hkR, hkW⟩
      have hm2 : k ∉ ({0, MulNW.sA, MulNW.sB, MulNW.sS, MulNW.sT, MulNW.sW} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hk, hkA, hkB, hkS, hkT, hkW⟩
      have hm1 : k ∉ ({0, MulNW.sA, MulNW.sB, MulNW.sR, MulNW.sC, MulNW.sS, MulNW.sT, MulNW.sW,
          MulNW.sU} : Finset Stk) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hk, hkA, hkB, hkR, hkC, hkS, hkT, hkW, hkU⟩
      rw [hf6 k hm6, hf5 k hm5, hf4 k hm4, hf3 k hm3, hf2 k hm2]
      exact hf1 k hm1
  refine ⟨[.int ((a * b : ℕ) : ℤ)] ++ rest, s6, n1 + (n2 + (n3 + (n4 + (n5 + n6)))), rfl, eall,
    ?_, hstk0, hrestore⟩
  -- the cost estimate
  have ha' : 1 ≤ a.size := Nat.size_pos.mpr (by omega)
  have hb' : 1 ≤ b.size := Nat.size_pos.mpr (by omega)
  have hn2' : n2 ≤ 40 * (a.size + b.size + 2) := hn2
  have hn3' : n3 ≤ 30 * (a.size + 1) := hn3
  have hn4' : n4 ≤ 110 * (a.size + 1) * (b.size + 1) := hn4
  have hn5' : n5 ≤ 60 * (a.size + b.size + 4) := hn5
  have hn6' : n6 ≤ 10 * (a.size + 2) := hn6
  nlinarith [hn1, hn2', hn3', hn4', hn5', hn6', ha', hb', Nat.zero_le a.size, Nat.zero_le b.size]

end Work.Resample
