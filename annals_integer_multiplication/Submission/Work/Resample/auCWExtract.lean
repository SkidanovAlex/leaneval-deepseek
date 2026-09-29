import Mathlib
import Submission.Work.Resample.auCWCntWord
import Submission.Work.Layout.mvVal_ev_full
import Submission.Work.Kernel.Raw

/-!
# `Work.Resample.auCWExtract`

Move the three parameter values `p, lo_r, lo_i` of the parameter block P to stack 1, run the
counting word `auCWCountWord` on the record chain left on stack 0, move the three values back on top
of the counts, and restore the frame.

Cost: three `mvVal` out (≤ `16*(3*(p+1)+1)` each), the counting word
(≤ `Kc*(qs.length+1)`) and three `mvVal` back.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Resample

open HvdH

theorem ev_cost {main p : HvdH.Cmd} {s s' : HvdH.State} {C : ℕ}
    (h : Work.Layout.Ev main p s s' C) : ∃ m, HvdH.Eval main p s s' m ∧ m ≤ C := h

theorem auCWExtract (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (lo_r lo_i : ℤ)
      (qs : List (ℤ × ℤ)) (T : List HvdH.Val),
      0 ≤ lo_r → lo_r < Work.Resample.awMod p → 0 ≤ lo_i → lo_i < Work.Resample.awMod p →
      (∀ q ∈ qs, q.1 = 0 ∨ q.1 = 1) → (∀ q ∈ qs, q.2 = 0 ∨ q.2 = 1) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int lo_r :: HvdH.Val.int lo_i
          :: HvdH.ofList (qs.map fun q => Work.Resample.awRec q.1 q.2) :: T)
        (fun _ out => out = HvdH.Val.int (p : ℤ) :: HvdH.Val.int lo_r :: HvdH.Val.int lo_i
          :: HvdH.Val.int ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum)
          :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
          :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
        (fun _ => K * (qs.length + 1) * (p + 1)) := by
  obtain ⟨cntP, Kc, hCnt⟩ := auCWCountWord hk hi
  refine ⟨HvdH.Cmd.seq (Work.Layout.mvVal 0 1 2 3)
    (HvdH.Cmd.seq (Work.Layout.mvVal 0 1 2 3)
    (HvdH.Cmd.seq (Work.Layout.mvVal 0 1 2 3)
    (HvdH.Cmd.seq cntP
    (HvdH.Cmd.seq (Work.Layout.mvVal 1 0 2 3)
    (HvdH.Cmd.seq (Work.Layout.mvVal 1 0 2 3)
      (Work.Layout.mvVal 1 0 2 3)))))), 500 + Kc, ?_⟩
  intro main p lo_r lo_i qs T hl0 hlM hl1 hlM2 hq1 hq2
  intro vs hpre s Rg hRg
  have hpre' : vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int lo_r :: HvdH.Val.int lo_i
      :: HvdH.ofList (qs.map fun q => awRec q.1 q.2) :: T := hpre
  -- ### move `int p`, `int lo_r`, `int lo_i` to stack 1
  have hA0 : s.stk 0 = (HvdH.Val.int (p : ℤ)).enc ++ (HvdH.encs (HvdH.Val.int lo_r
      :: HvdH.Val.int lo_i :: HvdH.ofList (qs.map fun q => awRec q.1 q.2) :: T) ++ Rg) := by
    rw [hRg, hpre']
    simp [Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨s1, n1, hev1, hn1, ha1, hb1, hc1, hd1, hf1⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s.reg) (X := s.stk) (v := HvdH.Val.int (p : ℤ))
      (A := HvdH.encs (HvdH.Val.int lo_r :: HvdH.Val.int lo_i
        :: HvdH.ofList (qs.map fun q => awRec q.1 q.2) :: T) ++ Rg) (B := s.stk 1) hA0 rfl
  have hA1 : s1.stk 0 = (HvdH.Val.int lo_r).enc ++ (HvdH.encs (HvdH.Val.int lo_i
      :: HvdH.ofList (qs.map fun q => awRec q.1 q.2) :: T) ++ Rg) := by
    rw [ha1]
    simp [Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨s2, n2, hev2, hn2, ha2, hb2, hc2, hd2, hf2⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s1.reg) (X := s1.stk) (v := HvdH.Val.int lo_r)
      (A := HvdH.encs (HvdH.Val.int lo_i :: HvdH.ofList (qs.map fun q => awRec q.1 q.2) :: T) ++ Rg)
      (B := s1.stk 1) hA1 rfl
  have hA2 : s2.stk 0 = (HvdH.Val.int lo_i).enc ++ (HvdH.encs (HvdH.ofList (qs.map fun q => awRec q.1 q.2)
      :: T) ++ Rg) := by
    rw [ha2]
    simp [Work.Kernel.encs_cons, List.append_assoc]
  obtain ⟨s3, n3, hev3, hn3, ha3, hb3, hc3, hd3, hf3⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s2.reg) (X := s2.stk) (v := HvdH.Val.int lo_i)
      (A := HvdH.encs (HvdH.ofList (qs.map fun q => awRec q.1 q.2) :: T) ++ Rg)
      (B := s2.stk 1) hA2 rfl
  -- the stack-1 content
  have hB1 : s3.stk 1 = (HvdH.Val.int lo_i).enc ++ ((HvdH.Val.int lo_r).enc ++ ((HvdH.Val.int (p : ℤ)).enc ++ s.stk 1)) := by
    rw [hb3, hb2, hb1]
  -- ### run the counting word
  have hR3 : s3.stk 0 = HvdH.encs (HvdH.ofList (qs.map fun q => awRec q.1 q.2) :: T) ++ Rg := ha3
  obtain ⟨out4, s4, n4, hpost4, hev4, hn4, h04, hf4⟩ :=
    hCnt main qs T hq1 hq2 (HvdH.ofList (qs.map fun q => awRec q.1 q.2) :: T) rfl s3 Rg hR3
  have hs41 : s4.stk 1 = s3.stk 1 := hf4 1 (by decide)
  -- ### move `int lo_i` back on top of stack 0
  have hEpre : s4.stk 1 = (HvdH.Val.int lo_i).enc ++ ((HvdH.Val.int lo_r).enc
      ++ ((HvdH.Val.int (p : ℤ)).enc ++ s.stk 1)) := by rw [hs41, hB1]
  have hE0 : s4.stk 0 = HvdH.encs (HvdH.Val.int
        ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum)
      :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
      :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T) ++ Rg := by
    rw [h04, hpost4]
  obtain ⟨s5, n5, hev5, hn5, ha5, hb5, hc5, hd5, hf5⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 1) (b := 0) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s4.reg) (X := s4.stk) (v := HvdH.Val.int lo_i)
      (A := (HvdH.Val.int lo_r).enc ++ ((HvdH.Val.int (p : ℤ)).enc ++ s.stk 1))
      (B := HvdH.encs (HvdH.Val.int ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T) ++ Rg) hEpre hE0
  have hB5 : s5.stk 1 = (HvdH.Val.int lo_r).enc ++ ((HvdH.Val.int (p : ℤ)).enc ++ s.stk 1) := ha5
  have hA5 : s5.stk 0 = (HvdH.Val.int lo_i).enc ++ (HvdH.encs (HvdH.Val.int
        ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum)
      :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
      :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T) ++ Rg) := hb5
  -- ### move `int lo_r` back
  obtain ⟨s6, n6, hev6, hn6, ha6, hb6, hc6, hd6, hf6⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 1) (b := 0) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s5.reg) (X := s5.stk) (v := HvdH.Val.int lo_r)
      (A := (HvdH.Val.int (p : ℤ)).enc ++ s.stk 1)
      (B := (HvdH.Val.int lo_i).enc ++ (HvdH.encs (HvdH.Val.int
          ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T) ++ Rg)) hB5 hA5
  have hB6 : s6.stk 1 = (HvdH.Val.int (p : ℤ)).enc ++ s.stk 1 := ha6
  have hA6 : s6.stk 0 = (HvdH.Val.int lo_r).enc ++ ((HvdH.Val.int lo_i).enc
      ++ (HvdH.encs (HvdH.Val.int ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T) ++ Rg)) := hb6
  -- ### move `int p` back
  obtain ⟨s7, n7, hev7, hn7, ha7, hb7, hc7, hd7, hf7⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 1) (b := 0) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (g := s6.reg) (X := s6.stk) (v := HvdH.Val.int (p : ℤ)) (A := s.stk 1)
      (B := (HvdH.Val.int lo_r).enc ++ ((HvdH.Val.int lo_i).enc
        ++ (HvdH.encs (HvdH.Val.int ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum)
          :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
          :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T) ++ Rg))) hB6 hA6
  -- ### sizes
  have hszp : HvdH.vsz (HvdH.Val.int (p : ℤ)) ≤ 3 * (p + 1) := by
    have hvz : HvdH.vsz (HvdH.Val.int (p : ℤ)) = HvdH.isz (p : ℤ) := Work.IntLib.vsz_int (p : ℤ)
    rw [hvz, HvdH.isz, Int.natAbs_natCast]
    have h : p.size ≤ p := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hszl : HvdH.vsz (HvdH.Val.int lo_r) ≤ 3 * (p + 1) := by
    have hvz : HvdH.vsz (HvdH.Val.int lo_r) = HvdH.isz lo_r := Work.IntLib.vsz_int lo_r
    rw [hvz, HvdH.isz]
    have hM : lo_r < (2 : ℤ) ^ (2 * p + 1) := by
      rw [Work.Resample.awMod, Work.Resample.awQ] at hlM
      exact hlM
    have h1 : (lo_r.natAbs : ℤ) < (2 : ℤ) ^ (2 * p + 1) := by
      rw [Int.natAbs_of_nonneg hl0]
      exact hM
    have h2 : lo_r.natAbs < 2 ^ (2 * p + 1) := by exact_mod_cast h1
    have h3 : lo_r.natAbs.size ≤ 2 * p + 1 := Nat.size_le.mpr h2
    omega
  have hszl1 : HvdH.vsz (HvdH.Val.int lo_i) ≤ 3 * (p + 1) := by
    have hvz : HvdH.vsz (HvdH.Val.int lo_i) = HvdH.isz lo_i := Work.IntLib.vsz_int lo_i
    rw [hvz, HvdH.isz]
    have hM : lo_i < (2 : ℤ) ^ (2 * p + 1) := by
      rw [Work.Resample.awMod, Work.Resample.awQ] at hlM2
      exact hlM2
    have h1 : (lo_i.natAbs : ℤ) < (2 : ℤ) ^ (2 * p + 1) := by
      rw [Int.natAbs_of_nonneg hl1]
      exact hM
    have h2 : lo_i.natAbs < 2 ^ (2 * p + 1) := by exact_mod_cast h1
    have h3 : lo_i.natAbs.size ≤ 2 * p + 1 := Nat.size_le.mpr h2
    omega
  -- ### Eval and cost
  obtain ⟨m1, he1, hm1⟩ := ev_cost hev1
  obtain ⟨m2, he2, hm2⟩ := ev_cost hev2
  obtain ⟨m3, he3, hm3⟩ := ev_cost hev3
  have hm4 : n4 ≤ Kc * (qs.length + 1) := hn4
  obtain ⟨m5, he5, hm5⟩ := ev_cost hev5
  obtain ⟨m6, he6, hm6⟩ := ev_cost hev6
  obtain ⟨m7, he7, hm7⟩ := ev_cost hev7
  have hEval : HvdH.Eval main (HvdH.Cmd.seq (Work.Layout.mvVal 0 1 2 3)
      (HvdH.Cmd.seq (Work.Layout.mvVal 0 1 2 3)
      (HvdH.Cmd.seq (Work.Layout.mvVal 0 1 2 3)
      (HvdH.Cmd.seq cntP
      (HvdH.Cmd.seq (Work.Layout.mvVal 1 0 2 3)
      (HvdH.Cmd.seq (Work.Layout.mvVal 1 0 2 3)
        (Work.Layout.mvVal 1 0 2 3))))))) s s7
      (m1 + (m2 + (m3 + (n4 + (m5 + (m6 + m7)))))) :=
    HvdH.Eval.seq he1 (HvdH.Eval.seq he2 (HvdH.Eval.seq he3 (HvdH.Eval.seq hev4
      (HvdH.Eval.seq he5 (HvdH.Eval.seq he6 he7)))))
  have hcost : m1 + (m2 + (m3 + (n4 + (m5 + (m6 + m7))))) ≤ (500 + Kc) * (qs.length + 1) * (p + 1) := by
    have hp1 : 1 ≤ p + 1 := by omega
    have hL1 : 1 ≤ qs.length + 1 := by omega
    have h1' : m1 ≤ 64 * (p + 1) := by
      have := hn1; have := hm1; nlinarith [hszp]
    have h2' : m2 ≤ 64 * (p + 1) := by
      have := hn2; have := hm2; nlinarith [hszl]
    have h3' : m3 ≤ 64 * (p + 1) := by
      have := hn3; have := hm3; nlinarith [hszl1]
    have h4' : n4 ≤ Kc * (qs.length + 1) := hm4
    have h5' : m5 ≤ 64 * (p + 1) := by
      have := hn5; have := hm5; nlinarith [hszl1]
    have h6' : m6 ≤ 64 * (p + 1) := by
      have := hn6; have := hm6; nlinarith [hszl]
    have h7' : m7 ≤ 64 * (p + 1) := by
      have := hn7; have := hm7; nlinarith [hszp]
    nlinarith [h1', h2', h3', h4', h5', h6', h7', hp1, hL1]
  -- ### the output
  refine ⟨HvdH.Val.int (p : ℤ) :: HvdH.Val.int lo_r :: HvdH.Val.int lo_i
    :: HvdH.Val.int ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum)
    :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
    :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T, s7,
    m1 + (m2 + (m3 + (n4 + (m5 + (m6 + m7))))), rfl, hEval, hcost, ?_, ?_⟩
  · rw [hb7]
    simp [Work.Kernel.encs_cons, List.append_assoc]
  · intro k hk0
    by_cases hk1 : k = 1
    · subst hk1; exact ha7
    by_cases hk2 : k = 2
    · subst hk2
      rw [hc7, hc6, hc5, hf4 2 (by decide), hc3, hc2, hc1]
    by_cases hk3 : k = 3
    · subst hk3
      rw [hd7, hd6, hd5, hf4 3 (by decide), hd3, hd2, hd1]
    · rw [hf7 k hk1 hk0 hk2 hk3, hf6 k hk1 hk0 hk2 hk3, hf5 k hk1 hk0 hk2 hk3, hf4 k hk0,
        hf3 k hk0 hk1 hk2 hk3, hf2 k hk0 hk1 hk2 hk3, hf1 k hk0 hk1 hk2 hk3]

end Work.Resample
