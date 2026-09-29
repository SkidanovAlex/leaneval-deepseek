import Mathlib
import Submission.Work.Fx.ExpDefs
import Submission.Work.Fx.expRec
import Submission.Work.Fx.expCplxAux
import Submission.Work.Fx.expPrelude
import Submission.Work.Fx.expStepA
import Submission.Work.Fx.expStepB
import Submission.Work.Fx.expEpilogue

/-!
# `Work.Fx.expCplx`: the fixed-point complex exponential (`p ≥ 100`, `‖z‖ ≤ 32`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.Fx

open HvdH

theorem expCplx (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (X Y : ℤ), 100 ≤ p →
      ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) →
      HvdH.WordR main prog (fun vs => ∃ (rest : List HvdH.Val),
          vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int X :: HvdH.Val.int Y :: rest)
        (fun vs out => ∃ (rest : List HvdH.Val) (U V : ℤ),
          vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int X :: HvdH.Val.int Y :: rest ∧
          out = HvdH.Val.int U :: HvdH.Val.int V :: rest ∧
          ‖((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ p -
            Complex.exp (((X : ℂ) + (Y : ℂ) * Complex.I) / 2 ^ p)‖ ≤ 4 / (2 : ℝ) ^ p)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨preP, Kpre, hpre⟩ := expPrelude hk hi
  obtain ⟨qA, KA, hA⟩ := expStepA hk hi
  obtain ⟨qB, KB, hB⟩ := expStepB hk hi
  obtain ⟨epP, Kep, hep⟩ := expEpilogue hk hi
  obtain ⟨comb, Kf, hfold⟩ := hk.foldList
  refine ⟨Cmd.seq preP (Cmd.seq (comb (Cmd.seq qA qB)) epP), ExpAsm.Cst Kpre KA KB Kep Kf, ?_⟩
  intro main p X Y hp hXY
  have hX : |(X : ℝ)| ≤ 32 * 2 ^ p := (ExpAsm.abs_le_of_sq_sum hXY (by positivity)).1
  have hY : |(Y : ℝ)| ≤ 32 * 2 ^ p := (ExpAsm.abs_le_of_sq_sum hXY (by positivity)).2
  have hz32 : ‖zval p X Y‖ ≤ 32 := ExpAsm.norm_zval_le p X Y hXY
  -- (1) one Horner step, as a `Spec` on the 8-value window
  have hstep : ∀ (Qre Qim dd : ℤ), 1 ≤ dd →
      Spec main (Cmd.seq qA qB) 8
        (fun t => t = ExpAsm.preWin p X Y Qre Qim dd)
        (fun t o => o = ExpAsm.postWin p X Y Qre Qim dd)
        (fun t => KA * (szl t + 1) ^ KA + KB * (szl (ExpAsm.midWin p X Y Qre Qim dd) + 1) ^ KB) := by
    intro Qre Qim dd hdd1
    have hPownz : ((2 : ℤ) ^ (wprec p)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hA1 := hA main Qre Qim dd (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p))
      ((2 : ℤ) ^ (wprec p)) ((d0 p : ℕ))
    have hB1 := hB main (X * (2 : ℤ) ^ (d0 p) * Qre - Y * (2 : ℤ) ^ (d0 p) * Qim)
      (X * (2 : ℤ) ^ (d0 p) * Qim + Y * (2 : ℤ) ^ (d0 p) * Qre) dd
      (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) ((d0 p : ℕ)) hPownz hdd1
    have hB2 : Spec main qB 7 (fun t => t = ExpAsm.midWin p X Y Qre Qim dd)
        (fun _ o => o = ExpAsm.postWin p X Y Qre Qim dd)
        (fun _ => KB * (szl (ExpAsm.midWin p X Y Qre Qim dd) + 1) ^ KB) :=
      Spec.mono hk hB1 (fun t ht hq => by rw [hq]; rfl)
        (fun t o ht hq hQ => hQ) (fun t ht hq => by rw [hq])
    have hAB := Spec.seq hk hA1 hB2
      (by intro t o ht hq hQ; rw [hQ]; rfl)
      (by intro t o ht hq hQ; rw [hQ]; rfl)
      (by intro t o ht hq hQ; exact le_rfl)
    refine Spec.mono hk hAB (fun t ht hq => by rw [hq]; rfl) ?_ (fun t ht hq => le_rfl)
    intro t o ht hq hQ
    rcases hQ with ⟨o', ho', hpost⟩
    rw [hpost]
  -- (2) the step requirement of the fold (with the rest pinned)
  have hstepReq : ∀ (rest : List Val) (i : ℕ) (acc : List Val),
      i < (List.replicate (wcnt p) (Val.int 1)).length → ExpAsm.Inv p X Y i acc →
      acc.drop 7 = rest →
      WordR main (Cmd.seq qA qB)
        (fun vs => vs = (List.replicate (wcnt p) (Val.int 1)).getD i Val.nil :: acc)
        (fun _ out => ExpAsm.Inv p X Y (i + 1) out ∧ out.drop 7 = rest)
        (fun _ => ExpAsm.cc p KA KB) := by
    intro rest i acc hilt hInv hdrop
    have hlt : i < wcnt p := by simpa using hilt
    rcases hInv with ⟨rest0, Qre, Qim, dd, hacc, hdd, hile, herr⟩
    subst hacc
    have hrest0 : rest0 = rest := by
      have h := hdrop
      rw [ExpAsm.drop_seven_append] at h
      exact h
    subst rest0
    have hdd1 : 1 ≤ dd := by rw [hdd]; omega
    have hcoord := ExpAsm.coord_bound p X Y hp hz32 i herr
    have hddle : isz dd ≤ wprec p + 10 := ExpAsm.isz_dd_le' p hdd hile
    have hszpre : szl (ExpAsm.preWin p X Y Qre Qim dd) ≤ scnt p :=
      ExpAsm.szl_pre_le p X Y Qre Qim dd hX hY hcoord.1 hcoord.2 hddle
    have hszmid : szl (ExpAsm.midWin p X Y Qre Qim dd) ≤ scnt p :=
      ExpAsm.szl_mid_le p X Y Qre Qim dd hX hY hcoord.1 hcoord.2 hddle
    have hcost : KA * (szl (ExpAsm.preWin p X Y Qre Qim dd) + 1) ^ KA +
        KB * (szl (ExpAsm.midWin p X Y Qre Qim dd) + 1) ^ KB ≤ ExpAsm.cc p KA KB :=
      ExpAsm.cost_absorb hszpre hszmid
    have hspec := hstep Qre Qim dd hdd1
    have hword : WordR main (Cmd.seq qA qB)
        (fun vs => vs = ExpAsm.preWin p X Y Qre Qim dd ++ rest)
        (fun _ out => ∃ o, out = o ++ rest ∧ o = ExpAsm.postWin p X Y Qre Qim dd)
        (fun _ => KA * (szl (ExpAsm.preWin p X Y Qre Qim dd) + 1) ^ KA +
          KB * (szl (ExpAsm.midWin p X Y Qre Qim dd) + 1) ^ KB) :=
      Spec.use hspec rfl rfl
    refine hk.conseq (main := main) (p := Cmd.seq qA qB)
      (P := fun vs => vs = ExpAsm.preWin p X Y Qre Qim dd ++ rest)
      (P' := fun vs => vs = (List.replicate (wcnt p) (Val.int 1)).getD i Val.nil ::
        ([Val.int Qre, Val.int Qim, Val.int dd, Val.int (X * (2 : ℤ) ^ (d0 p)),
          Val.int (Y * (2 : ℤ) ^ (d0 p)), Val.int ((2 : ℤ) ^ (wprec p)),
          Val.int ((d0 p : ℕ))] ++ rest))
      (Q := fun _ out => ∃ o, out = o ++ rest ∧ o = ExpAsm.postWin p X Y Qre Qim dd)
      (Q' := fun _ out => ExpAsm.Inv p X Y (i + 1) out ∧ out.drop 7 = rest)
      (C := fun _ => KA * (szl (ExpAsm.preWin p X Y Qre Qim dd) + 1) ^ KA +
          KB * (szl (ExpAsm.midWin p X Y Qre Qim dd) + 1) ^ KB)
      (C' := fun _ => ExpAsm.cc p KA KB) hword ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [ExpAsm.getD_replicate_nil hlt, ExpAsm.preWin, List.cons_append]
    · intro vs out hvs hQ
      rcases hQ with ⟨o, hout, ho⟩
      rw [hout, ho]
      refine ⟨⟨rest, _, _, dd - 1, rfl, ?_, ?_, ?_⟩, ?_⟩
      · rw [hdd]; omega
      · omega
      · exact ExpAsm.err_step p X Y hlt hdd hdd1 hz32 herr
      · rw [ExpAsm.drop_append_postWin]
    · intro vs hvs
      exact hcost
  -- (3) the fold
  have hfoldW : ∀ (rest : List Val),
      WordR main (comb (Cmd.seq qA qB))
        (fun vs => ∃ acc, vs = ofList (List.replicate (wcnt p) (Val.int 1)) :: acc ∧
          ExpAsm.Inv p X Y 0 acc ∧ acc.drop 7 = rest)
        (fun _ out => ExpAsm.Inv p X Y (wcnt p) out ∧ out.drop 7 = rest)
        (fun _ => wcnt p * (ExpAsm.cc p KA KB + Kf * 4) + Kf) := by
    intro rest
    have h := hfold main (Cmd.seq qA qB) (List.replicate (wcnt p) (Val.int 1))
      (fun i acc => ExpAsm.Inv p X Y i acc ∧ acc.drop 7 = rest)
      (ExpAsm.cc p KA KB) 3 (by
        intro x hx
        have hx1 : x = Val.int 1 := List.eq_of_mem_replicate hx
        rw [hx1]
        exact le_of_eq ExpAsm.vsz_int_one)
      (fun i acc hilt hI => hstepReq rest i acc hilt hI.1 hI.2)
    simpa using h
  -- (4) the epilogue
  have hepW : ∀ (Qre Qim : ℤ) (rest : List Val),
      isz Qre ≤ wprec p + 52 → isz Qim ≤ wprec p + 52 →
      WordR main epP (fun vs => vs = ExpAsm.epWin p X Y Qre Qim ++ rest)
        (fun _ out => out = [Val.int (Int.tdiv Qre ((2 : ℤ) ^ (d0 p))),
          Val.int (Int.tdiv Qim ((2 : ℤ) ^ (d0 p)))] ++ rest)
        (fun _ => Kep * (scnt p + 1) ^ Kep) := by
    intro Qre Qim rest h1 h2
    have hspec := hep main (d0 p) Qre Qim 0 (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p))
      ((2 : ℤ) ^ (wprec p))
    have hword : WordR main epP (fun vs => vs = ExpAsm.epWin p X Y Qre Qim ++ rest)
        (fun _ out => ∃ o, out = o ++ rest ∧
          o = [Val.int (Int.tdiv Qre ((2 : ℤ) ^ (d0 p))),
            Val.int (Int.tdiv Qim ((2 : ℤ) ^ (d0 p)))])
        (fun _ => Kep * (szl (ExpAsm.epWin p X Y Qre Qim) + 1) ^ Kep) :=
      Spec.use hspec rfl rfl
    refine hk.conseq (main := main) (p := epP)
      (P := fun vs => vs = ExpAsm.epWin p X Y Qre Qim ++ rest)
      (P' := fun vs => vs = ExpAsm.epWin p X Y Qre Qim ++ rest)
      (Q := fun _ out => ∃ o, out = o ++ rest ∧
          o = [Val.int (Int.tdiv Qre ((2 : ℤ) ^ (d0 p))),
            Val.int (Int.tdiv Qim ((2 : ℤ) ^ (d0 p)))])
      (Q' := fun _ out => out = [Val.int (Int.tdiv Qre ((2 : ℤ) ^ (d0 p))),
          Val.int (Int.tdiv Qim ((2 : ℤ) ^ (d0 p)))] ++ rest)
      (C := fun _ => Kep * (szl (ExpAsm.epWin p X Y Qre Qim) + 1) ^ Kep)
      (C' := fun _ => Kep * (scnt p + 1) ^ Kep) hword ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hQ
      rcases hQ with ⟨o, hout, ho⟩
      rw [hout, ho]
    · intro vs hvs
      have hsz : szl (ExpAsm.epWin p X Y Qre Qim) ≤ scnt p :=
        ExpAsm.szl_ep_le p X Y Qre Qim hX hY h1 h2
      have hpow : (szl (ExpAsm.epWin p X Y Qre Qim) + 1) ^ Kep ≤ (scnt p + 1) ^ Kep :=
        Nat.pow_le_pow_left (by omega) Kep
      exact Nat.mul_le_mul_left Kep hpow
  -- (5) run prelude, fold, epilogue
  intro vs hvs s R hR
  rcases hvs with ⟨rest, rfl⟩
  set acc0 : List Val := [Val.int ((2 : ℤ) ^ (wprec p)), Val.int 0, Val.int ((wcnt p : ℕ)),
      Val.int (X * (2 : ℤ) ^ (d0 p)), Val.int (Y * (2 : ℤ) ^ (d0 p)),
      Val.int ((2 : ℤ) ^ (wprec p)), Val.int ((d0 p : ℕ))] ++ rest with hacc0
  obtain ⟨mid1, s1, n1, hpost1, hev1, hn1, hstk1, hfr1⟩ :=
    (hpre main p X Y rest hp hXY) ([Val.int (p : ℤ), Val.int X, Val.int Y] ++ rest) rfl s R hR
  have hmid1 : mid1 = ofList (List.replicate (wcnt p) (Val.int 1)) :: acc0 := by
    rw [hpost1]; rfl
  have hInv0 : ExpAsm.Inv p X Y 0 acc0 := by
    refine ⟨rest, (2 : ℤ) ^ (wprec p), 0, ((wcnt p : ℕ) : ℤ), by rw [hacc0], ?_, ?_, ?_⟩
    · simp
    · exact Nat.zero_le _
    · have hone : ∀ k : ℕ, hval (zval p X Y) k 0 = 1 := by
        intro k
        rw [hval, Finset.sum_range_one]
        simp [Nat.factorial_ne_zero]
      have hz0 : (((2 : ℤ) ^ (wprec p) : ℤ) : ℂ) / (2 : ℂ) ^ (wprec p) = 1 := by
        rw [show (((2 : ℤ) ^ (wprec p) : ℤ) : ℂ) = (2 : ℂ) ^ (wprec p) by push_cast; ring]
        exact div_self (pow_ne_zero _ (by norm_num))
      rw [hone]
      simp only [Int.cast_zero, zero_mul, add_zero, hz0, sub_self, norm_zero]
      simp [pot]
  have hdrop0 : acc0.drop 7 = rest := by
    rw [hacc0]
    exact ExpAsm.drop_seven_append _ _ _ _ _ _ _ rest
  obtain ⟨mid2, s2, n2, hpost2, hev2, hn2, hstk2, hfr2⟩ :=
    hfoldW rest mid1 ⟨acc0, hmid1, hInv0, hdrop0⟩ s1 R hstk1
  obtain ⟨hInv2, hdrop2⟩ := hpost2
  obtain ⟨rest2, Qre, Qim, dd, hmid2, hdd, hile, herr⟩ := hInv2
  have hrest2 : rest2 = rest := by
    have h := hdrop2
    rw [hmid2, ExpAsm.drop_seven_append] at h
    exact h
  subst rest2
  have hdd0 : dd = 0 := by rw [hdd]; simp
  rw [hdd0] at hmid2
  have hcoord := ExpAsm.coord_bound p X Y hp hz32 (wcnt p) herr
  obtain ⟨out, s3, n3, hpost3, hev3, hn3, hstk3, hfr3⟩ :=
    hepW Qre Qim rest hcoord.1 hcoord.2 mid2 (by simp only [hmid2, ExpAsm.epWin]) s2 R hstk2
  refine ⟨out, s3, n1 + (n2 + n3), ⟨rest, Int.tdiv Qre ((2 : ℤ) ^ (d0 p)),
    Int.tdiv Qim ((2 : ℤ) ^ (d0 p)), ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rfl
  · rw [hpost3]
    rfl
  · -- the error bound
    refine ExpAsm.final_bound p hp (zval p X Y) hz32 _ _ Qre Qim rfl rfl ?_
    have hw : wcnt p - wcnt p = 0 := by omega
    rw [hw] at herr
    simpa using herr
  · exact Eval.seq (c₁ := preP) (c₂ := Cmd.seq (comb (Cmd.seq qA qB)) epP)
      (s₁ := s) (s₂ := s1) (s₃ := s3) (n₁ := n1) (n₂ := n2 + n3)
      hev1 (Eval.seq (c₁ := comb (Cmd.seq qA qB)) (c₂ := epP) (s₁ := s1) (s₂ := s2) (s₃ := s3)
        (n₁ := n2) (n₂ := n3) hev2 hev3)
  · have hn1' : n1 ≤ Kpre * (p + 1) ^ Kpre := hn1
    have hn2' : n2 ≤ wcnt p * (ExpAsm.cc p KA KB + Kf * 4) + Kf := hn2
    have hn3' : n3 ≤ Kep * (scnt p + 1) ^ Kep := hn3
    rw [← Nat.add_assoc]
    exact ExpAsm.cost_total p n1 n2 n3 Kpre KA KB Kep Kf hp hn1' hn2' hn3'
  · rw [hstk3, hpost3]
  · intro k hk
    rw [hfr3 k hk, hfr2 k hk, hfr1 k hk]

end Work.Fx
