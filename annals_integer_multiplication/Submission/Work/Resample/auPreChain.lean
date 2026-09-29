import Mathlib
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auPreKit
import Submission.Work.Fx.piDefs
import Submission.Work.Kernel.Raw

/-!
# `Work.Resample.auPreChain`: the "pre" word of the 1-D resampling

See `Work.Resample.auPreKit` for the values the program computes and their size bounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Work.Resample

open HvdH
open Work.Fx

theorem auPreChain (hk : HvdH.KernelLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib)
    (piProg : HvdH.Cmd) (Kp : ℕ)
    (piSpec : ∀ (main : HvdH.Cmd) (P : ℕ), 100 ≤ P → HvdH.WordR main piProg
      (fun vs => ∃ rest, vs = [HvdH.Val.int (P : ℤ)] ++ rest)
      (fun vs out => ∃ rest, vs = [HvdH.Val.int (P : ℤ)] ++ rest ∧
        out = [HvdH.Val.int (Work.Fx.uval P)] ++ rest)
      (fun _ => Kp * (P + 1) ^ Kp)) :
    ∃ (pre : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (htp : t < 2 ^ p) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p),
      Work.Resample.Pipe main pre
        [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)]
        [HvdH.ofList (Work.Resample.auKs p t), HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ),
          HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ), HvdH.Val.int (Work.Resample.auPi p),
          HvdH.Val.int (Work.Resample.auCop p α s), HvdH.Val.int (Work.Resample.auOff p α s)]
        (K * (t + 1) * (p + 1) ^ K) := by
  obtain ⟨pickProg, Kpick, hPick⟩ := hk.pick
  obtain ⟨rollProg, Kroll, hRoll⟩ := hk.roll
  obtain ⟨pushProg, Kpush, hPush⟩ := hk.pushVal
  obtain ⟨addProg, Kadd, hAdd⟩ := hi.add
  obtain ⟨subProg, Ksub, hSub⟩ := hi.sub
  obtain ⟨mulProg, Kmul, hMul⟩ := hi.mulS
  obtain ⟨tdivProg, Ktdiv, hTdiv⟩ := hi.tdiv
  obtain ⟨sqrtProg, Ksqrt, hSqrt⟩ := hi.sqrt
  obtain ⟨replProg, Kr, hRepl⟩ := hl.replicate
  obtain ⟨enumProg, Ke, hEnum⟩ := hl.enumerate
  set KS : ℕ := Kpick + Kroll + Kpush + Kadd + Ksub + Kmul + Ktdiv + Ksqrt + 1 with hKS
  have hKpick : Kpick ≤ KS := by rw [hKS]; omega
  have hKroll : Kroll ≤ KS := by rw [hKS]; omega
  have hKpush : Kpush ≤ KS := by rw [hKS]; omega
  have hKadd : Kadd ≤ KS := by rw [hKS]; omega
  have hKsub : Ksub ≤ KS := by rw [hKS]; omega
  have hKmul : Kmul ≤ KS := by rw [hKS]; omega
  have hKtdiv : Ktdiv ≤ KS := by rw [hKS]; omega
  have hKsqrt : Ksqrt ≤ KS := by rw [hKS]; omega
  set Krc : ℕ := 10 * (Kr + Ke + 1) with hKrc
  set Ktot : ℕ := 100000 * (Kp + KS + Kr + Ke + 1) with hKtot
  set Kfin : ℕ := 10 * Ktot + 1000 with hKfin
  let preProg : Cmd :=
    Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq ((pickProg 0)) sqrtProg) (pushProg (Val.int (1)))) addProg) (pickProg 2)) mulProg) (pickProg 3)) (rollProg 1)) addProg) (pushProg (Val.int (1)))) (rollProg 1)) subProg) (pickProg 3)) (rollProg 1)) tdivProg) (pickProg 3)) mulProg) (pickProg 1)) sqrtProg) (pushProg (Val.int (1)))) addProg) (pickProg 3)) mulProg) (rollProg 1)) subProg) (pickProg 0)) (pickProg 4)) (pushProg (Val.int (2)))) mulProg) (pickProg 3)) sqrtProg) (pushProg (Val.int (1)))) addProg) (pickProg 5)) mulProg) (pushProg (Val.int (2)))) mulProg) addProg) (rollProg 1)) addProg) (pickProg 4)) (rollProg 1)) tdivProg) (pickProg 2)) (pushProg (Val.int (3)))) mulProg) (pushProg (Val.int (100)))) addProg) piProg) (rollProg 6)) (rollProg 6)) (rollProg 6)) (rollProg 6)) (pickProg 3)) (pickProg 5)) (rollProg 1)) replProg) enumProg
  refine ⟨preProg, Kfin, ?_⟩
  intro main p α s t hs hst htp hα hp hαp
  have hα1 : 1 ≤ α := by omega
  have hs1 : 1 ≤ s := by omega
  have hs2 : s ≤ 2 ^ p := le_of_lt (lt_trans hst htp)
  have h100 : 100 ≤ auPrec p := by simp only [auPrec]; omega
  set SB : ℕ := auSB p KS with hSB
  set CBt : ℕ := Krc * (t + 2) * (auSZ p + p + 3) with hCBt
  set CBIG : ℕ := SB + Kp * (auPrec p + 1) ^ Kp + CBt with hCBIG
  have hleSB : ∀ {c : ℕ}, c ≤ SB → c ≤ CBIG := by intro c hc; rw [hCBIG]; omega
  have hlePi : Kp * (auPrec p + 1) ^ Kp ≤ CBIG := by rw [hCBIG]; omega
  have hleT : ∀ {c : ℕ}, c ≤ CBt → c ≤ CBIG := by intro c hc; rw [hCBIG]; omega
  have hrepl : Kr * ((t + 1) * (vsz (Val.int (auPi p)) + 1) + isz ((t : ℤ)) + 1) ≤ CBt := by
    rw [hCBt]
    have h1 : vsz (Val.int (auPi p)) ≤ auSZ p := vszVI (isz_auPi_le p)
    have h2 : isz ((t : ℤ)) ≤ auSZ p := isz_t_le p t htp
    have h3 : Kr ≤ Krc := by rw [hKrc]; omega
    have e1 : (t + 1) * (vsz (Val.int (auPi p)) + 1) + isz ((t : ℤ)) + 1 ≤ (t + 2) * (auSZ p + 1) := by
      calc (t + 1) * (vsz (Val.int (auPi p)) + 1) + isz ((t : ℤ)) + 1
          ≤ (t + 1) * (auSZ p + 1) + auSZ p + 1 :=
            Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) h2) le_rfl
        _ = (t + 2) * (auSZ p + 1) := by ring
    calc Kr * ((t + 1) * (vsz (Val.int (auPi p)) + 1) + isz ((t : ℤ)) + 1)
        ≤ Kr * ((t + 2) * (auSZ p + 1)) := Nat.mul_le_mul_left _ e1
      _ = (Kr * (t + 2)) * (auSZ p + 1) := by rw [Nat.mul_assoc]
      _ ≤ Krc * (t + 2) * (auSZ p + p + 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul h3 le_rfl) (by omega)
  have hleTrepl : Kr * ((t + 1) * (vsz (Val.int (auPi p)) + 1) + isz ((t : ℤ)) + 1) ≤ CBIG :=
    hleT hrepl
  have htsz : t.size ≤ p := Nat.size_le.mpr htp
  have hvsL : vsz (ofList (List.replicate t (Val.int (auPi p)))) ≤ (t + 1) * (auSZ p + 1) := by
    have h : ∀ x ∈ List.replicate t (Val.int (auPi p)), vsz x ≤ auSZ p := by
      intro x hx
      rw [List.eq_of_mem_replicate hx]
      exact vszVI (isz_auPi_le p)
    have h4 := vsz_ofList_le (l := List.replicate t (Val.int (auPi p))) (B := auSZ p) h
    rw [List.length_replicate] at h4
    exact h4
  have henum : Ke * (vsz (ofList (List.replicate t (Val.int (auPi p)))) +
      (List.replicate t (Val.int (auPi p))).length *
        (((List.replicate t (Val.int (auPi p))).length).size + 1) + 1) ≤ CBt := by
    rw [hCBt, List.length_replicate]
    have hKe : 3 * Ke ≤ Krc := by rw [hKrc]; omega
    have hinner : vsz (ofList (List.replicate t (Val.int (auPi p)))) + t * (t.size + 1) + 1
        ≤ 3 * (t + 2) * (auSZ p + p + 3) := by
      have h2 : t * (t.size + 1) ≤ (t + 1) * (p + 1) := by
        calc t * (t.size + 1) ≤ t * (p + 1) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ (t + 1) * (p + 1) := Nat.mul_le_mul_right _ (by omega)
      have h3 : 1 ≤ (t + 1) * (p + 1) := by
        simpa using Nat.mul_le_mul (by omega : 1 ≤ t + 1) (by omega : 1 ≤ p + 1)
      calc vsz (ofList (List.replicate t (Val.int (auPi p)))) + t * (t.size + 1) + 1
          ≤ (t + 1) * (auSZ p + 1) + (t + 1) * (p + 1) + (t + 1) * (p + 1) :=
            Nat.add_le_add (Nat.add_le_add hvsL h2) h3
        _ = (t + 1) * ((auSZ p + 1) + 2 * (p + 1)) := by ring
        _ ≤ (t + 1) * (3 * (auSZ p + p + 3)) :=
            Nat.mul_le_mul_left _ (by simp only [auSZ]; omega)
        _ = 3 * (t + 1) * (auSZ p + p + 3) := by ring
        _ ≤ 3 * (t + 2) * (auSZ p + p + 3) := Nat.mul_le_mul_right _ (by omega)
    calc Ke * (vsz (ofList (List.replicate t (Val.int (auPi p)))) + t * (t.size + 1) + 1)
        ≤ Ke * (3 * (t + 2) * (auSZ p + p + 3)) := Nat.mul_le_mul_left _ hinner
      _ = 3 * Ke * (t + 2) * (auSZ p + p + 3) := by ring
      _ ≤ Krc * (t + 2) * (auSZ p + p + 3) := Nat.mul_le_mul (Nat.mul_le_mul hKe le_rfl) le_rfl
  have hleTenum : Ke * (vsz (ofList (List.replicate t (Val.int (auPi p)))) +
      (List.replicate t (Val.int (auPi p))).length *
        (((List.replicate t (Val.int (auPi p))).length).size + 1) + 1) ≤ CBIG :=
    hleT henum
  have hstep : ∀ {n : ℕ} {p' q : Cmd} {A B' D : List Val},
      Pipe main p' A B' (n * CBIG) → Pipe main q B' D CBIG → Pipe main (Cmd.seq p' q) A D ((n + 1) * CBIG) := by
    intro n p' q A B' D hp1 hq1
    have h := Pipe.comp hp1 hq1
    have heq : n * CBIG + CBIG = (n + 1) * CBIG := by rw [Nat.add_mul, Nat.one_mul]
    rw [heq] at h
    exact h
  -- the cost arithmetic
  have hKSle : KS ≤ Ktot := by rw [hKtot, hKS]; omega
  have hKrc_le : Krc ≤ 2 * Ktot := by rw [hKrc]; omega
  have hSB1 : SB ≤ KS * (168100 * (p + 1) ^ 2) := by
    rw [hSB, auSB, auSZ]
    have h1 : (10 * p + 408) ^ 2 ≤ (410 * (p + 1)) ^ 2 :=
      Nat.pow_le_pow_left (n := 10 * p + 408) (m := 410 * (p + 1)) (by omega) 2
    calc KS * (10 * p + 408) ^ 2 ≤ KS * (410 * (p + 1)) ^ 2 := Nat.mul_le_mul_left _ h1
      _ = KS * (168100 * (p + 1) ^ 2) := by
          rw [mul_pow, show (410 : ℕ) ^ 2 = 168100 by norm_num]
  have hC1 : 58 * (KS * 168100) ≤ 2 ^ (Ktot + 24) := by
    have h2 : 58 * (KS * 168100) ≤ 58 * (Ktot * 168100) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hKSle)
    have h3 : 58 * (Ktot * 168100) ≤ (58 * 168100) * Ktot := le_of_eq (by ac_rfl)
    have h4 : (58 * 168100) * Ktot ≤ 2 ^ 24 * Ktot :=
      Nat.mul_le_mul_right _ (by norm_num)
    have h5 : 2 ^ 24 * Ktot ≤ 2 ^ (Ktot + 24) := by
      calc 2 ^ 24 * Ktot ≤ 2 ^ 24 * 2 ^ Ktot :=
            Nat.mul_le_mul_left _ (le_of_lt (Nat.lt_two_pow_self (n := Ktot)))
        _ = 2 ^ (Ktot + 24) := by
            rw [← pow_add]
            exact congrArg (fun e => 2 ^ e) (Nat.add_comm 24 Ktot)
    exact le_trans h2 (le_trans h3 (le_trans h4 h5))
  have hpart1 : 58 * SB ≤ (t + 1) * (p + 1) ^ Kfin := by
    have hb : 2 ≤ p + 1 := by omega
    have h1 : 58 * SB ≤ 58 * (KS * (168100 * (p + 1) ^ 2)) := Nat.mul_le_mul_left _ hSB1
    have h2 : 58 * (KS * (168100 * (p + 1) ^ 2)) = (58 * (KS * 168100)) * (p + 1) ^ 2 := by ac_rfl
    have h3 : (58 * (KS * 168100)) * (p + 1) ^ 2 ≤ (p + 1) ^ Kfin :=
      const_mul_pow_le (c := Ktot + 24) (m := 2) (e := Kfin) hb hC1 (by rw [hKfin]; omega)
    have h4 : (p + 1) ^ Kfin ≤ (t + 1) * (p + 1) ^ Kfin := by
      calc (p + 1) ^ Kfin = 1 * (p + 1) ^ Kfin := (Nat.one_mul _).symm
        _ ≤ (t + 1) * (p + 1) ^ Kfin := Nat.mul_le_mul_right _ (by omega)
    exact le_trans h1 (le_trans (le_of_eq h2) (le_trans h3 h4))
  have hC2 : 58 * (Kp * 101 ^ Kp) ≤ 2 ^ (8 * Kp + 6) := by
    have h1 : 101 ^ Kp ≤ 128 ^ Kp := Nat.pow_le_pow_left (by norm_num) Kp
    have h2 : 58 * Kp ≤ 2 ^ 6 * 2 ^ Kp := by
      calc 58 * Kp ≤ 64 * Kp := Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ 64 * 2 ^ Kp := Nat.mul_le_mul_left _ (le_of_lt (Nat.lt_two_pow_self (n := Kp)))
        _ = 2 ^ 6 * 2 ^ Kp := by norm_num
    have h3 : (2 ^ 6 * 2 ^ Kp) * 128 ^ Kp = 2 ^ 6 * (2 ^ Kp * 128 ^ Kp) := by ac_rfl
    have h4 : 2 ^ 6 * (2 ^ Kp * 128 ^ Kp) = 2 ^ 6 * (2 ^ Kp * (2 ^ 7) ^ Kp) := by
      rw [show (128 : ℕ) = 2 ^ 7 by norm_num]
    have h5 : 2 ^ 6 * (2 ^ Kp * (2 ^ 7) ^ Kp) = 2 ^ 6 * 2 ^ (Kp + 7 * Kp) := by
      rw [← pow_mul, ← pow_add]
    have h6 : 2 ^ 6 * 2 ^ (Kp + 7 * Kp) = 2 ^ (8 * Kp + 6) := by
      rw [← pow_add]
      congr 1
      omega
    calc 58 * (Kp * 101 ^ Kp) = (58 * Kp) * 101 ^ Kp := by ac_rfl
      _ ≤ (2 ^ 6 * 2 ^ Kp) * 128 ^ Kp := Nat.mul_le_mul h2 h1
      _ = 2 ^ 6 * (2 ^ Kp * 128 ^ Kp) := h3
      _ = 2 ^ 6 * (2 ^ Kp * (2 ^ 7) ^ Kp) := h4
      _ = 2 ^ 6 * 2 ^ (Kp + 7 * Kp) := h5
      _ = 2 ^ (8 * Kp + 6) := h6
  have hpart2 : 58 * (Kp * (auPrec p + 1) ^ Kp) ≤ (t + 1) * (p + 1) ^ Kfin := by
    have hb : 2 ≤ p + 1 := by omega
    have hpre : auPrec p + 1 = 3 * p + 101 := by simp only [auPrec]
    rw [hpre]
    have h1 : (3 * p + 101) ^ Kp ≤ 101 ^ Kp * (p + 1) ^ Kp := by
      calc (3 * p + 101) ^ Kp ≤ (101 * (p + 1)) ^ Kp :=
            Nat.pow_le_pow_left (by omega) Kp
        _ = 101 ^ Kp * (p + 1) ^ Kp := by rw [mul_pow]
    have h2 : 58 * (Kp * (101 ^ Kp * (p + 1) ^ Kp))
        = (58 * (Kp * 101 ^ Kp)) * (p + 1) ^ Kp := by ac_rfl
    have h3 : (58 * (Kp * 101 ^ Kp)) * (p + 1) ^ Kp ≤ (p + 1) ^ Kfin :=
      const_mul_pow_le (c := 8 * Kp + 6) (m := Kp) (e := Kfin) hb hC2 (by rw [hKfin]; omega)
    have h4 : (p + 1) ^ Kfin ≤ (t + 1) * (p + 1) ^ Kfin := by
      calc (p + 1) ^ Kfin = 1 * (p + 1) ^ Kfin := (Nat.one_mul _).symm
        _ ≤ (t + 1) * (p + 1) ^ Kfin := Nat.mul_le_mul_right _ (by omega)
    calc 58 * (Kp * (3 * p + 101) ^ Kp)
        ≤ 58 * (Kp * (101 ^ Kp * (p + 1) ^ Kp)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ = (58 * (Kp * 101 ^ Kp)) * (p + 1) ^ Kp := h2
      _ ≤ (p + 1) ^ Kfin := h3
      _ ≤ (t + 1) * (p + 1) ^ Kfin := h4
  have hC3 : 58 * (Krc * (2 * 418)) ≤ 2 ^ (Ktot + 18) := by
    have h1 : 58 * (Krc * (2 * 418)) ≤ 58 * ((2 * Ktot) * (2 * 418)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hKrc_le)
    have h2 : 58 * ((2 * Ktot) * (2 * 418)) = (58 * (2 * 418)) * (2 * Ktot) := by ac_rfl
    have h3 : (58 * (2 * 418)) * (2 * Ktot) ≤ 2 ^ 17 * (2 * Ktot) :=
      Nat.mul_le_mul_right _ (by norm_num)
    have h4 : 2 ^ 17 * (2 * Ktot) = (2 ^ 17 * 2) * Ktot := by ac_rfl
    have h5 : (2 ^ 17 * 2) * Ktot = 2 ^ 18 * Ktot := by rw [← pow_succ]
    have h6 : 2 ^ 18 * Ktot ≤ 2 ^ 18 * 2 ^ Ktot :=
      Nat.mul_le_mul_left _ (le_of_lt (Nat.lt_two_pow_self (n := Ktot)))
    have h7 : 2 ^ 18 * 2 ^ Ktot = 2 ^ (Ktot + 18) := by
      rw [← pow_add]
      exact congrArg (fun e => 2 ^ e) (Nat.add_comm 18 Ktot)
    exact le_trans h1 (le_trans (le_of_eq h2) (le_trans h3 (le_trans (le_of_eq h4) (le_trans (le_of_eq h5) (le_trans h6 (le_of_eq h7))))))
  have hpart3 : 58 * (Krc * (t + 2) * (auSZ p + p + 3)) ≤ (t + 1) * (p + 1) ^ Kfin := by
    have hb : 2 ≤ p + 1 := by omega
    have h1 : auSZ p + p + 3 ≤ 418 * (p + 1) := by simp only [auSZ]; omega
    have h2 : t + 2 ≤ 2 * (t + 1) := by omega
    have hpc : (58 * (Krc * (2 * 418))) * (p + 1) ≤ (p + 1) ^ (Kfin - 1) := by
      have h0 := const_mul_pow_le (c := Ktot + 18) (m := 1) (e := Kfin - 1) hb hC3
        (by rw [hKfin]; omega)
      simpa only [pow_one] using h0
    have h4 : (58 * (Krc * (2 * 418))) * (t + 1) * (p + 1) ≤ (t + 1) * (p + 1) ^ Kfin := by
      have e : (58 * (Krc * (2 * 418))) * (t + 1) * (p + 1)
          = (t + 1) * ((58 * (Krc * (2 * 418))) * (p + 1)) := by ac_rfl
      rw [e]
      calc (t + 1) * ((58 * (Krc * (2 * 418))) * (p + 1))
          ≤ (t + 1) * (p + 1) ^ (Kfin - 1) := Nat.mul_le_mul_left _ hpc
        _ ≤ (t + 1) * (p + 1) ^ Kfin :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (n := p + 1) (i := Kfin - 1)
              (j := Kfin) (by omega) (by omega))
    have e1 : (t + 2) * (auSZ p + p + 3) ≤ (2 * (t + 1)) * (418 * (p + 1)) :=
      Nat.mul_le_mul h2 h1
    have e2 : 58 * (Krc * (t + 2) * (auSZ p + p + 3))
        = (58 * Krc) * ((t + 2) * (auSZ p + p + 3)) := by ring
    have e3 : (58 * Krc) * ((2 * (t + 1)) * (418 * (p + 1)))
        = (58 * (Krc * (2 * 418))) * (t + 1) * (p + 1) := by ring
    calc 58 * (Krc * (t + 2) * (auSZ p + p + 3))
        = (58 * Krc) * ((t + 2) * (auSZ p + p + 3)) := e2
      _ ≤ (58 * Krc) * ((2 * (t + 1)) * (418 * (p + 1))) := Nat.mul_le_mul_left _ e1
      _ = (58 * (Krc * (2 * 418))) * (t + 1) * (p + 1) := e3
      _ ≤ (t + 1) * (p + 1) ^ Kfin := h4
  have he : 58 * CBIG = 58 * SB + 58 * (Kp * (auPrec p + 1) ^ Kp) + 58 * CBt := by
    rw [hCBIG, Nat.mul_add, Nat.mul_add]
  have htot : 58 * CBIG ≤ Kfin * (t + 1) * (p + 1) ^ Kfin := by
    rw [he]
    have hsum : 58 * SB + 58 * (Kp * (auPrec p + 1) ^ Kp) + 58 * CBt
        ≤ 3 * ((t + 1) * (p + 1) ^ Kfin) := by
      have h := Nat.add_le_add (Nat.add_le_add hpart1 hpart2) hpart3
      omega
    calc 58 * SB + 58 * (Kp * (auPrec p + 1) ^ Kp) + 58 * CBt
        ≤ 3 * ((t + 1) * (p + 1) ^ Kfin) := hsum
      _ ≤ Kfin * ((t + 1) * (p + 1) ^ Kfin) := by
          have h3 : 3 ≤ Kfin := by rw [hKfin]; omega
          have h4 := Nat.mul_le_mul_left ((t + 1) * (p + 1) ^ Kfin) h3
          rw [Nat.mul_comm 3 ((t + 1) * (p + 1) ^ Kfin),
            Nat.mul_comm Kfin ((t + 1) * (p + 1) ^ Kfin)]
          exact h4
      _ = Kfin * (t + 1) * (p + 1) ^ Kfin := (Nat.mul_assoc Kfin (t + 1) ((p + 1) ^ Kfin)).symm

  -- the chain of 58 library steps
  have s1 : Pipe main (pickProg 0) [Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((p : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 0) (by simp) (v := Val.int ((p : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 0) (by simp) (by simp) (vsz_mem_le4 (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s2 : Pipe main sqrtProg [Val.int ((p : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (sqz p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.unOp (hSqrt main) (a := (p : ℤ)) (by positivity)))
      (hleSB (au_le_sq hKsqrt (isz_p_le p)))
  have s3 : Pipe main (pushProg (Val.int (1))) [Val.int (sqz p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (1), Val.int (sqz p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pushOnAny (T := [Val.int (sqz p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (hPush main (Val.int (1))))
      (hleSB (au_le_one hKpush (vszVI (isz_small_le p 1 (by norm_num)))))
  have s4 : Pipe main addProg [Val.int (1), Val.int (sqz p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (s1z p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hAdd main) (a := 1) (b := sqz p) trivial))
      (hleSB (au_le_two hKadd (isz_small_le p 1 (by norm_num)) (isz_sqz_le p)))
  have s5 : Pipe main (pickProg 2) [Val.int (s1z p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((α : ℤ)), Val.int (s1z p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (s1z p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 2) (by simp) (v := Val.int ((α : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 2) (by simp) (by simp) (vsz_mem_le5 (vszVI (isz_s1z_le p)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s6 : Pipe main mulProg [Val.int ((α : ℤ)), Val.int (s1z p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (mz p α), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hMul main) (a := (α : ℤ)) (b := s1z p) trivial))
      (hleSB (au_le_mul_auPreKit hKmul (isz_alpha_le p α hαp) (isz_s1z_le p)))
  have s7 : Pipe main (pickProg 3) [Val.int (mz p α), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((s : ℤ)), Val.int (mz p α), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (mz p α), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 3) (by simp) (v := Val.int ((s : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 3) (by simp) (by simp) (vsz_mem_le5 (vszVI (isz_mz_le p α hαp)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s8 : Pipe main (rollProg 1) [Val.int ((s : ℤ)), Val.int (mz p α), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (mz p α), Val.int ((s : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.roll main hRoll (A := [Val.int ((s : ℤ)), Val.int (mz p α), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 1) (by simp))
      (hleSB (au_le_roll hKroll (k := 1) (by simp) (by simp) (vsz_mem_le6 (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_mz_le p α hαp)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s9 : Pipe main addProg [Val.int (mz p α), Val.int ((s : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (X1z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hAdd main) (a := mz p α) (b := (s : ℤ)) trivial))
      (hleSB (au_le_two hKadd (isz_mz_le p α hαp) (isz_s_le p s t hst htp)))
  have s10 : Pipe main (pushProg (Val.int (1))) [Val.int (X1z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (1), Val.int (X1z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pushOnAny (T := [Val.int (X1z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (hPush main (Val.int (1))))
      (hleSB (au_le_one hKpush (vszVI (isz_small_le p 1 (by norm_num)))))
  have s11 : Pipe main (rollProg 1) [Val.int (1), Val.int (X1z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (X1z p α s), Val.int (1), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.roll main hRoll (A := [Val.int (1), Val.int (X1z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 1) (by simp))
      (hleSB (au_le_roll hKroll (k := 1) (by simp) (by simp) (vsz_mem_le6 (vszVI (isz_small_le p 1 (by norm_num))) (vszVI (isz_X1z_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s12 : Pipe main subProg [Val.int (X1z p α s), Val.int (1), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (X2z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hSub main) (a := X1z p α s) (b := 1) trivial))
      (hleSB (au_le_two hKsub (isz_X1z_le p α s hαp hs2) (isz_small_le p 1 (by norm_num))))
  have s13 : Pipe main (pickProg 3) [Val.int (X2z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((s : ℤ)), Val.int (X2z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (X2z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 3) (by simp) (v := Val.int ((s : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 3) (by simp) (by simp) (vsz_mem_le5 (vszVI (isz_X2z_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s14 : Pipe main (rollProg 1) [Val.int ((s : ℤ)), Val.int (X2z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (X2z p α s), Val.int ((s : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.roll main hRoll (A := [Val.int ((s : ℤ)), Val.int (X2z p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 1) (by simp))
      (hleSB (au_le_roll hKroll (k := 1) (by simp) (by simp) (vsz_mem_le6 (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_X2z_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s15 : Pipe main tdivProg [Val.int (X2z p α s), Val.int ((s : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (qz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hTdiv main) (a := X2z p α s) (b := (s : ℤ)) (by omega)))
      (hleSB (au_le_mul_auPreKit hKtdiv (isz_X2z_le p α s hαp hs2) (isz_s_le p s t hst htp)))
  have s16 : Pipe main (pickProg 3) [Val.int (qz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((s : ℤ)), Val.int (qz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (qz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 3) (by simp) (v := Val.int ((s : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 3) (by simp) (by simp) (vsz_mem_le5 (vszVI (isz_qz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s17 : Pipe main mulProg [Val.int ((s : ℤ)), Val.int (qz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hMul main) (a := (s : ℤ)) (b := qz p α s) trivial))
      (hleSB (au_le_mul_auPreKit hKmul (isz_s_le p s t hst htp) (isz_qz_le p α s hαp hs2)))
  have s18 : Pipe main (pickProg 1) [Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((p : ℤ)), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 1) (by simp) (v := Val.int ((p : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 1) (by simp) (by simp) (vsz_mem_le5 (vszVI (isz_szq_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s19 : Pipe main sqrtProg [Val.int ((p : ℤ)), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (sqz p), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (szq p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.unOp (hSqrt main) (a := (p : ℤ)) (by positivity)))
      (hleSB (au_le_sq hKsqrt (isz_p_le p)))
  have s20 : Pipe main (pushProg (Val.int (1))) [Val.int (sqz p), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (1), Val.int (sqz p), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pushOnAny (T := [Val.int (sqz p), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (hPush main (Val.int (1))))
      (hleSB (au_le_one hKpush (vszVI (isz_small_le p 1 (by norm_num)))))
  have s21 : Pipe main addProg [Val.int (1), Val.int (sqz p), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (s1z p), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (szq p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hAdd main) (a := 1) (b := sqz p) trivial))
      (hleSB (au_le_two hKadd (isz_small_le p 1 (by norm_num)) (isz_sqz_le p)))
  have s22 : Pipe main (pickProg 3) [Val.int (s1z p), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((α : ℤ)), Val.int (s1z p), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (s1z p), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 3) (by simp) (v := Val.int ((α : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 3) (by simp) (by simp) (vsz_mem_le6 (vszVI (isz_s1z_le p)) (vszVI (isz_szq_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s23 : Pipe main mulProg [Val.int ((α : ℤ)), Val.int (s1z p), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (mz p α), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (szq p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hMul main) (a := (α : ℤ)) (b := s1z p) trivial))
      (hleSB (au_le_mul_auPreKit hKmul (isz_alpha_le p α hαp) (isz_s1z_le p)))
  have s24 : Pipe main (rollProg 1) [Val.int (mz p α), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (szq p α s), Val.int (mz p α), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.roll main hRoll (A := [Val.int (mz p α), Val.int (szq p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 1) (by simp))
      (hleSB (au_le_roll hKroll (k := 1) (by simp) (by simp) (vsz_mem_le6 (vszVI (isz_mz_le p α hαp)) (vszVI (isz_szq_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s25 : Pipe main subProg [Val.int (szq p α s), Val.int (mz p α), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hSub main) (a := szq p α s) (b := mz p α) trivial))
      (hleSB (au_le_two hKsub (isz_szq_le p α s hαp hs2) (isz_mz_le p α hαp)))
  have s26 : Pipe main (pickProg 0) [Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 0) (by simp) (v := Val.int (offz p α s)) (by rfl))
      (hleSB (au_le_roll hKpick (k := 0) (by simp) (by simp) (vsz_mem_le5 (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s27 : Pipe main (pickProg 4) [Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((s : ℤ)), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 4) (by simp) (v := Val.int ((s : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 4) (by simp) (by simp) (vsz_mem_le6 (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s28 : Pipe main (pushProg (Val.int (2))) [Val.int ((s : ℤ)), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (2), Val.int ((s : ℤ)), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pushOnAny (T := [Val.int ((s : ℤ)), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (hPush main (Val.int (2))))
      (hleSB (au_le_one hKpush (vszVI (isz_small_le p 2 (by norm_num)))))
  have s29 : Pipe main mulProg [Val.int (2), Val.int ((s : ℤ)), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (offz p α s),Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hMul main) (a := 2) (b := (s : ℤ)) trivial))
      (hleSB (au_le_mul_auPreKit hKmul (isz_small_le p 2 (by norm_num)) (isz_s_le p s t hst htp)))
  have s30 : Pipe main (pickProg 3) [Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((p : ℤ)), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 3) (by simp) (v := Val.int ((p : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 3) (by simp) (by simp) (vsz_mem_le7 (vszVI (isz_t2sz_le p s hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s31 : Pipe main sqrtProg [Val.int ((p : ℤ)), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (sqz p), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (t2sz s),Val.int (offz p α s),Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.unOp (hSqrt main) (a := (p : ℤ)) (by positivity)))
      (hleSB (au_le_sq hKsqrt (isz_p_le p)))
  have s32 : Pipe main (pushProg (Val.int (1))) [Val.int (sqz p), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (1), Val.int (sqz p), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pushOnAny (T := [Val.int (sqz p), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (hPush main (Val.int (1))))
      (hleSB (au_le_one hKpush (vszVI (isz_small_le p 1 (by norm_num)))))
  have s33 : Pipe main addProg [Val.int (1), Val.int (sqz p), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (s1z p), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (t2sz s),Val.int (offz p α s),Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hAdd main) (a := 1) (b := sqz p) trivial))
      (hleSB (au_le_two hKadd (isz_small_le p 1 (by norm_num)) (isz_sqz_le p)))
  have s34 : Pipe main (pickProg 5) [Val.int (s1z p), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((α : ℤ)), Val.int (s1z p), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (s1z p), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 5) (by simp) (v := Val.int ((α : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 5) (by simp) (by simp) (vsz_mem_le8 (vszVI (isz_s1z_le p)) (vszVI (isz_t2sz_le p s hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s35 : Pipe main mulProg [Val.int ((α : ℤ)), Val.int (s1z p), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (mz p α), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (t2sz s),Val.int (offz p α s),Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hMul main) (a := (α : ℤ)) (b := s1z p) trivial))
      (hleSB (au_le_mul_auPreKit hKmul (isz_alpha_le p α hαp) (isz_s1z_le p)))
  have s36 : Pipe main (pushProg (Val.int (2))) [Val.int (mz p α), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (2), Val.int (mz p α), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pushOnAny (T := [Val.int (mz p α), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (hPush main (Val.int (2))))
      (hleSB (au_le_one hKpush (vszVI (isz_small_le p 2 (by norm_num)))))
  have s37 : Pipe main mulProg [Val.int (2), Val.int (mz p α), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (t2mz p α), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (t2sz s),Val.int (offz p α s),Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hMul main) (a := 2) (b := mz p α) trivial))
      (hleSB (au_le_mul_auPreKit hKmul (isz_small_le p 2 (by norm_num)) (isz_mz_le p α hαp)))
  have s38 : Pipe main addProg [Val.int (t2mz p α), Val.int (t2sz s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (Z1z p α s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (offz p α s),Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hAdd main) (a := t2mz p α) (b := t2sz s) trivial))
      (hleSB (au_le_two hKadd (isz_t2mz_le p α hαp) (isz_t2sz_le p s hs2)))
  have s39 : Pipe main (rollProg 1) [Val.int (Z1z p α s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (offz p α s), Val.int (Z1z p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.roll main hRoll (A := [Val.int (Z1z p α s), Val.int (offz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 1) (by simp))
      (hleSB (au_le_roll hKroll (k := 1) (by simp) (by simp) (vsz_mem_le7 (vszVI (isz_Z1z_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s40 : Pipe main addProg [Val.int (offz p α s), Val.int (Z1z p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (Yz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hAdd main) (a := offz p α s) (b := Z1z p α s) trivial))
      (hleSB (au_le_two hKadd (isz_offz_le p α s hαp hs2) (isz_Z1z_le p α s hαp hs2)))
  have s41 : Pipe main (pickProg 4) [Val.int (Yz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((s : ℤ)), Val.int (Yz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (Yz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 4) (by simp) (v := Val.int ((s : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 4) (by simp) (by simp) (vsz_mem_le6 (vszVI (isz_Yz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s42 : Pipe main (rollProg 1) [Val.int ((s : ℤ)), Val.int (Yz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (Yz p α s), Val.int ((s : ℤ)), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.roll main hRoll (A := [Val.int ((s : ℤ)), Val.int (Yz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 1) (by simp))
      (hleSB (au_le_roll hKroll (k := 1) (by simp) (by simp) (vsz_mem_le7 (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_Yz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s43 : Pipe main tdivProg [Val.int (Yz p α s), Val.int ((s : ℤ)), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hTdiv main) (a := Yz p α s) (b := (s : ℤ)) (by omega)))
      (hleSB (au_le_mul_auPreKit hKtdiv (isz_Yz_le p α s hαp hs2) (isz_s_le p s t hst htp)))
  have s44 : Pipe main (pickProg 2) [Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((p : ℤ)), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 2) (by simp) (v := Val.int ((p : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 2) (by simp) (by simp) (vsz_mem_le6 (vszVI (isz_copz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s45 : Pipe main (pushProg (Val.int (3))) [Val.int ((p : ℤ)), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (3), Val.int ((p : ℤ)), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pushOnAny (T := [Val.int ((p : ℤ)), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (hPush main (Val.int (3))))
      (hleSB (au_le_one hKpush (vszVI (isz_small_le p 3 (by norm_num)))))
  have s46 : Pipe main mulProg [Val.int (3), Val.int ((p : ℤ)), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (P3z p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (copz p α s),Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hMul main) (a := 3) (b := (p : ℤ)) trivial))
      (hleSB (au_le_mul_auPreKit hKmul (isz_small_le p 3 (by norm_num)) (isz_p_le p)))
  have s47 : Pipe main (pushProg (Val.int (100))) [Val.int (P3z p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (100), Val.int (P3z p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.pushOnAny (T := [Val.int (P3z p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (hPush main (Val.int (100))))
      (hleSB (au_le_one hKpush (vszVI (isz_small_le p 100 (by norm_num)))))
  have s48 : Pipe main addProg [Val.int (100), Val.int (P3z p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (((auPrec p : ℕ) : ℤ)), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.rw (Pipe.le (Pipe.appendTail [Val.int (copz p α s),Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.binOp (hAdd main) (a := 100) (b := P3z p) trivial))
      (hleSB (au_le_two hKadd (isz_small_le p 100 (by norm_num)) (isz_P3z_le p))))
      (by
        show [Val.int (precz p)] ++ [Val.int (copz p α s),Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] = [Val.int ((auPrec p : ℕ) : ℤ)] ++ [Val.int (copz p α s),Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))]
        rw [precz_eq p])
  have s49 : Pipe main piProg [Val.int (((auPrec p : ℕ) : ℤ)), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] CBIG := Pipe.le (Pipe.appendTail [Val.int (copz p α s),Val.int (offz p α s),Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ))] (Pipe.ofWordR (piSpec main (auPrec p) h100))) hlePi
  have s50 : Pipe main (rollProg 6) [Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ))] CBIG := Pipe.le (Pipe.roll main hRoll (A := [Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))]) (k := 6) (by simp))
      (hleSB (au_le_roll hKroll (k := 6) (by simp) (by simp) (vsz_mem_le7 (vszVI (isz_auPi_le p)) (vszVI (isz_copz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)))))
  have s51 : Pipe main (rollProg 6) [Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ))] [Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ))] CBIG := Pipe.le (Pipe.roll main hRoll (A := [Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ))]) (k := 6) (by simp))
      (hleSB (au_le_roll hKroll (k := 6) (by simp) (by simp) (vsz_mem_le7 (vszVI (isz_t_le p t htp)) (vszVI (isz_auPi_le p)) (vszVI (isz_copz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)))))
  have s52 : Pipe main (rollProg 6) [Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ))] [Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ))] CBIG := Pipe.le (Pipe.roll main hRoll (A := [Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ)), Val.int ((α : ℤ))]) (k := 6) (by simp))
      (hleSB (au_le_roll hKroll (k := 6) (by simp) (by simp) (vsz_mem_le7 (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)) (vszVI (isz_auPi_le p)) (vszVI (isz_copz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)))))
  have s53 : Pipe main (rollProg 6) [Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ))] [Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)] CBIG := Pipe.le (Pipe.roll main hRoll (A := [Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s), Val.int ((p : ℤ))]) (k := 6) (by simp))
      (hleSB (au_le_roll hKroll (k := 6) (by simp) (by simp) (vsz_mem_le7 (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)) (vszVI (isz_auPi_le p)) (vszVI (isz_copz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)) (vszVI (isz_p_le p)))))
  have s54 : Pipe main (pickProg 3) [Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)] [Val.int ((t : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)]) (k := 3) (by simp) (v := Val.int ((t : ℤ))) (by rfl))
      (hleSB (au_le_roll hKpick (k := 3) (by simp) (by simp) (vsz_mem_le7 (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)) (vszVI (isz_auPi_le p)) (vszVI (isz_copz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)))))
  have s55 : Pipe main (pickProg 5) [Val.int ((t : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)] [Val.int (auPi p), Val.int ((t : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)] CBIG := Pipe.le (Pipe.pickAt main hPick (A := [Val.int ((t : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)]) (k := 5) (by simp) (v := Val.int (auPi p)) (by rfl))
      (hleSB (au_le_roll hKpick (k := 5) (by simp) (by simp) (vsz_mem_le8 (vszVI (isz_t_le p t htp)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)) (vszVI (isz_auPi_le p)) (vszVI (isz_copz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)))))
  have s56 : Pipe main (rollProg 1) [Val.int (auPi p), Val.int ((t : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)] [Val.int ((t : ℤ)), Val.int (auPi p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)] CBIG := Pipe.le (Pipe.roll main hRoll (A := [Val.int (auPi p), Val.int ((t : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)]) (k := 1) (by simp))
      (hleSB (au_le_roll hKroll (k := 1) (by simp) (by simp) (vsz_mem_le9 (vszVI (isz_auPi_le p)) (vszVI (isz_t_le p t htp)) (vszVI (isz_p_le p)) (vszVI (isz_alpha_le p α hαp)) (vszVI (isz_s_le p s t hst htp)) (vszVI (isz_t_le p t htp)) (vszVI (isz_auPi_le p)) (vszVI (isz_copz_le p α s hαp hs2)) (vszVI (isz_offz_le p α s hαp hs2)))))
  have s57 : Pipe main replProg [Val.int ((t : ℤ)), Val.int (auPi p), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)] [ofList (List.replicate t (Val.int (auPi p))), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)] CBIG := Pipe.le (Pipe.appendTail [Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ)),Val.int (auPi p),Val.int (copz p α s),Val.int (offz p α s)] (Pipe.replicate main hRepl)) hleTrepl
  have s58 : Pipe main enumProg [ofList (List.replicate t (Val.int (auPi p))), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)] [ofList ((List.range (List.replicate t (Val.int (auPi p))).length).map fun (i : ℕ) => Val.cons (Val.int (i : ℤ)) ((List.replicate t (Val.int (auPi p))).getD i Val.nil)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ)), Val.int (auPi p), Val.int (copz p α s), Val.int (offz p α s)] CBIG := Pipe.le (Pipe.appendTail [Val.int ((p : ℤ)),Val.int ((α : ℤ)),Val.int ((s : ℤ)),Val.int ((t : ℤ)),Val.int (auPi p),Val.int (copz p α s),Val.int (offz p α s)] (Pipe.enumerate main hEnum)) hleTenum

  -- composition of the 58 steps
  have g1 : Pipe main (pickProg 0) [Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] [Val.int ((p : ℤ)), Val.int ((p : ℤ)), Val.int ((α : ℤ)), Val.int ((s : ℤ)), Val.int ((t : ℤ))] (1 * CBIG) := by rw [Nat.one_mul]; exact s1
  have g2 := hstep g1 s2
  have g3 := hstep g2 s3
  have g4 := hstep g3 s4
  have g5 := hstep g4 s5
  have g6 := hstep g5 s6
  have g7 := hstep g6 s7
  have g8 := hstep g7 s8
  have g9 := hstep g8 s9
  have g10 := hstep g9 s10
  have g11 := hstep g10 s11
  have g12 := hstep g11 s12
  have g13 := hstep g12 s13
  have g14 := hstep g13 s14
  have g15 := hstep g14 s15
  have g16 := hstep g15 s16
  have g17 := hstep g16 s17
  have g18 := hstep g17 s18
  have g19 := hstep g18 s19
  have g20 := hstep g19 s20
  have g21 := hstep g20 s21
  have g22 := hstep g21 s22
  have g23 := hstep g22 s23
  have g24 := hstep g23 s24
  have g25 := hstep g24 s25
  have g26 := hstep g25 s26
  have g27 := hstep g26 s27
  have g28 := hstep g27 s28
  have g29 := hstep g28 s29
  have g30 := hstep g29 s30
  have g31 := hstep g30 s31
  have g32 := hstep g31 s32
  have g33 := hstep g32 s33
  have g34 := hstep g33 s34
  have g35 := hstep g34 s35
  have g36 := hstep g35 s36
  have g37 := hstep g36 s37
  have g38 := hstep g37 s38
  have g39 := hstep g38 s39
  have g40 := hstep g39 s40
  have g41 := hstep g40 s41
  have g42 := hstep g41 s42
  have g43 := hstep g42 s43
  have g44 := hstep g43 s44
  have g45 := hstep g44 s45
  have g46 := hstep g45 s46
  have g47 := hstep g46 s47
  have g48 := hstep g47 s48
  have g49 := hstep g48 s49
  have g50 := hstep g49 s50
  have g51 := hstep g50 s51
  have g52 := hstep g51 s52
  have g53 := hstep g52 s53
  have g54 := hstep g53 s54
  have g55 := hstep g54 s55
  have g56 := hstep g55 s56
  have g57 := hstep g56 s57
  have gN := hstep g57 s58
  refine Pipe.rw (Pipe.le gN htot) ?_
  rw [enumerate_replicate t (Val.int (auPi p)), copz_eq p α s hα1 hs1, offz_eq p α s hα1 hs1]
  rfl

end Work.Resample
