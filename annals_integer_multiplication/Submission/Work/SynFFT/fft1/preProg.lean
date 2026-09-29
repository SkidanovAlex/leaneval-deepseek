import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.fft1.stepKit

/-!
# The prologue of the slice word
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.SynFFT

open HvdH
open Work.SynFFT.MrgKit
open Work.SynFFT.Fft1Kit

local infixl:68 " ;;; " => HvdH.Cmd.seq

theorem preProg (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (X : HvdH.Val) (k : ℕ) (sgn : ℤ)
      (r p : ℕ) (rest : List HvdH.Val) (D : ℕ),
      (sgn = 1 ∨ sgn = -1) →
      k ≤ Nat.clog 2 (2 * r) →
      K * (HvdH.vsz X + HvdH.isz (k : ℤ) + HvdH.isz (r : ℤ) + HvdH.isz (p : ℤ) +
            Nat.clog 2 (2 * r) + 2 ^ k + k + 1) ≤ D →
      HvdH.WordR main prog
        (fun vs => vs = X :: HvdH.Val.int (k : ℤ) :: HvdH.Val.int sgn :: HvdH.Val.int (r : ℤ) ::
          HvdH.Val.int (p : ℤ) :: rest)
        (fun _ out => out = HvdH.ofList (List.replicate k HvdH.Val.nil) :: X ::
          HvdH.Val.int ((2 ^ k : ℕ) : ℤ) :: HvdH.Val.int ((Nat.clog 2 (2 * r) - k : ℕ) : ℤ) ::
          HvdH.Val.int sgn :: HvdH.Val.int (r : ℤ) :: HvdH.Val.int (p : ℤ) ::
          HvdH.Val.int (k : ℤ) :: rest)
        (fun _ => D) := by
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  obtain ⟨addP, Ka, hadd⟩ := hi.add
  obtain ⟨subP, Ksb, hsub⟩ := hi.sub
  obtain ⟨shrP, Kc, hclog⟩ := hi.clog2
  obtain ⟨powP, Kpw, hpow⟩ := hi.pow2
  obtain ⟨repP, Krp, hrep⟩ := hl.replicate
  refine ⟨pickP 1 ;;; powP ;;; pickP 4 ;;; dupP ;;; addP ;;; shrP ;;; pickP 3 ;;; swapP ;;; subP ;;;
    pushP (.nil) ;;; pickP 4 ;;; repP ;;; rollP 7 ;;; rollP 7 ;;; rollP 7 ;;; rollP 4 ;;; rollP 5 ;;;
    rollP 6 ;;; rollP 6,
    100000 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr + 1), ?_⟩
  intro main X k sgn r p rest D hsgn hkc hD
  set U : ℕ := vsz X + isz (k : ℤ) + isz (r : ℤ) + isz (p : ℤ) + Nat.clog 2 (2 * r) + 2 ^ k + k + 1
    with hU
  have hvX : 1 ≤ vsz X := one_le_vsz X
  have hisk : 2 ≤ isz (k : ℤ) := two_le_isz _
  have hisr : 2 ≤ isz (r : ℤ) := two_le_isz _
  have hisp : 2 ≤ isz (p : ℤ) := two_le_isz _
  have hsg : isz sgn = 3 := isz_of_sign hsgn
  have h2kp : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hU1 : 1 ≤ U := by rw [hU]; omega
  have h2kv : isz (((2 ^ k : ℕ)) : ℤ) ≤ U := by
    rw [isz_two_pow]
    nlinarith [hU, hvX, hisk, hisr, hisp, h2kp]
  have hcrv : isz ((Nat.clog 2 (2 * r) : ℕ) : ℤ) ≤ U := by
    have h1 : isz ((Nat.clog 2 (2 * r) : ℕ) : ℤ) ≤ Nat.clog 2 (2 * r) + 2 := isz_natCast_le _
    nlinarith [h1, hU, hvX, hisk, hisr, hisp, h2kp]
  have hcrkv : isz (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) ≤ U := by
    have h1 : isz (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) ≤ (Nat.clog 2 (2 * r) - k) + 2 :=
      isz_natCast_le _
    have h2 : Nat.clog 2 (2 * r) - k ≤ Nat.clog 2 (2 * r) := Nat.sub_le _ _
    nlinarith [h1, h2, hU, hvX, hisk, hisr, hisp, h2kp]
  have hrr : isz ((r : ℤ) + (r : ℤ)) ≤ U := by
    have h1 : isz (2 * (r : ℤ)) ≤ isz (r : ℤ) + 1 := isz_two_mul_le _
    rw [show ((r : ℤ) + (r : ℤ)) = 2 * (r : ℤ) by ring]
    nlinarith [h1, hU, hvX, hisk, hisp, h2kp]
  have hcrto : ((r : ℤ) + (r : ℤ)).toNat = 2 * r := by
    have h : ((r : ℤ) + (r : ℤ)) = ((2 * r : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]
  have hDv : vsz (ofList (List.replicate k (Val.nil))) ≤ U := by
    rw [vsz_ofList_replicate_nil]
    nlinarith [hU, hvX, hisk, hisr, hisp, h2kp]
  have h2keq : (2 : ℤ) ^ k = (((2 ^ k : ℕ)) : ℤ) := by push_cast; ring
  have hcast : ((Nat.clog 2 (2 * r) : ℕ) : ℤ) - (k : ℤ) =
      (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) := by
    rw [← Nat.cast_sub hkc]
  have s1 : WordR main (pickP 1)
      (fun vs => vs = X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (k : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (pickStep (hpick main) 1 _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s2 : WordR main powP
      (fun vs => vs = .int (k : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (pow2Step (hpow main) (k : ℤ) _ (by norm_num) _ ?_) rfl (fun out hout => by rw [hout, Int.toNat_natCast, h2keq]) le_rfl
    rw [Int.toNat_natCast]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s3 : WordR main (pickP 4)
      (fun vs => vs = .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (r : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (pickStep (hpick main) 4 _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s4 : WordR main dupP
      (fun vs => vs = .int (r : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (r : ℤ) :: .int (r : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (dupStep (hdup main) (.int (r : ℤ)) _ _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    rw [Work.SynFFT.MrgKit.vsz_int']
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s5 : WordR main addP
      (fun vs => vs = .int (r : ℤ) :: .int (r : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int ((r : ℤ) + (r : ℤ)) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (addStep (hadd main) (r : ℤ) (r : ℤ) _ _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s6 : WordR main shrP
      (fun vs => vs = .int ((r : ℤ) + (r : ℤ)) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (((Nat.clog 2 (2 * r) : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (clog2Step (hclog main) ((r : ℤ) + (r : ℤ)) _ (by norm_num) _ ?_) rfl (fun out hout => by rw [hout, hcrto]) le_rfl
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s7 : WordR main (pickP 3)
      (fun vs => vs = .int (((Nat.clog 2 (2 * r) : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (k : ℤ) :: .int (((Nat.clog 2 (2 * r) : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (pickStep (hpick main) 3 _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s8 : WordR main swapP
      (fun vs => vs = .int (k : ℤ) :: .int (((Nat.clog 2 (2 * r) : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (((Nat.clog 2 (2 * r) : ℕ)) : ℤ) :: .int (k : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (swapStep (hswap main) _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s9 : WordR main subP
      (fun vs => vs = .int (((Nat.clog 2 (2 * r) : ℕ)) : ℤ) :: .int (k : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (subStep (hsub main) ((Nat.clog 2 (2 * r) : ℕ) : ℤ) (k : ℤ) _ _ ?_) rfl (fun out hout => by rw [hout, hcast]) le_rfl
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s10 : WordR main (pushP (.nil))
      (fun vs => vs = .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .nil :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (pushStep (hpush main) (.nil) _ _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    rw [vsz_nil]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s11 : WordR main (pickP 4)
      (fun vs => vs = .nil :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (k : ℤ) :: .nil :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (pickStep (hpick main) 4 _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s12 : WordR main repP
      (fun vs => vs = .int (k : ℤ) :: .nil :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = ofList (List.replicate k (Val.nil)) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (replicateStep (hrep main) k (Val.nil) _ _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    rw [vsz_nil]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s13 : WordR main (rollP 7)
      (fun vs => vs = ofList (List.replicate k (Val.nil)) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 7 _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s14 : WordR main (rollP 7)
      (fun vs => vs = .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: rest)
      (fun _ out => out = .int (r : ℤ) :: .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 7 _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s15 : WordR main (rollP 7)
      (fun vs => vs = .int (r : ℤ) :: .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: .int sgn :: rest)
      (fun _ out => out = .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 7 _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s16 : WordR main (rollP 4)
      (fun vs => vs = .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: rest)
      (fun _ out => out = .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 4 _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s17 : WordR main (rollP 5)
      (fun vs => vs = .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: .int (((2 ^ k : ℕ)) : ℤ) :: X :: .int (k : ℤ) :: rest)
      (fun _ out => out = .int (((2 ^ k : ℕ)) : ℤ) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: X :: .int (k : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 5 _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s18 : WordR main (rollP 6)
      (fun vs => vs = .int (((2 ^ k : ℕ)) : ℤ) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: X :: .int (k : ℤ) :: rest)
      (fun _ out => out = X :: .int (((2 ^ k : ℕ)) : ℤ) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: .int (k : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 6 _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have s19 : WordR main (rollP 6)
      (fun vs => vs = X :: .int (((2 ^ k : ℕ)) : ℤ) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (List.replicate k (Val.nil)) :: .int (k : ℤ) :: rest)
      (fun _ out => out = ofList (List.replicate k (Val.nil)) :: X :: .int (((2 ^ k : ℕ)) : ℤ) :: .int (((Nat.clog 2 (2 * r) - k : ℕ)) : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: .int (k : ℤ) :: rest) (fun _ => 4096 * (Kp + Kpw + Kd + Ka + Ksb + Kc + Ksw + Kpv + Krp + Kr) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 6 _ (by simp) _ ?_) rfl (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', vsz_nil, vsz_ofList_replicate_nil, isz_one]
    nlinarith [hU, hvX, hisk, hisr, hisp, hsg, h2kv, hcrv, hcrkv, hrr, hDv, h2kp]
  have h12 := seqC hk.seq s1 s2
  have h123 := seqC hk.seq h12 s3
  have h1234 := seqC hk.seq h123 s4
  have h12345 := seqC hk.seq h1234 s5
  have h123456 := seqC hk.seq h12345 s6
  have h1234567 := seqC hk.seq h123456 s7
  have h12345678 := seqC hk.seq h1234567 s8
  have h123456789 := seqC hk.seq h12345678 s9
  have h12345678910 := seqC hk.seq h123456789 s10
  have h11 := seqC hk.seq h12345678910 s11
  have h12' := seqC hk.seq h11 s12
  have h13 := seqC hk.seq h12' s13
  have h14 := seqC hk.seq h13 s14
  have h15 := seqC hk.seq h14 s15
  have h16 := seqC hk.seq h15 s16
  have h17 := seqC hk.seq h16 s17
  have h18 := seqC hk.seq h17 s18
  have h19 := seqC hk.seq h18 s19
  exact WordR_weaken h19 (fun vs hvs => hvs) (fun vs out hvs hout => hout)
    (fun vs hvs => by nlinarith [hD, hU1])

end Work.SynFFT
