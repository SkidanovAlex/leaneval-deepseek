import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.fft1.stepKit

/-!
# Updating the level parameters below the data list

`X :: int m :: int sh :: rest ↦ X :: int (m/2) :: int (sh+1) :: rest`
by `roll 2; push 1; add; roll 2; push 1; swap; shrT 1; roll 2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH
open Work.SynFFT.MrgKit
open Work.SynFFT.Fft1Kit

local infixl:68 " ;;; " => HvdH.Cmd.seq

theorem updLvl (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (X : HvdH.Val) (m sh : ℕ)
      (rest : List HvdH.Val) (D : ℕ),
      K * (HvdH.vsz X + HvdH.isz (m : ℤ) + HvdH.isz (sh : ℤ) + 1) ≤ D →
      HvdH.WordR main prog
        (fun vs => vs = X :: HvdH.Val.int (m : ℤ) :: HvdH.Val.int (sh : ℤ) :: rest)
        (fun _ out => out = X :: HvdH.Val.int ((m / 2 : ℕ) : ℤ) ::
          HvdH.Val.int ((sh + 1 : ℕ) : ℤ) :: rest)
        (fun _ => D) := by
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  obtain ⟨addP, Ka, hadd⟩ := hi.add
  obtain ⟨shrP, Ksh, hshr⟩ := hi.shrT
  refine ⟨rollP 2 ;;; pushP (.int 1) ;;; addP ;;; rollP 2 ;;; pushP (.int 1) ;;; swapP ;;;
    shrP ;;; rollP 2, 8192 * (Kr + Kpv + Ksw + Ka + Ksh + 1), ?_⟩
  intro main X m sh rest D hD
  set U : ℕ := vsz X + isz (m : ℤ) + isz (sh : ℤ) + 1 with hU
  have hvX : 1 ≤ vsz X := one_le_vsz X
  have him : 2 ≤ isz (m : ℤ) := two_le_isz _
  have hish : 2 ≤ isz (sh : ℤ) := two_le_isz _
  have h1sheq : ((1 : ℤ) + (sh : ℤ)) = ((sh + 1 : ℕ) : ℤ) := by push_cast; ring
  have h1sh : isz ((1 : ℤ) + (sh : ℤ)) ≤ isz (sh : ℤ) + 1 := by
    rw [h1sheq]; exact isz_succ_le sh
  have hm2 : isz (((m / 2 : ℕ) : ℤ)) ≤ isz (m : ℤ) := isz_natCast_mono (Nat.div_le_self m 2)
  have hm2b : isz ((m : ℤ) / 2) ≤ isz (m : ℤ) := by
    rw [show ((m : ℤ) / 2) = (((m / 2 : ℕ)) : ℤ) by exact (Int.ofNat_tdiv m 2).symm]
    exact hm2
  have hshrval : Int.tdiv (m : ℤ) (2 ^ ((1 : ℤ)).toNat) = ((m / 2 : ℕ) : ℤ) := by
    have h1 : ((1 : ℤ)).toNat = 1 := Int.toNat_natCast 1
    rw [h1, pow_one]
    exact (Int.ofNat_tdiv m 2).symm
  have s1 : WordR main (rollP 2) (fun vs => vs = X :: .int (m : ℤ) :: .int (sh : ℤ) :: rest)
      (fun _ out => out = .int (sh : ℤ) :: X :: .int (m : ℤ) :: rest)
      (fun _ => 256 * (Kr + Kpv + Ksw + Ka + Ksh) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 2 _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, him, hish]
  have s2 : WordR main (pushP (.int 1))
      (fun vs => vs = .int (sh : ℤ) :: X :: .int (m : ℤ) :: rest)
      (fun _ out => out = .int 1 :: .int (sh : ℤ) :: X :: .int (m : ℤ) :: rest)
      (fun _ => 256 * (Kr + Kpv + Ksw + Ka + Ksh) * U) :=
    pushStep (hpush main) (.int 1) _ _ (by rw [vsz_int_one]; nlinarith [hU, hvX, him, hish])
  have s3 : WordR main addP (fun vs => vs = .int 1 :: .int (sh : ℤ) :: X :: .int (m : ℤ) :: rest)
      (fun _ out => out = .int ((1 : ℤ) + (sh : ℤ)) :: X :: .int (m : ℤ) :: rest)
      (fun _ => 256 * (Kr + Kpv + Ksw + Ka + Ksh) * U) :=
    addStep (hadd main) (1 : ℤ) (sh : ℤ) (X :: .int (m : ℤ) :: rest) _
      (by nlinarith [hU, hvX, him, hish, isz_one])
  have s4 : WordR main (rollP 2)
      (fun vs => vs = .int ((1 : ℤ) + (sh : ℤ)) :: X :: .int (m : ℤ) :: rest)
      (fun _ out => out = .int (m : ℤ) :: .int ((1 : ℤ) + (sh : ℤ)) :: X :: rest)
      (fun _ => 256 * (Kr + Kpv + Ksw + Ka + Ksh) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 2 _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, him, hish, h1sh]
  have s5 : WordR main (pushP (.int 1))
      (fun vs => vs = .int (m : ℤ) :: .int ((1 : ℤ) + (sh : ℤ)) :: X :: rest)
      (fun _ out => out = .int 1 :: .int (m : ℤ) :: .int ((1 : ℤ) + (sh : ℤ)) :: X :: rest)
      (fun _ => 256 * (Kr + Kpv + Ksw + Ka + Ksh) * U) :=
    pushStep (hpush main) (.int 1) _ _ (by rw [vsz_int_one]; nlinarith [hU, hvX, him, hish])
  have s6 : WordR main swapP
      (fun vs => vs = .int 1 :: .int (m : ℤ) :: .int ((1 : ℤ) + (sh : ℤ)) :: X :: rest)
      (fun _ out => out = .int (m : ℤ) :: .int 1 :: .int ((1 : ℤ) + (sh : ℤ)) :: X :: rest)
      (fun _ => 256 * (Kr + Kpv + Ksw + Ka + Ksh) * U) := by
    refine WordR_conseqC (swapStep (hswap main) _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, him, hish]
  have s7 : WordR main shrP
      (fun vs => vs = .int (m : ℤ) :: .int 1 :: .int ((1 : ℤ) + (sh : ℤ)) :: X :: rest)
      (fun _ out => out = .int (((m / 2 : ℕ)) : ℤ) :: .int ((1 : ℤ) + (sh : ℤ)) :: X :: rest)
      (fun _ => 256 * (Kr + Kpv + Ksw + Ka + Ksh) * U) := by
    refine WordR_conseqC (shrTStep (hshr main) (m : ℤ) (1 : ℤ)
      (.int ((1 : ℤ) + (sh : ℤ)) :: X :: rest) (by norm_num) _ ?_) rfl
      (fun out hout => by rw [hout, hshrval]) le_rfl
    nlinarith [hU, hvX, him, hish, isz_one]
  have s8 : WordR main (rollP 2)
      (fun vs => vs = .int (((m / 2 : ℕ)) : ℤ) :: .int ((1 : ℤ) + (sh : ℤ)) :: X :: rest)
      (fun _ out => out = X :: .int (((m / 2 : ℕ)) : ℤ) :: .int ((1 : ℤ) + (sh : ℤ)) :: rest)
      (fun _ => 256 * (Kr + Kpv + Ksw + Ka + Ksh) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 2 _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, him, hish, h1sh, hm2, hm2b]
  have h12 := seqC hk.seq s1 s2
  have h123 := seqC hk.seq h12 s3
  have h1234 := seqC hk.seq h123 s4
  have h12345 := seqC hk.seq h1234 s5
  have h123456 := seqC hk.seq h12345 s6
  have h1234567 := seqC hk.seq h123456 s7
  have h12345678 := seqC hk.seq h1234567 s8
  refine WordR_weaken h12345678 (fun vs hvs => hvs) ?_ ?_
  · intro vs out hvs hout
    rw [hout, h1sheq]
  · intro vs hvs
    nlinarith [hD, hU, hvX]

end Work.SynFFT
