import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.fft1.stepKit

/-!
# Reordering the level parameters into the merge parameters

`X, m, sh, sgn, r, p, k ↦ X, 1, r, p, sgn, k` by `roll 1; roll 2; drop; drop; roll 3; roll 3;
push 1; roll 3`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH
open Work.SynFFT.MrgKit
open Work.SynFFT.Fft1Kit

local infixl:68 " ;;; " => HvdH.Cmd.seq

theorem transProg (hk : Work.SynFFT.KLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (X : HvdH.Val) (m sh : ℕ) (sgn : ℤ)
      (r p k : ℕ) (rest : List HvdH.Val) (D : ℕ),
      K * (HvdH.vsz X + HvdH.isz (m : ℤ) + HvdH.isz (sh : ℤ) + HvdH.isz sgn +
            HvdH.isz (r : ℤ) + HvdH.isz (p : ℤ) + HvdH.isz (k : ℤ) + 1) ≤ D →
      HvdH.WordR main prog
        (fun vs => vs = X :: HvdH.Val.int (m : ℤ) :: HvdH.Val.int (sh : ℤ) :: HvdH.Val.int sgn ::
          HvdH.Val.int (r : ℤ) :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (k : ℤ) :: rest)
        (fun _ out => out = X :: HvdH.Val.int (1 : ℤ) :: HvdH.Val.int (r : ℤ) ::
          HvdH.Val.int (p : ℤ) :: HvdH.Val.int sgn :: HvdH.Val.int (k : ℤ) :: rest)
        (fun _ => D) := by
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  refine ⟨rollP 1 ;;; rollP 2 ;;; kdrP ;;; kdrP ;;; rollP 3 ;;; rollP 3 ;;; pushP (.int 1) ;;; rollP 3,
    4096 * (Kr + Kdr + Kpv + 1), ?_⟩
  intro main X m sh sgn r p k rest D hD
  set U : ℕ := vsz X + isz (m : ℤ) + isz (sh : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) +
    isz (k : ℤ) + 1 with hU
  have hvX : 1 ≤ vsz X := one_le_vsz X
  have him : 2 ≤ isz (m : ℤ) := two_le_isz _
  have hish : 2 ≤ isz (sh : ℤ) := two_le_isz _
  have hig : 2 ≤ isz sgn := two_le_isz _
  have hir : 2 ≤ isz (r : ℤ) := two_le_isz _
  have hip : 2 ≤ isz (p : ℤ) := two_le_isz _
  have hik : 2 ≤ isz (k : ℤ) := two_le_isz _
  have h1 : WordR main (rollP 1)
      (fun vs => vs = X :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: .int (k : ℤ) :: rest)
      (fun _ out => out = .int (m : ℤ) :: X :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: .int (k : ℤ) :: rest) (fun _ => 256 * (Kr + Kdr + Kpv) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 1 _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, him, hish, hig, hir, hip, hik]
  have h2 : WordR main (rollP 2)
      (fun vs => vs = .int (m : ℤ) :: X :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: .int (k : ℤ) :: rest)
      (fun _ out => out = .int (sh : ℤ) :: .int (m : ℤ) :: X :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: .int (k : ℤ) :: rest) (fun _ => 256 * (Kr + Kdr + Kpv) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 2 _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, him, hish, hig, hir, hip, hik]
  have h3 : WordR main kdrP
      (fun vs => vs = .int (sh : ℤ) :: .int (m : ℤ) :: X :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: .int (k : ℤ) :: rest)
      (fun _ out => out = .int (m : ℤ) :: X :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: .int (k : ℤ) :: rest) (fun _ => 256 * (Kr + Kdr + Kpv) * U) := by
    refine WordR_conseqC (kdropStep (hkdr main) _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, him, hish, hig, hir, hip, hik]
  have h4 : WordR main kdrP
      (fun vs => vs = .int (m : ℤ) :: X :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: .int (k : ℤ) :: rest)
      (fun _ out => out = X :: .int sgn :: .int (r : ℤ) ::
        .int (p : ℤ) :: .int (k : ℤ) :: rest) (fun _ => 256 * (Kr + Kdr + Kpv) * U) := by
    refine WordR_conseqC (kdropStep (hkdr main) _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, him, hish, hig, hir, hip, hik]
  have h5 : WordR main (rollP 3)
      (fun vs => vs = X :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) ::
        .int (k : ℤ) :: rest)
      (fun _ out => out = .int (p : ℤ) :: X :: .int sgn :: .int (r : ℤ) ::
        .int (k : ℤ) :: rest) (fun _ => 256 * (Kr + Kdr + Kpv) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 3 _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, him, hish, hig, hir, hip, hik]
  have h6 : WordR main (rollP 3)
      (fun vs => vs = .int (p : ℤ) :: X :: .int sgn :: .int (r : ℤ) ::
        .int (k : ℤ) :: rest)
      (fun _ out => out = .int (r : ℤ) :: .int (p : ℤ) :: X :: .int sgn ::
        .int (k : ℤ) :: rest) (fun _ => 256 * (Kr + Kdr + Kpv) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 3 _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, him, hish, hig, hir, hip, hik]
  have h7 : WordR main (pushP (.int 1))
      (fun vs => vs = .int (r : ℤ) :: .int (p : ℤ) :: X :: .int sgn :: .int (k : ℤ) :: rest)
      (fun _ out => out = .int 1 :: .int (r : ℤ) :: .int (p : ℤ) :: X :: .int sgn ::
        .int (k : ℤ) :: rest) (fun _ => 256 * (Kr + Kdr + Kpv) * U) :=
    pushStep (hpush main) (.int 1) _ _ (by rw [vsz_int_one]; nlinarith [hU, hvX, hish])
  have h8 : WordR main (rollP 3)
      (fun vs => vs = .int 1 :: .int (r : ℤ) :: .int (p : ℤ) :: X :: .int sgn ::
        .int (k : ℤ) :: rest)
      (fun _ out => out = X :: .int 1 :: .int (r : ℤ) :: .int (p : ℤ) :: .int sgn ::
        .int (k : ℤ) :: rest) (fun _ => 256 * (Kr + Kdr + Kpv) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 3 _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, him, hish, hig, hir, hip, hik]
  have h12 := seqC hk.seq h1 h2
  have h123 := seqC hk.seq h12 h3
  have h1234 := seqC hk.seq h123 h4
  have h12345 := seqC hk.seq h1234 h5
  have h123456 := seqC hk.seq h12345 h6
  have h1234567 := seqC hk.seq h123456 h7
  have h12345678 := seqC hk.seq h1234567 h8
  exact WordR_weaken h12345678 (fun vs hvs => hvs) (fun vs out hvs hout => hout)
    (fun vs hvs => by nlinarith [hD, hU, hvX])

end Work.SynFFT
