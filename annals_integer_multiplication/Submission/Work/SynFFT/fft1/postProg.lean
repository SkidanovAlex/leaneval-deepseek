import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.fft1.stepKit

/-!
# The epilogue of the slice word

`X, s, r, p, sgn, k ↦ X, k, sgn, r, p` by `roll 1; drop; roll 3; roll 4; roll 2`.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH
open Work.SynFFT.MrgKit
open Work.SynFFT.Fft1Kit

local infixl:68 " ;;; " => HvdH.Cmd.seq

theorem postProg (hk : Work.SynFFT.KLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (X : HvdH.Val) (s r p k : ℕ) (sgn : ℤ)
      (rest : List HvdH.Val) (D : ℕ),
      K * (HvdH.vsz X + HvdH.isz (s : ℤ) + HvdH.isz (r : ℤ) + HvdH.isz (p : ℤ) +
            HvdH.isz sgn + HvdH.isz (k : ℤ) + 1) ≤ D →
      HvdH.WordR main prog
        (fun vs => vs = X :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (r : ℤ) ::
          HvdH.Val.int (p : ℤ) :: HvdH.Val.int sgn :: HvdH.Val.int (k : ℤ) :: rest)
        (fun _ out => out = X :: HvdH.Val.int (k : ℤ) :: HvdH.Val.int sgn ::
          HvdH.Val.int (r : ℤ) :: HvdH.Val.int (p : ℤ) :: rest) (fun _ => D) := by
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  refine ⟨rollP 1 ;;; kdrP ;;; rollP 3 ;;; rollP 4 ;;; rollP 2, 200 * (Kr + Kdr + 1), ?_⟩
  intro main X s r p k sgn rest D hD
  set U : ℕ := vsz X + isz (s : ℤ) + isz (r : ℤ) + isz (p : ℤ) + isz sgn + isz (k : ℤ) + 1
    with hU
  have hU1 : 1 ≤ U := by rw [hU]; omega
  have hUX : vsz X ≤ U := by rw [hU]; omega
  have hUs : isz (s : ℤ) ≤ U := by rw [hU]; omega
  have hUr : isz (r : ℤ) ≤ U := by rw [hU]; omega
  have hUp : isz (p : ℤ) ≤ U := by rw [hU]; omega
  have hUg : isz sgn ≤ U := by rw [hU]; omega
  have hUk : isz (k : ℤ) ≤ U := by rw [hU]; omega
  have h1 : WordR main (rollP 1)
      (fun vs => vs = X :: .int (s : ℤ) :: .int (r : ℤ) :: .int (p : ℤ) :: .int sgn ::
        .int (k : ℤ) :: rest)
      (fun _ out => out = .int (s : ℤ) :: X :: .int (r : ℤ) :: .int (p : ℤ) :: .int sgn ::
        .int (k : ℤ) :: rest) (fun _ => 8 * Kr * U) := by
    refine WordR_conseqC (rollStep (hroll main) 1 _ (by simp) (8 * Kr * U) ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int']
    nlinarith [hU1, hUX, hUs]
  have h2 : WordR main kdrP
      (fun vs => vs = .int (s : ℤ) :: X :: .int (r : ℤ) :: .int (p : ℤ) :: .int sgn ::
        .int (k : ℤ) :: rest)
      (fun _ out => out = X :: .int (r : ℤ) :: .int (p : ℤ) :: .int sgn ::
        .int (k : ℤ) :: rest) (fun _ => 8 * Kdr * U) := by
    refine WordR_conseqC (kdropStep (hkdr main) _ (by simp) (8 * Kdr * U) ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int']
    nlinarith [hUs, hU1]
  have h3 : WordR main (rollP 3)
      (fun vs => vs = X :: .int (r : ℤ) :: .int (p : ℤ) :: .int sgn :: .int (k : ℤ) :: rest)
      (fun _ out => out = .int sgn :: X :: .int (r : ℤ) :: .int (p : ℤ) :: .int (k : ℤ) ::
        rest) (fun _ => 16 * Kr * U) := by
    refine WordR_conseqC (rollStep (hroll main) 3 _ (by simp) (16 * Kr * U) ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int']
    nlinarith [hU1, hUX, hUr, hUp, hUg]
  have h4 : WordR main (rollP 4)
      (fun vs => vs = .int sgn :: X :: .int (r : ℤ) :: .int (p : ℤ) :: .int (k : ℤ) :: rest)
      (fun _ out => out = .int (k : ℤ) :: .int sgn :: X :: .int (r : ℤ) :: .int (p : ℤ) ::
        rest) (fun _ => 16 * Kr * U) := by
    refine WordR_conseqC (rollStep (hroll main) 4 _ (by simp) (16 * Kr * U) ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int']
    nlinarith [hU1, hUX, hUr, hUp, hUg, hUk]
  have h5 : WordR main (rollP 2)
      (fun vs => vs = .int (k : ℤ) :: .int sgn :: X :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
      (fun _ out => out = X :: .int (k : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) ::
        rest) (fun _ => 8 * Kr * U) := by
    refine WordR_conseqC (rollStep (hroll main) 2 _ (by simp) (8 * Kr * U) ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int']
    nlinarith [hU1, hUX, hUk, hUg]
  have h12 := seqC hk.seq h1 h2
  have h123 := seqC hk.seq h12 h3
  have h1234 := seqC hk.seq h123 h4
  have h12345 := seqC hk.seq h1234 h5
  exact WordR_weaken h12345 (fun vs hvs => hvs) (fun vs out hvs hout => hout)
    (fun vs hvs => by nlinarith [hD, hU1])

end Work.SynFFT
