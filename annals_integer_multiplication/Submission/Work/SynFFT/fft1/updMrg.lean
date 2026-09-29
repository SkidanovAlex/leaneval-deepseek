import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.fft1.stepKit

/-!
# Doubling the merge scale below the data list

`X :: int s :: rest ↦ X :: int (2s) :: rest` by `roll 1; dup; add; roll 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH
open Work.SynFFT.MrgKit
open Work.SynFFT.Fft1Kit

local infixl:68 " ;;; " => HvdH.Cmd.seq

theorem updMrg (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (X : HvdH.Val) (s : ℕ)
      (rest : List HvdH.Val) (D : ℕ),
      K * (HvdH.vsz X + HvdH.isz (s : ℤ) + 1) ≤ D →
      HvdH.WordR main prog
        (fun vs => vs = X :: HvdH.Val.int (s : ℤ) :: rest)
        (fun _ out => out = X :: HvdH.Val.int ((2 * s : ℕ) : ℤ) :: rest) (fun _ => D) := by
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨addP, Ka, hadd⟩ := hi.add
  refine ⟨rollP 1 ;;; dupP ;;; addP ;;; rollP 1, 2048 * (Kr + Kd + Ka + 1), ?_⟩
  intro main X s rest D hD
  set U : ℕ := vsz X + isz (s : ℤ) + 1 with hU
  have hvX : 1 ≤ vsz X := one_le_vsz X
  have his : 2 ≤ isz (s : ℤ) := two_le_isz _
  have h2s : isz ((s : ℤ) + (s : ℤ)) ≤ isz (s : ℤ) + 1 := by
    rw [show ((s : ℤ) + (s : ℤ)) = 2 * (s : ℤ) by ring]
    exact isz_two_mul_le _
  have s1 : WordR main (rollP 1) (fun vs => vs = X :: .int (s : ℤ) :: rest)
      (fun _ out => out = .int (s : ℤ) :: X :: rest) (fun _ => 256 * (Kr + Kd + Ka) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 1 _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, his]
  have s2 : WordR main dupP (fun vs => vs = .int (s : ℤ) :: X :: rest)
      (fun _ out => out = .int (s : ℤ) :: .int (s : ℤ) :: X :: rest)
      (fun _ => 256 * (Kr + Kd + Ka) * U) :=
    dupStep (hdup main) (.int (s : ℤ)) (X :: rest) _ (by rw [vsz_int']; nlinarith [hU, hvX, his])
  have s3 : WordR main addP (fun vs => vs = .int (s : ℤ) :: .int (s : ℤ) :: X :: rest)
      (fun _ out => out = .int ((s : ℤ) + (s : ℤ)) :: X :: rest)
      (fun _ => 256 * (Kr + Kd + Ka) * U) :=
    addStep (hadd main) (s : ℤ) (s : ℤ) (X :: rest) _ (by nlinarith [hU, hvX, his])
  have s4 : WordR main (rollP 1) (fun vs => vs = .int ((s : ℤ) + (s : ℤ)) :: X :: rest)
      (fun _ out => out = X :: .int ((s : ℤ) + (s : ℤ)) :: rest)
      (fun _ => 256 * (Kr + Kd + Ka) * U) := by
    refine WordR_conseqC (rollStep (hroll main) 1 _ (by simp) _ ?_) rfl
      (fun out hout => by simpa using hout) le_rfl
    simp [Work.SynFFT.MrgKit.vsz_int', isz_one]
    nlinarith [hU, hvX, his, h2s]
  have h12 := seqC hk.seq s1 s2
  have h123 := seqC hk.seq h12 s3
  have h1234 := seqC hk.seq h123 s4
  have heq : ((s : ℤ) + (s : ℤ)) = ((2 * s : ℕ) : ℤ) := by push_cast; ring
  refine WordR_weaken h1234 (fun vs hvs => hvs) ?_ ?_
  · intro vs out hvs hout
    rw [hout, heq]
  · intro vs hvs
    nlinarith [hD, hU, hvX]

end Work.SynFFT
