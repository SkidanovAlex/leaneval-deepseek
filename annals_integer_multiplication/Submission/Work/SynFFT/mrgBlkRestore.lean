import Mathlib
import Submission.Work.SynFFT.mrgBlkHelper

/-!
# SynFFT, interleave block pass: restoring the parameter `s`

`ofList xs :: rest  ↦  ofList xs :: int (xs.length / 2) :: rest`, at cost
`K * (vsz (ofList xs) + 1) + K`: compute the length of the list, halve it, and move the result
below the list again.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

theorem isz_one : isz (1 : ℤ) = 3 := by simp [isz]

theorem mrgBlk_restoreW (hk : KLib) (hi : IntLib) (hl : LayoutLib) :
    ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (xs : List Val) (rest : List Val),
      WordR main prog
        (fun vs => vs = ofList xs :: rest)
        (fun vs out => out = ofList xs :: .int ((xs.length / 2 : ℕ) : ℤ) :: rest)
        (fun _ => K * (vsz (ofList xs) + 1) + K) := by
  obtain ⟨lenP, Kl, hlen⟩ := hl.length
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨swapP, Ksw, hswap⟩ := hk.swap
  obtain ⟨shP, Ksh, hsh⟩ := hi.shrT
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  refine ⟨(((lenP ;;; pushP (.int 1)) ;;; swapP) ;;; shP) ;;; rollP 1,
    10000 * (Kl + Kpv + Ksw + Ksh + Kr + 1), ?_⟩
  intro main xs rest
  set Kx : ℕ := 100 * (Kl + Kpv + Ksw + Ksh + Kr + 1) with hKx
  set V : ℕ := vsz (ofList xs) + 1 with hV
  have hV1 : 1 ≤ V := by omega
  have hKl : Kl ≤ Kx := by rw [hKx]; omega
  have hKpv : Kpv ≤ Kx := by rw [hKx]; omega
  have hKsw : Ksw ≤ Kx := by rw [hKx]; omega
  have hKsh : Ksh ≤ Kx := by rw [hKx]; omega
  have hKr : Kr ≤ Kx := by rw [hKx]; omega
  set B : ℕ := 10 * Kx * V with hB
  have hV4 : V + 4 ≤ 5 * V := by omega
  have hlenle : xs.length + 2 ≤ V := by rw [hV, MrgKit.vsz_ofList]; omega
  have hiszlen : isz (xs.length : ℤ) ≤ V := by
    rw [isz, Int.natAbs_natCast]
    have h : xs.length.size ≤ xs.length := (Nat.size_le).mpr Nat.lt_two_pow_self
    omega
  have hiszhalf : isz ((xs.length / 2 : ℕ) : ℤ) ≤ V := by
    rw [isz, Int.natAbs_natCast]
    have h : (xs.length / 2).size ≤ xs.length / 2 := (Nat.size_le).mpr Nat.lt_two_pow_self
    omega
  -- step 0: length
  have s0 : WordR main lenP (fun vs => vs = ofList xs :: rest)
      (fun _ out => out = .int (xs.length : ℤ) :: ofList xs :: rest) (fun _ => B) := by
    refine lengthStep (fun ys => hlen main ys) xs rest B ?_
    rw [hB, hV]
    nlinarith [hKl, hV1, Nat.zero_le Kx]
  -- step 1: push 1
  have s1 : WordR main (pushP (.int 1))
      (fun vs => vs = .int (xs.length : ℤ) :: ofList xs :: rest)
      (fun _ out => out = .int (1 : ℤ) :: .int (xs.length : ℤ) :: ofList xs :: rest)
      (fun _ => B) := by
    refine MrgKit.pushStep (hpush main) (.int 1) _ B ?_
    rw [MrgKit.vsz_int', isz_one, hB]
    nlinarith [hKpv, hV1, Nat.zero_le Kx]
  -- step 2: swap
  have s2 : WordR main swapP
      (fun vs => vs = .int (1 : ℤ) :: .int (xs.length : ℤ) :: ofList xs :: rest)
      (fun _ out => out = .int (xs.length : ℤ) :: .int (1 : ℤ) :: ofList xs :: rest)
      (fun _ => B) := by
    refine MrgKit.swapStep (hswap main) _ (by simp) B ?_
    simp only [List.getD_cons_zero, List.getD_cons_succ, MrgKit.vsz_int', isz_one, hB]
    nlinarith [hKsw, hiszlen, hV1, hV4, Nat.zero_le Kx]
  -- step 3: halve
  have hshstep : WordR main shP
      (fun vs => vs = .int (xs.length : ℤ) :: .int (1 : ℤ) :: ofList xs :: rest)
      (fun _ out => out = .int (Int.tdiv (xs.length : ℤ) 2) :: ofList xs :: rest)
      (fun _ => B) := by
    refine binOpStep (hsh main) (xs.length : ℤ) 1 (ofList xs :: rest)
      (by norm_num : (0 : ℤ) ≤ 1) B ?_
    rw [isz_one, hB]
    nlinarith [hKsh, hiszlen, hV1, hV4, Nat.zero_le Kx]
  have s3 : WordR main shP
      (fun vs => vs = .int (xs.length : ℤ) :: .int (1 : ℤ) :: ofList xs :: rest)
      (fun _ out => out = .int (((xs.length / 2 : ℕ) : ℤ)) :: ofList xs :: rest)
      (fun _ => B) := by
    have h := hshstep
    have htd : Int.tdiv (xs.length : ℤ) 2 = (((xs.length / 2 : ℕ) : ℤ)) :=
      (Int.ofNat_tdiv xs.length 2).symm
    rw [htd] at h
    exact h
  -- step 4: roll 1
  have s4 : WordR main (rollP 1)
      (fun vs => vs = .int (((xs.length / 2 : ℕ) : ℤ)) :: ofList xs :: rest)
      (fun _ out => out = ofList xs :: .int (((xs.length / 2 : ℕ) : ℤ)) :: rest)
      (fun _ => B) := by
    refine MrgKit.rollStep (fun k => hroll main k) 1
      (.int (((xs.length / 2 : ℕ) : ℤ)) :: ofList xs :: rest) (by simp) B ?_
    have hsum : (((.int (((xs.length / 2 : ℕ) : ℤ)) :: ofList xs :: rest : List Val).take 2).map vsz).sum
        = isz (((xs.length / 2 : ℕ) : ℤ)) + vsz (ofList xs) := by
      simp [MrgKit.vsz_int']
    rw [hsum, hB]
    nlinarith [hKr, hiszhalf, hV1, Nat.zero_le Kx]
  -- assembly
  have e01 := MrgKit.WordR_seqC s0 s1
  have e012 := MrgKit.WordR_seqC e01 s2
  have e0123 := MrgKit.WordR_seqC e012 s3
  have e01234 := MrgKit.WordR_seqC e0123 s4
  refine MrgKit.WordR_weaken e01234 (fun vs hvs => hvs) (fun vs out _ hq => hq) (fun vs _ => ?_)
  set S : ℕ := Kl + Kpv + Ksw + Ksh + Kr + 1 with hS
  have h5 : B + B + B + B + B = 5 * B := by ring
  rw [h5]
  have h6 : 5 * B ≤ 100 * Kx * V := by
    rw [hB]
    have h7 : 5 * (10 * Kx * V) = (50 * Kx) * V := by ring
    rw [h7]
    exact Nat.mul_le_mul_right V (by omega)
  have h8 : 100 * Kx * V = 10000 * S * V := by rw [hKx, hS]; ring
  have h9 : 10000 * S * V ≤ 10000 * S * (vsz (ofList xs) + 1) + 10000 * S := by
    rw [hV]
    exact Nat.le_add_right _ _
  calc 5 * B ≤ 100 * Kx * V := h6
    _ = 10000 * S * V := h8
    _ ≤ 10000 * S * (vsz (ofList xs) + 1) + 10000 * S := h9
    _ = 10000 * (Kl + Kpv + Ksw + Ksh + Kr + 1) * (vsz (ofList xs) + 1)
          + 10000 * (Kl + Kpv + Ksw + Ksh + Kr + 1) := by rw [hS]

end Work.SynFFT
