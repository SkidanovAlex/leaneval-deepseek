import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.paramKit

/-!
# `Work.SynFFT.paramCalc` — the twiddle parameters as a `StackLang` word
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000

namespace Work.SynFFT

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

theorem paramCalc (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) :
    ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (j sh r p : ℕ) (sgn : ℤ) (W₁ W₂ : Val)
      (rest : List Val) (MB : ℕ),
      (∀ v ∈ [W₁, W₂, .int (j : ℤ), .int (sh : ℤ), .int sgn, .int (r : ℤ), .int (p : ℤ)],
        vsz v ≤ MB) →
      0 < r → 2 ^ sh ≤ 2 * r → j * 2 ^ sh < r → (sgn = 1 ∨ sgn = -1) →
      WordR main prog
        (fun vs => vs = W₁ :: W₂ :: .int (j : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) ::
          .int (p : ℤ) :: rest)
        (fun _ out => out =
          .int ((if 0 < ((j * 2 ^ sh : ℕ) : ℤ) then (1 : ℤ) else 0) *
            (((j * 2 ^ sh : ℕ) : ℤ) + max sgn 0 * ((r : ℤ) - 2 * ((j * 2 ^ sh : ℕ) : ℤ)))) ::
          .int (1 - 2 * (max sgn 0 * (if 0 < ((j * 2 ^ sh : ℕ) : ℤ) then (1 : ℤ) else 0))) ::
          .int (r : ℤ) :: .int (p : ℤ) :: W₁ :: W₂ :: .int (j : ℤ) :: .int (sh : ℤ) ::
          .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun _ => Kc * (MB + 1) * 64) := by
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨pushP, Kpv, hpush⟩ := hk.pushVal
  obtain ⟨shlP, Kshl, hshl⟩ := hi.shl
  obtain ⟨ltP, Klt, hlt⟩ := hi.lt
  obtain ⟨maxP, Kmax, hmax⟩ := hi.max
  obtain ⟨mulP, Kmul, hmul⟩ := hi.mulS
  obtain ⟨subP, Ksub, hsub⟩ := hi.sub
  obtain ⟨addP, Kadd, hadd⟩ := hi.add
  set Kx : ℕ := 1000000 * (Kp + Kr + Kpv + Kshl + Klt + Kmax + Kmul + Ksub + Kadd + 1) with hKx
  have hKp : Kp ≤ Kx := by rw [hKx]; omega
  have hKr : Kr ≤ Kx := by rw [hKx]; omega
  have hKpv : Kpv ≤ Kx := by rw [hKx]; omega
  have hKshl : Kshl ≤ Kx := by rw [hKx]; omega
  have hKlt : Klt ≤ Kx := by rw [hKx]; omega
  have hKmax : Kmax ≤ Kx := by rw [hKx]; omega
  have hKmul : Kmul ≤ Kx := by rw [hKx]; omega
  have hKsub : Ksub ≤ Kx := by rw [hKx]; omega
  have hKadd : Kadd ≤ Kx := by rw [hKx]; omega
  refine ⟨pickP 6 ;;; pickP 6 ;;; pickP 5 ;;; pickP 5 ;;; shlP ;;; pickP 0 ;;; pickP 0 ;;;
    pushP (.int 0) ;;; ltP ;;; pushP (.int 0) ;;; pickP 10 ;;; maxP ;;; pickP 1 ;;; rollP 1 ;;;
    mulP ;;; pushP (.int 2) ;;; mulP ;;; pushP (.int 1) ;;; subP ;;; pushP (.int 0) ;;; pickP 11 ;;;
    maxP ;;; rollP 3 ;;; pushP (.int 2) ;;; mulP ;;; pickP 5 ;;; subP ;;; rollP 1 ;;; mulP ;;;
    rollP 3 ;;; addP ;;; rollP 2 ;;; mulP, 10000000 * Kx, ?_⟩
  intro main j sh r p sgn W₁ W₂ rest MB hMBs hr hsh ht hsgn
  -- ## abbreviations
  set tZ : ℤ := ((j * 2 ^ sh : ℕ) : ℤ) with htZ
  set btZ : ℤ := (if 0 < ((j * 2 ^ sh : ℕ) : ℤ) then (1 : ℤ) else 0) with hbtZ
  set bZ : ℤ := max sgn 0 with hbZ
  set sC : ℤ := btZ * (tZ + bZ * ((r : ℤ) - 2 * tZ)) with hsC
  set sgC : ℤ := 1 - 2 * (bZ * btZ) with hsgC
  set Jv : Val := .int (j : ℤ) with hJv
  set SHv : Val := .int (sh : ℤ) with hSHv
  set SGv : Val := .int sgn with hSGv
  set Rv : Val := .int (r : ℤ) with hRv
  set Pv : Val := .int (p : ℤ) with hPv
  set S0 : List Val := W₁ :: W₂ :: Jv :: SHv :: SGv :: Rv :: Pv :: rest with hS0
  set L : List Val := [W₁, W₂, Jv, SHv, SGv, Rv, Pv, .int tZ, .int btZ, .int bZ,
    .int (0 : ℤ), .int (1 : ℤ), .int (2 : ℤ), .int (bZ * btZ), .int (2 * (bZ * btZ)),
    .int sgC, .int (2 * tZ), .int ((r : ℤ) - 2 * tZ), .int (bZ * ((r : ℤ) - 2 * tZ)),
    .int (tZ + bZ * ((r : ℤ) - 2 * tZ)), .int sC] with hL
  set Cs : ℕ := Kx * (MB + 1) * 10000000 with hCs
  have hshlval : j * 2 ^ (sh : ℤ).toNat = tZ := by
    rw [htZ, Int.toNat_natCast]
    push_cast
    ring
  -- ## sizes
  have hone : ∀ v : Val, 1 ≤ vsz v := by
    intro v
    cases v with
    | nil => simp [vsz, Val.enc]
    | int z => simp only [vsz, Val.enc, List.length_cons, List.length_append,
        List.length_map, List.length_singleton]; omega
    | cons a b => simp only [vsz, Val.enc, List.length_cons, List.length_append,
        List.length_map, List.length_singleton]; omega
  have hW1sz : vsz W₁ ≤ MB := hMBs W₁ (by simp)
  have hMB1 : 1 ≤ MB := le_trans (hone W₁) hW1sz
  have hJisz : isz (j : ℤ) ≤ MB := by
    have h := hMBs Jv (by simp)
    rwa [hJv, MrgKit.vsz_int'] at h
  have hSHisz : isz (sh : ℤ) ≤ MB := by
    have h := hMBs SHv (by simp)
    rwa [hSHv, MrgKit.vsz_int'] at h
  have hSGisz' : isz sgn ≤ MB := by
    have h := hMBs SGv (by simp)
    rwa [hSGv, MrgKit.vsz_int'] at h
  have hPisz : isz (p : ℤ) ≤ MB := by
    have h := hMBs Pv (by simp)
    rwa [hPv, MrgKit.vsz_int'] at h
  have hiszR : isz (r : ℤ) ≤ MB := by
    have h := hMBs Rv (by simp)
    rwa [hRv, MrgKit.vsz_int'] at h
  have hsizeR : r.size + 2 ≤ MB := by have := hiszR; rwa [isz] at this
  have sgnisz : isz sgn ≤ 3 := by
    rcases hsgn with h | h <;> rw [h] <;> decide
  have h2isz : isz (2 : ℤ) ≤ 4 := by decide
  have htZnn : 0 ≤ tZ := by rw [htZ]; positivity
  have htZle : tZ ≤ (r : ℤ) := by rw [htZ]; exact_mod_cast le_of_lt ht
  have hTisz : isz tZ ≤ 3 * (MB + 1) := by
    have h : isz tZ = (j * 2 ^ sh).size + 2 := by
      rw [isz, htZ, Int.natAbs_natCast]
    rw [h]
    have h2 : (j * 2 ^ sh).size ≤ r.size := Nat.size_le_size (le_of_lt ht)
    omega
  have hBTisz : isz btZ ≤ 3 := by
    have h : btZ = 0 ∨ btZ = 1 := by rw [hbtZ]; split <;> simp
    rcases h with h | h <;> rw [h] <;> decide
  have hBZisz : isz bZ ≤ 3 := by
    have h : bZ = 0 ∨ bZ = 1 := by
      rw [hbZ]; rcases hsgn with h | h <;> rw [h] <;> norm_num
    rcases h with h | h <;> rw [h] <;> decide
  have hBB0 : bZ * btZ = 0 ∨ bZ * btZ = 1 := by
    have hz : bZ = 0 ∨ bZ = 1 := by
      rw [hbZ]; rcases hsgn with h | h <;> rw [h] <;> norm_num
    have ht0 : btZ = 0 ∨ btZ = 1 := by rw [hbtZ]; split <;> simp
    rcases hz with hz | hz <;> rcases ht0 with ht0 | ht0 <;> rw [hz, ht0] <;> simp
  have hBBisz : isz (bZ * btZ) ≤ 3 := by
    rcases hBB0 with h | h <;> rw [h] <;> decide
  have h2BBisz : isz (2 * (bZ * btZ)) ≤ 4 := by
    rcases hBB0 with h | h <;> rw [h] <;> decide
  have hSGisz : isz sgC ≤ 3 := by
    have h : sgC = 1 ∨ sgC = -1 := by
      rcases hBB0 with hb | hb <;> rw [hsgC, hb] <;> norm_num
    rcases h with h | h <;> rw [h] <;> decide
  have h2Tisz : isz (2 * tZ) ≤ 3 * (MB + 1) := by
    have h : (2 * tZ).natAbs = 2 * (j * 2 ^ sh) := by
      rw [htZ, Int.natAbs_mul, Int.natAbs_natCast]
      norm_num
    rw [isz, h]
    have h2 : (2 * (j * 2 ^ sh)).size ≤ r.size + 1 := by
      have h3 : 2 * (j * 2 ^ sh) ≤ 2 * r := by omega
      have h4 : (2 * (j * 2 ^ sh)).size ≤ (2 * r).size := Nat.size_le_size h3
      have h5 : (2 * r).size ≤ r.size + 1 := by
        rw [Nat.size_le, pow_succ]
        nlinarith [Nat.lt_size_self r]
      omega
    omega
  have hR2Tisz : isz ((r : ℤ) - 2 * tZ) ≤ 3 * (MB + 1) := by
    have h : ((r : ℤ) - 2 * tZ).natAbs ≤ 2 * r := by
      have h1 : ((r : ℤ) - 2 * tZ).natAbs ≤ ((2 * r : ℕ) : ℤ).natAbs := by
        rw [Int.natAbs_le_iff_sq_le]
        push_cast
        nlinarith [htZnn, htZle]
      have h2 : ((2 * r : ℕ) : ℤ).natAbs = 2 * r := by rw [Int.natAbs_natCast]
      omega
    rw [isz]
    have h3 : ((r : ℤ) - 2 * tZ).natAbs.size ≤ r.size + 1 := by
      have h4 : ((r : ℤ) - 2 * tZ).natAbs.size ≤ (2 * r).size := Nat.size_le_size h
      have h5 : (2 * r).size ≤ r.size + 1 := by
        rw [Nat.size_le, pow_succ]
        nlinarith [Nat.lt_size_self r]
      omega
    omega
  have hBUisz : isz (bZ * ((r : ℤ) - 2 * tZ)) ≤ 3 * (MB + 1) := by
    have hbz : bZ = 0 ∨ bZ = 1 := by
      rw [hbZ]; rcases hsgn with h | h <;> rw [h] <;> norm_num
    rcases hbz with hbz | hbz <;> rw [hbz]
    · rw [zero_mul]
      have : isz (0 : ℤ) = 2 := by decide
      omega
    · rw [one_mul]; exact hR2Tisz
  have hWisz : isz (tZ + bZ * ((r : ℤ) - 2 * tZ)) ≤ 3 * (MB + 1) := by
    have hbz : bZ = 0 ∨ bZ = 1 := by
      rw [hbZ]; rcases hsgn with h | h <;> rw [h] <;> norm_num
    rcases hbz with hbz | hbz <;> rw [hbz]
    · rw [zero_mul, add_zero]; exact hTisz
    · rw [one_mul]
      have h : (tZ + ((r : ℤ) - 2 * tZ)).natAbs ≤ r := by
        rw [show tZ + ((r : ℤ) - 2 * tZ) = (r : ℤ) - tZ by ring]
        have h1 : ((r : ℤ) - tZ).natAbs ≤ ((r : ℕ) : ℤ).natAbs := by
          rw [Int.natAbs_le_iff_sq_le]
          push_cast
          nlinarith [htZnn, htZle]
        have h3 : ((r : ℕ) : ℤ).natAbs = r := by rw [Int.natAbs_natCast]
        omega
      have h2 : isz (tZ + ((r : ℤ) - 2 * tZ)) ≤ r.size + 2 := isz_le_size _ r h
      omega
  have hSCisz : isz sC ≤ 3 * (MB + 1) := by
    have ht0 : btZ = 0 ∨ btZ = 1 := by rw [hbtZ]; split <;> simp
    rcases ht0 with ht0 | ht0 <;> rw [hsC, ht0]
    · rw [zero_mul]
      have : isz (0 : ℤ) = 2 := by decide
      omega
    · rw [one_mul]; exact hWisz
  have hW2sz : vsz W₂ ≤ MB := hMBs W₂ (by simp)
  -- ## vsz-bounds for every value occurring in the computation
  have bW1 : vsz W₁ ≤ 3 * (MB + 1) := by omega
  have bW2 : vsz W₂ ≤ 3 * (MB + 1) := by omega
  have bJ : vsz Jv ≤ 3 * (MB + 1) := by rw [hJv, MrgKit.vsz_int']; omega
  have bSH : vsz SHv ≤ 3 * (MB + 1) := by rw [hSHv, MrgKit.vsz_int']; omega
  have bSG : vsz SGv ≤ 3 * (MB + 1) := by rw [hSGv, MrgKit.vsz_int']; omega
  have bR : vsz Rv ≤ 3 * (MB + 1) := by rw [hRv, MrgKit.vsz_int']; omega
  have bP : vsz Pv ≤ 3 * (MB + 1) := by rw [hPv, MrgKit.vsz_int']; omega
  have bT : vsz (.int tZ) ≤ 3 * (MB + 1) := by rw [MrgKit.vsz_int']; exact hTisz
  have bBT : vsz (.int btZ) ≤ 3 * (MB + 1) := by rw [MrgKit.vsz_int']; omega
  have bBZ : vsz (.int bZ) ≤ 3 * (MB + 1) := by rw [MrgKit.vsz_int']; omega
  have b0 : vsz (.int (0 : ℤ)) ≤ 3 * (MB + 1) := by
    rw [MrgKit.vsz_int']
    have h : isz (0 : ℤ) = 2 := by decide
    omega
  have b1 : vsz (.int (1 : ℤ)) ≤ 3 * (MB + 1) := by
    rw [MrgKit.vsz_int']
    have h : isz (1 : ℤ) = 3 := by decide
    omega
  have b2 : vsz (.int (2 : ℤ)) ≤ 3 * (MB + 1) := by
    rw [MrgKit.vsz_int']
    have h : isz (2 : ℤ) = 4 := by decide
    omega
  have bBB : vsz (.int (bZ * btZ)) ≤ 3 * (MB + 1) := by
    rw [MrgKit.vsz_int']; omega
  have b2BB : vsz (.int (2 * (bZ * btZ))) ≤ 3 * (MB + 1) := by
    rw [MrgKit.vsz_int']; omega
  have bSGC : vsz (.int sgC) ≤ 3 * (MB + 1) := by
    rw [MrgKit.vsz_int']; omega
  have b2T : vsz (.int (2 * tZ)) ≤ 3 * (MB + 1) := by
    rw [MrgKit.vsz_int']; exact h2Tisz
  have bR2T : vsz (.int ((r : ℤ) - 2 * tZ)) ≤ 3 * (MB + 1) := by
    rw [MrgKit.vsz_int']; exact hR2Tisz
  have bBU : vsz (.int (bZ * ((r : ℤ) - 2 * tZ))) ≤ 3 * (MB + 1) := by
    rw [MrgKit.vsz_int']; exact hBUisz
  have bWM : vsz (.int (tZ + bZ * ((r : ℤ) - 2 * tZ))) ≤ 3 * (MB + 1) := by
    rw [MrgKit.vsz_int']; exact hWisz
  have bSC : vsz (.int sC) ≤ 3 * (MB + 1) := by
    rw [MrgKit.vsz_int']; exact hSCisz

  -- ## the states
  set S1 : List Val := Pv :: S0 with hS1
  set S2 : List Val := Rv :: Pv :: S0 with hS2
  set S3 : List Val := SHv :: Rv :: Pv :: S0 with hS3
  set S4 : List Val := Jv :: SHv :: Rv :: Pv :: S0 with hS4
  set S5 : List Val := .int tZ :: Rv :: Pv :: S0 with hS5
  set S6 : List Val := .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS6
  set S7 : List Val := .int tZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS7
  set S8 : List Val := .int 0 :: .int tZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS8
  set S9 : List Val := .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS9
  set S10 : List Val := .int 0 :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS10
  set S11 : List Val := SGv :: .int 0 :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS11
  set S12 : List Val := .int bZ :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS12
  set S13 : List Val := .int btZ :: .int bZ :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS13
  set S14 : List Val := .int bZ :: .int btZ :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS14
  set S15 : List Val := .int (bZ * btZ) :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS15
  set S16 : List Val := .int 2 :: .int (bZ * btZ) :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS16
  set S17 : List Val := .int (2 * (bZ * btZ)) :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS17
  set S18 : List Val := .int 1 :: .int (2 * (bZ * btZ)) :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS18
  set S19 : List Val := .int sgC :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS19
  set S20 : List Val := .int 0 :: .int sgC :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS20
  set S21 : List Val := SGv :: .int 0 :: .int sgC :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS21
  set S22 : List Val := .int bZ :: .int sgC :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0 with hS22
  set S23 : List Val := .int tZ :: .int bZ :: .int sgC :: .int btZ :: .int tZ :: Rv :: Pv :: S0 with hS23
  set S24 : List Val := .int 2 :: .int tZ :: .int bZ :: .int sgC :: .int btZ :: .int tZ :: Rv :: Pv :: S0 with hS24
  set S25 : List Val := .int (2 * tZ) :: .int bZ :: .int sgC :: .int btZ :: .int tZ :: Rv :: Pv :: S0 with hS25
  set S26 : List Val := Rv :: .int (2 * tZ) :: .int bZ :: .int sgC :: .int btZ :: .int tZ :: Rv :: Pv :: S0 with hS26
  set S27 : List Val := .int ((r : ℤ) - 2 * tZ) :: .int bZ :: .int sgC :: .int btZ :: .int tZ :: Rv :: Pv :: S0 with hS27
  set S28 : List Val := .int bZ :: .int ((r : ℤ) - 2 * tZ) :: .int sgC :: .int btZ :: .int tZ :: Rv :: Pv :: S0 with hS28
  set S29 : List Val := .int (bZ * ((r : ℤ) - 2 * tZ)) :: .int sgC :: .int btZ :: .int tZ :: Rv :: Pv :: S0 with hS29
  set S30 : List Val := .int tZ :: .int (bZ * ((r : ℤ) - 2 * tZ)) :: .int sgC :: .int btZ :: Rv :: Pv :: S0 with hS30
  set S31 : List Val := .int (tZ + bZ * ((r : ℤ) - 2 * tZ)) :: .int sgC :: .int btZ :: Rv :: Pv :: S0 with hS31
  set S32 : List Val := .int btZ :: .int (tZ + bZ * ((r : ℤ) - 2 * tZ)) :: .int sgC :: Rv :: Pv :: S0 with hS32
  set S33 : List Val := .int sC :: .int sgC :: Rv :: Pv :: S0 with hS33
  -- ## the steps
  have hs1 : WordR main (pickP 6) (fun vs => vs = S0) (fun _ out => out = S1) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 6 + 1 → vsz (S0.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS0, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kp) (k := 6) (by norm_num) hsmall hKp hCs
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 6 S0 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS0, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS1, hS0, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs2 : WordR main (pickP 6) (fun vs => vs = S1) (fun _ out => out = S2) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 6 + 1 → vsz (S1.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS1, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kp) (k := 6) (by norm_num) hsmall hKp hCs
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 6 S1 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS1, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS2, hS1, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs3 : WordR main (pickP 5) (fun vs => vs = S2) (fun _ out => out = S3) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 5 + 1 → vsz (S2.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS2, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kp) (k := 5) (by norm_num) hsmall hKp hCs
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 5 S2 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS2, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS3, hS2, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs4 : WordR main (pickP 5) (fun vs => vs = S3) (fun _ out => out = S4) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 5 + 1 → vsz (S3.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS3, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kp) (k := 5) (by norm_num) hsmall hKp hCs
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 5 S3 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS3, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS4, hS3, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs5 : WordR main (shlP) (fun vs => vs = S4) (fun _ out => out = S5) (fun _ => Cs) := by
    have hcost : Kshl * (isz (j : ℤ) + (sh : ℤ).toNat + isz (sh : ℤ)) ≤ Cs := by
      refine binCost' hKshl ?_ hCs
      have c1 : isz (j : ℤ) ≤ MB := hJisz
      have c3 : sh ≤ MB + 1 := by
        have h4 : 2 ^ sh ≤ 2 ^ (r.size + 1) := by
          calc 2 ^ sh ≤ 2 * r := hsh
            _ ≤ 2 ^ (r.size + 1) := by
                rw [pow_succ]
                calc 2 * r ≤ 2 * 2 ^ r.size :=
                      Nat.mul_le_mul_left 2 (le_of_lt (Nat.lt_size_self r))
                  _ = 2 ^ r.size * 2 := by ring
        have h5 : sh ≤ r.size + 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
        omega
      have c4 : isz (sh : ℤ) ≤ MB + 4 := by
        have h5 : (sh : ℤ).natAbs = sh := by simp
        rw [isz, h5]
        have h6 : sh.size ≤ sh := (Nat.size_le).mpr Nat.lt_two_pow_self
        omega
      have c5 : (sh : ℤ).toNat ≤ sh := by rw [Int.toNat_natCast]
      omega
    refine MrgKit.WordR_conseqC (shlStep (hshl main) (j) (sh) (by positivity) (Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS4]
    · intro out hout
      simpa only [hS5, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have hs6 : WordR main (pickP 0) (fun vs => vs = S5) (fun _ out => out = S6) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 0 + 1 → vsz (S5.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS5, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kp) (k := 0) (by norm_num) hsmall hKp hCs
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 0 S5 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS5, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS6, hS5, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs7 : WordR main (pickP 0) (fun vs => vs = S6) (fun _ out => out = S7) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 0 + 1 → vsz (S6.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS6, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kp) (k := 0) (by norm_num) hsmall hKp hCs
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 0 S6 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS6, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS7, hS6, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs8 : WordR main (pushP (.int 0)) (fun vs => vs = S7) (fun _ out => out = S8) (fun _ => Cs) := by
    have hv : vsz (.int (0 : ℤ)) ≤ 3 * (MB + 1) := by
      have h0 : vsz (.int (0 : ℤ)) = 2 := by decide
      omega
    have hcost := pushCost' (v := .int 0) hKpv hv hCs
    refine MrgKit.WordR_conseqC (MrgKit.pushStep (hpush main) (.int 0) S7 Cs hcost) rfl ?_ le_rfl
    · intro out hout
      simpa only [hS8, hS7, hS0] using hout

  have hs9 : WordR main (ltP) (fun vs => vs = S8) (fun _ out => out = S9) (fun _ => Cs) := by
    have hcost : Klt * (isz (0 : ℤ) + isz tZ) ≤ Cs := by
      refine binCost' hKlt ?_ hCs
      have c0 : isz (0 : ℤ) = 2 := by decide
      have c1 : isz tZ ≤ 3 * (MB + 1) := hTisz
      omega
    refine MrgKit.WordR_conseqC (ltStep (hlt main) (0) (tZ) (.int tZ :: .int tZ :: Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS8]
    · intro out hout
      simpa only [hS9, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have hs10 : WordR main (pushP (.int 0)) (fun vs => vs = S9) (fun _ out => out = S10) (fun _ => Cs) := by
    have hv : vsz (.int (0 : ℤ)) ≤ 3 * (MB + 1) := by
      have h0 : vsz (.int (0 : ℤ)) = 2 := by decide
      omega
    have hcost := pushCost' (v := .int 0) hKpv hv hCs
    refine MrgKit.WordR_conseqC (MrgKit.pushStep (hpush main) (.int 0) S9 Cs hcost) rfl ?_ le_rfl
    · intro out hout
      simpa only [hS10, hS9, hS0] using hout

  have hs11 : WordR main (pickP 10) (fun vs => vs = S10) (fun _ out => out = S11) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 10 + 1 → vsz (S10.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS10, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kp) (k := 10) (by norm_num) hsmall hKp hCs
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 10 S10 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS10, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS11, hS10, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs12 : WordR main (maxP) (fun vs => vs = S11) (fun _ out => out = S12) (fun _ => Cs) := by
    have hcost : Kmax * (isz sgn + isz (0 : ℤ)) ≤ Cs := by
      refine binCost' hKmax ?_ hCs
      have c0 : isz (0 : ℤ) = 2 := by decide
      have c1 : isz sgn ≤ 3 := sgnisz
      omega
    refine MrgKit.WordR_conseqC (MrgKit.maxStep (hmax main) (sgn) (0) (.int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS11]
    · intro out hout
      simpa only [hS12, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have hs13 : WordR main (pickP 1) (fun vs => vs = S12) (fun _ out => out = S13) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 1 + 1 → vsz (S12.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS12, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kp) (k := 1) (by norm_num) hsmall hKp hCs
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 1 S12 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS12, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS13, hS12, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs14 : WordR main (rollP 1) (fun vs => vs = S13) (fun _ out => out = S14) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 1 + 1 → vsz (S13.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS13, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kr) (k := 1) (by norm_num) hsmall hKr hCs
    refine MrgKit.WordR_conseqC (MrgKit.rollStep (hroll main) 1 S13 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS13, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS14, hS13, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs15 : WordR main (mulP) (fun vs => vs = S14) (fun _ out => out = S15) (fun _ => Cs) := by
    have hcost : Kmul * isz (bZ) * isz (btZ) ≤ Cs := mulCost' hKmul (le_trans hBZisz (by omega)) (le_trans hBTisz (by omega)) hCs
    refine MrgKit.WordR_conseqC (MrgKit.mulStep (hmul main) (bZ) (btZ) (.int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS14]
    · intro out hout
      simpa only [hS15, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have hs16 : WordR main (pushP (.int 2)) (fun vs => vs = S15) (fun _ out => out = S16) (fun _ => Cs) := by
    have hv : vsz (.int (2 : ℤ)) ≤ 3 * (MB + 1) := by
      have h0 : vsz (.int (2 : ℤ)) = 4 := by decide
      omega
    have hcost := pushCost' (v := .int 2) hKpv hv hCs
    refine MrgKit.WordR_conseqC (MrgKit.pushStep (hpush main) (.int 2) S15 Cs hcost) rfl ?_ le_rfl
    · intro out hout
      simpa only [hS16, hS15, hS0] using hout

  have hs17 : WordR main (mulP) (fun vs => vs = S16) (fun _ out => out = S17) (fun _ => Cs) := by
    have hcost : Kmul * isz (2) * isz (bZ * btZ) ≤ Cs := mulCost' hKmul h2isz (le_trans hBBisz (by omega)) hCs
    refine MrgKit.WordR_conseqC (MrgKit.mulStep (hmul main) (2) (bZ * btZ) (.int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS16]
    · intro out hout
      simpa only [hS17, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have hs18 : WordR main (pushP (.int 1)) (fun vs => vs = S17) (fun _ out => out = S18) (fun _ => Cs) := by
    have hv : vsz (.int (1 : ℤ)) ≤ 3 * (MB + 1) := by
      have h0 : vsz (.int (1 : ℤ)) = 3 := by decide
      omega
    have hcost := pushCost' (v := .int 1) hKpv hv hCs
    refine MrgKit.WordR_conseqC (MrgKit.pushStep (hpush main) (.int 1) S17 Cs hcost) rfl ?_ le_rfl
    · intro out hout
      simpa only [hS18, hS17, hS0] using hout

  have hs19 : WordR main (subP) (fun vs => vs = S18) (fun _ out => out = S19) (fun _ => Cs) := by
    have hcost : Ksub * (isz (1 : ℤ) + isz (2 * (bZ * btZ))) ≤ Cs := by
      refine binCost' hKsub ?_ hCs
      have c0 : isz (1 : ℤ) = 3 := by decide
      have c1 : isz (2 * (bZ * btZ)) ≤ 4 := h2BBisz
      omega
    refine MrgKit.WordR_conseqC (subStep (hsub main) (1) (2 * (bZ * btZ)) (.int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS18]
    · intro out hout
      simpa only [hS19, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have hs20 : WordR main (pushP (.int 0)) (fun vs => vs = S19) (fun _ out => out = S20) (fun _ => Cs) := by
    have hv : vsz (.int (0 : ℤ)) ≤ 3 * (MB + 1) := by
      have h0 : vsz (.int (0 : ℤ)) = 2 := by decide
      omega
    have hcost := pushCost' (v := .int 0) hKpv hv hCs
    refine MrgKit.WordR_conseqC (MrgKit.pushStep (hpush main) (.int 0) S19 Cs hcost) rfl ?_ le_rfl
    · intro out hout
      simpa only [hS20, hS19, hS0] using hout

  have hs21 : WordR main (pickP 11) (fun vs => vs = S20) (fun _ out => out = S21) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 11 + 1 → vsz (S20.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS20, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kp) (k := 11) (by norm_num) hsmall hKp hCs
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 11 S20 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS20, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS21, hS20, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs22 : WordR main (maxP) (fun vs => vs = S21) (fun _ out => out = S22) (fun _ => Cs) := by
    have hcost : Kmax * (isz sgn + isz (0 : ℤ)) ≤ Cs := by
      refine binCost' hKmax ?_ hCs
      have c0 : isz (0 : ℤ) = 2 := by decide
      have c1 : isz sgn ≤ 3 := sgnisz
      omega
    refine MrgKit.WordR_conseqC (MrgKit.maxStep (hmax main) (sgn) (0) (.int sgC :: .int btZ :: .int tZ :: .int tZ :: Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS21]
    · intro out hout
      simpa only [hS22, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have hs23 : WordR main (rollP 3) (fun vs => vs = S22) (fun _ out => out = S23) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 3 + 1 → vsz (S22.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS22, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kr) (k := 3) (by norm_num) hsmall hKr hCs
    refine MrgKit.WordR_conseqC (MrgKit.rollStep (hroll main) 3 S22 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS22, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS23, hS22, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs24 : WordR main (pushP (.int 2)) (fun vs => vs = S23) (fun _ out => out = S24) (fun _ => Cs) := by
    have hv : vsz (.int (2 : ℤ)) ≤ 3 * (MB + 1) := by
      have h0 : vsz (.int (2 : ℤ)) = 4 := by decide
      omega
    have hcost := pushCost' (v := .int 2) hKpv hv hCs
    refine MrgKit.WordR_conseqC (MrgKit.pushStep (hpush main) (.int 2) S23 Cs hcost) rfl ?_ le_rfl
    · intro out hout
      simpa only [hS24, hS23, hS0] using hout

  have hs25 : WordR main (mulP) (fun vs => vs = S24) (fun _ out => out = S25) (fun _ => Cs) := by
    have hcost : Kmul * isz (2) * isz (tZ) ≤ Cs := mulCost' hKmul h2isz hTisz hCs
    refine MrgKit.WordR_conseqC (MrgKit.mulStep (hmul main) (2) (tZ) (.int bZ :: .int sgC :: .int btZ :: .int tZ :: Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS24]
    · intro out hout
      simpa only [hS25, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have hs26 : WordR main (pickP 5) (fun vs => vs = S25) (fun _ out => out = S26) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 5 + 1 → vsz (S25.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS25, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kp) (k := 5) (by norm_num) hsmall hKp hCs
    refine MrgKit.WordR_conseqC (MrgKit.pickStep (hpick main) 5 S25 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS25, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS26, hS25, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs27 : WordR main (subP) (fun vs => vs = S26) (fun _ out => out = S27) (fun _ => Cs) := by
    have hcost : Ksub * (isz (r : ℤ) + isz (2 * tZ)) ≤ Cs := by
      refine binCost' hKsub ?_ hCs
      have c1 : isz (r : ℤ) ≤ MB := hiszR
      have c2 : isz (2 * tZ) ≤ 3 * (MB + 1) := h2Tisz
      omega
    refine MrgKit.WordR_conseqC (subStep (hsub main) ((r : ℤ)) (2 * tZ) (.int bZ :: .int sgC :: .int btZ :: .int tZ :: Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS26]
    · intro out hout
      simpa only [hS27, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have hs28 : WordR main (rollP 1) (fun vs => vs = S27) (fun _ out => out = S28) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 1 + 1 → vsz (S27.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS27, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kr) (k := 1) (by norm_num) hsmall hKr hCs
    refine MrgKit.WordR_conseqC (MrgKit.rollStep (hroll main) 1 S27 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS27, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS28, hS27, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs29 : WordR main (mulP) (fun vs => vs = S28) (fun _ out => out = S29) (fun _ => Cs) := by
    have hcost : Kmul * isz (bZ) * isz ((r : ℤ) - 2 * tZ) ≤ Cs := mulCost' hKmul (le_trans hBZisz (by omega)) hR2Tisz hCs
    refine MrgKit.WordR_conseqC (MrgKit.mulStep (hmul main) (bZ) ((r : ℤ) - 2 * tZ) (.int sgC :: .int btZ :: .int tZ :: Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS28]
    · intro out hout
      simpa only [hS29, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have hs30 : WordR main (rollP 3) (fun vs => vs = S29) (fun _ out => out = S30) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 3 + 1 → vsz (S29.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS29, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kr) (k := 3) (by norm_num) hsmall hKr hCs
    refine MrgKit.WordR_conseqC (MrgKit.rollStep (hroll main) 3 S29 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS29, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS30, hS29, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs31 : WordR main (addP) (fun vs => vs = S30) (fun _ out => out = S31) (fun _ => Cs) := by
    have hcost : Kadd * (isz tZ + isz (bZ * ((r : ℤ) - 2 * tZ))) ≤ Cs := by
      refine binCost' hKadd ?_ hCs
      have c1 : isz tZ ≤ 3 * (MB + 1) := hTisz
      have c2 : isz (bZ * ((r : ℤ) - 2 * tZ)) ≤ 3 * (MB + 1) := hBUisz
      omega
    refine MrgKit.WordR_conseqC (MrgKit.addStep (hadd main) (tZ) (bZ * ((r : ℤ) - 2 * tZ)) (.int sgC :: .int btZ :: Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS30]
    · intro out hout
      simpa only [hS31, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have hs32 : WordR main (rollP 2) (fun vs => vs = S31) (fun _ out => out = S32) (fun _ => Cs) := by
    have hsmall : ∀ i, i < 2 + 1 → vsz (S31.getD i .nil) ≤ 3 * (MB + 1) := by
      intro i hi
      interval_cases i <;>
        simp only [hS31, hS0, List.getD_cons_zero, List.getD_cons_succ] <;>
        first | exact bW1 | exact bW2 | exact bJ | exact bSH | exact bSG | exact bR |
          exact bP | exact bT | exact bBT | exact bBZ | exact b0 | exact b1 | exact b2 |
          exact bBB | exact b2BB | exact bSGC | exact b2T | exact bR2T | exact bBU |
          exact bW | exact bSC | omega
    have hcost := pickrollCost (Kp := Kr) (k := 2) (by norm_num) hsmall hKr hCs
    refine MrgKit.WordR_conseqC (MrgKit.rollStep (hroll main) 2 S31 ?_ Cs hcost) rfl ?_ le_rfl
    · simp only [hS31, hS0, List.length_cons]
      omega
    · intro out hout
      simpa only [hS32, hS31, hS0, List.getD_cons_zero, List.getD_cons_succ,
        List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] using hout

  have hs33 : WordR main (mulP) (fun vs => vs = S32) (fun _ out => out = S33) (fun _ => Cs) := by
    have hcost : Kmul * isz (btZ) * isz (tZ + bZ * ((r : ℤ) - 2 * tZ)) ≤ Cs := mulCost' hKmul (le_trans hBTisz (by omega)) hWisz hCs
    refine MrgKit.WordR_conseqC (MrgKit.mulStep (hmul main) (btZ) (tZ + bZ * ((r : ℤ) - 2 * tZ)) (.int sgC :: Rv :: Pv :: S0) Cs hcost) ?_ ?_ le_rfl
    · rw [hS32]
    · intro out hout
      simpa only [hS33, hS0, hshlval, hbZ, hsgC, hsC, hbtZ, htZ,
        List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
        List.eraseIdx_cons_succ] using hout

  have u1 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S1) (fun _ => Cs) := hs1
  have u2 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S2) (fun _ => 2 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u1 hs2) (by omega)
  have u3 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S3) (fun _ => 3 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u2 hs3) (by omega)
  have u4 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S4) (fun _ => 4 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u3 hs4) (by omega)
  have u5 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S5) (fun _ => 5 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u4 hs5) (by omega)
  have u6 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S6) (fun _ => 6 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u5 hs6) (by omega)
  have u7 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S7) (fun _ => 7 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u6 hs7) (by omega)
  have u8 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S8) (fun _ => 8 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u7 hs8) (by omega)
  have u9 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S9) (fun _ => 9 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u8 hs9) (by omega)
  have u10 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S10) (fun _ => 10 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u9 hs10) (by omega)
  have u11 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S11) (fun _ => 11 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u10 hs11) (by omega)
  have u12 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S12) (fun _ => 12 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u11 hs12) (by omega)
  have u13 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S13) (fun _ => 13 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u12 hs13) (by omega)
  have u14 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S14) (fun _ => 14 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u13 hs14) (by omega)
  have u15 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S15) (fun _ => 15 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u14 hs15) (by omega)
  have u16 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S16) (fun _ => 16 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u15 hs16) (by omega)
  have u17 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S17) (fun _ => 17 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u16 hs17) (by omega)
  have u18 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S18) (fun _ => 18 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u17 hs18) (by omega)
  have u19 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S19) (fun _ => 19 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u18 hs19) (by omega)
  have u20 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S20) (fun _ => 20 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u19 hs20) (by omega)
  have u21 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S21) (fun _ => 21 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u20 hs21) (by omega)
  have u22 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S22) (fun _ => 22 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u21 hs22) (by omega)
  have u23 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S23) (fun _ => 23 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u22 hs23) (by omega)
  have u24 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S24) (fun _ => 24 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u23 hs24) (by omega)
  have u25 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S25) (fun _ => 25 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u24 hs25) (by omega)
  have u26 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S26) (fun _ => 26 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u25 hs26) (by omega)
  have u27 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S27) (fun _ => 27 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u26 hs27) (by omega)
  have u28 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S28) (fun _ => 28 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u27 hs28) (by omega)
  have u29 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S29) (fun _ => 29 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u28 hs29) (by omega)
  have u30 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S30) (fun _ => 30 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u29 hs30) (by omega)
  have u31 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S31) (fun _ => 31 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u30 hs31) (by omega)
  have u32 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S32) (fun _ => 32 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u31 hs32) (by omega)
  have u33 : WordR main _ (fun vs => vs = S0) (fun _ out => out = S33) (fun _ => 33 * Cs) :=
    WordR_costNorm (MrgKit.WordR_seqC u32 hs33) (by omega)
  refine MrgKit.WordR_weaken u33 (fun vs hvs => hvs) ?_ ?_
  · intro vs out hvs hq
    rw [hq]
  · intro vs hvs
    rw [hCs]
    nlinarith [Nat.zero_le Kx, hMB1]
end Work.SynFFT
