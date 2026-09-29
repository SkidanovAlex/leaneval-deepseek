import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.blkLvlSuffixKit

/-!
# SynFFT: the "take `m/2` and append" step

`takeAppendStep` builds the word

`ofList F :: ofList S :: int m :: rest  ↦  ofList (F.take (m/2) ++ S) :: int m :: rest`

at linear cost, out of the library words `Layout.take`, `Layout.append`, `Int.fdiv` and
`Kernel.dup/pick`, sequenced with `MrgKit.WordR_seqC`:

* `push (int 2)`,
* `pick 3` (copies `int m` to the top, leaving the original in place),
* `fdiv` (`a = m`, `b = 2`, so `int (m/2)`),
* `Layout.take` (`take (m/2)` of `F`),
* `Layout.append` (append `S`).

Costs are bounded by `N = vsz (ofList F) + vsz (ofList S) + m + 1` using
`isz_nat_le` (`isz (m : ℤ) ≤ 2 (m+1)`), `vsz_ofList_take_le` and
`vsz (ofList xs) ≥ 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-- `isz (2 : ℤ) ≤ 4`. -/
lemma isz_two_le : isz (2 : ℤ) ≤ 4 := by
  have h1 : ((2 : ℤ)).natAbs = 2 := by norm_num
  have h2 : (2 : ℕ).size ≤ 2 := (Nat.size_le).mpr (by norm_num)
  simp only [isz, h1]
  omega

/-- The size of the first four values of the intermediate stack is the sum of the individual
sizes. -/
lemma take4_sum (m : ℕ) (F S t : List Val) :
    (List.map vsz (List.take (3 + 1)
        (Val.int (2 : ℤ) :: ofList F :: ofList S :: Val.int (m : ℤ) :: t))).sum
      = isz (2 : ℤ) + vsz (ofList F) + vsz (ofList S) + isz (m : ℤ) := by
  simp [MrgKit.vsz_int']
  ring

theorem takeAppendStep (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (m : ℕ) (F S t : List HvdH.Val),
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList F :: HvdH.ofList S :: HvdH.Val.int (m : ℤ) :: t)
        (fun _ out => out = HvdH.ofList ((F.take (m / 2)) ++ S) :: HvdH.Val.int (m : ℤ) :: t)
        (fun _ => K * (HvdH.vsz (HvdH.ofList F) + HvdH.vsz (HvdH.ofList S) + m + 1) + K) := by
  obtain ⟨pickP, Kp, hkp⟩ := hk.pick
  obtain ⟨pushP, Kpv, hkpv⟩ := hk.pushVal
  obtain ⟨fdivP, Kf, hfdiv⟩ := hi.fdiv
  obtain ⟨takeP, Kt, htake⟩ := hl.take
  obtain ⟨appP, Kap, happ⟩ := hl.append
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (pushP (.int 2)) (pickP 3)) fdivP) takeP) appP,
    2 * Kpv + 32 * Kp + 8 * Kf + 4 * Kt + 2 * Kap, ?_⟩
  intro main m F S t
  set N : ℕ := vsz (ofList F) + vsz (ofList S) + m + 1 with hN
  have hA : 1 ≤ vsz (ofList F) := by
    rw [MrgKit.vsz_ofList]; omega
  have hB : 1 ≤ vsz (ofList S) := by
    rw [MrgKit.vsz_ofList]; omega
  have hFN : vsz (ofList F) ≤ N := by omega
  have hSN : vsz (ofList S) ≤ N := by omega
  have h1N : 1 ≤ N := by omega
  have hmu : isz (m : ℤ) ≤ 2 * N := by
    have := isz_nat_le m
    omega
  have hhalf : isz (((m / 2 : ℕ) : ℤ)) ≤ 2 * N := by
    have := isz_nat_le (m / 2)
    omega
  have htakele : vsz (ofList (F.take (m / 2))) ≤ N :=
    le_trans (vsz_ofList_take_le F (m / 2)) hFN
  -- step 1: push `int 2`
  have h1 : WordR main (pushP (.int 2))
      (fun vs => vs = ofList F :: ofList S :: Val.int (m : ℤ) :: t)
      (fun _ out => out = Val.int 2 :: ofList F :: ofList S :: Val.int (m : ℤ) :: t)
      (fun _ => 2 * Kpv * N) := by
    refine MrgKit.pushStep (hkpv main) (Val.int 2)
      (ofList F :: ofList S :: Val.int (m : ℤ) :: t) (2 * Kpv * N) ?_
    rw [MrgKit.vsz_int']
    have h : isz (2 : ℤ) + 1 ≤ 2 * N := by
      have := isz_two_le
      omega
    calc Kpv * (isz (2 : ℤ) + 1) ≤ Kpv * (2 * N) := Nat.mul_le_mul_left Kpv h
      _ = 2 * Kpv * N := by ring
  -- step 2: `pick 3` copies `int m` to the top
  have h2 : WordR main (pickP 3)
      (fun vs => vs = Val.int 2 :: ofList F :: ofList S :: Val.int (m : ℤ) :: t)
      (fun _ out => out =
        Val.int (m : ℤ) :: Val.int 2 :: ofList F :: ofList S :: Val.int (m : ℤ) :: t)
      (fun _ => 32 * Kp * N) := by
    refine MrgKit.pickStep (hkp main) 3
      (Val.int 2 :: ofList F :: ofList S :: Val.int (m : ℤ) :: t)
      (by simp only [List.length_cons]; omega) (32 * Kp * N) ?_
    rw [take4_sum]
    have h : isz (2 : ℤ) + vsz (ofList F) + vsz (ofList S) + isz (m : ℤ) + 1 ≤ 8 * N := by
      have := isz_two_le
      omega
    calc Kp * (3 + 1) * (isz (2 : ℤ) + vsz (ofList F) + vsz (ofList S) + isz (m : ℤ) + 1)
        ≤ Kp * (3 + 1) * (8 * N) := Nat.mul_le_mul_left _ h
      _ = 32 * Kp * N := by ring
  -- step 3: `fdiv` computes `m / 2`
  have h3 : WordR main fdivP
      (fun vs => vs =
        Val.int (m : ℤ) :: Val.int 2 :: ofList F :: ofList S :: Val.int (m : ℤ) :: t)
      (fun _ out => out =
        Val.int (((m / 2 : ℕ) : ℤ)) :: ofList F :: ofList S :: Val.int (m : ℤ) :: t)
      (fun _ => 8 * Kf * N) := by
    refine MrgKit.WordR_weaken (fdivStep (hfdiv main) (m : ℤ) 2
      (ofList F :: ofList S :: Val.int (m : ℤ) :: t) (by norm_num) (8 * Kf * N) ?_)
      (fun vs h => h) (fun vs out h hout => ?_) (fun vs h => le_rfl)
    · calc Kf * isz (m : ℤ) * isz (2 : ℤ) = Kf * (isz (m : ℤ) * isz (2 : ℤ)) := by ring
        _ ≤ Kf * ((2 * N) * 4) := Nat.mul_le_mul_left Kf (Nat.mul_le_mul hmu isz_two_le)
        _ = 8 * Kf * N := by ring
    · rw [hout, int_fdiv_two]
  -- step 4: `take (m/2)` of `F`
  have h4 : WordR main takeP
      (fun vs => vs =
        Val.int (((m / 2 : ℕ) : ℤ)) :: ofList F :: ofList S :: Val.int (m : ℤ) :: t)
      (fun _ out => out = ofList (F.take (m / 2)) :: ofList S :: Val.int (m : ℤ) :: t)
      (fun _ => 4 * Kt * N) := by
    refine MrgKit.layTakeStep (htake main) (m / 2) (((m / 2 : ℕ) : ℤ)) rfl F
      (ofList S :: Val.int (m : ℤ) :: t) (4 * Kt * N) ?_
    have h : vsz (ofList F) + isz (((m / 2 : ℕ) : ℤ)) + 1 ≤ 4 * N := by omega
    calc Kt * (vsz (ofList F) + isz (((m / 2 : ℕ) : ℤ)) + 1) ≤ Kt * (4 * N) :=
        Nat.mul_le_mul_left Kt h
      _ = 4 * Kt * N := by ring
  -- step 5: append `S`
  have h5 : WordR main appP
      (fun vs => vs = ofList (F.take (m / 2)) :: ofList S :: Val.int (m : ℤ) :: t)
      (fun _ out => out = ofList ((F.take (m / 2)) ++ S) :: Val.int (m : ℤ) :: t)
      (fun _ => 2 * Kap * N) := by
    refine MrgKit.appStep (happ main) (F.take (m / 2)) S (Val.int (m : ℤ) :: t) (2 * Kap * N) ?_
    have h : vsz (ofList (F.take (m / 2))) + 1 ≤ 2 * N := by omega
    calc Kap * (vsz (ofList (F.take (m / 2))) + 1) ≤ Kap * (2 * N) := Nat.mul_le_mul_left Kap h
      _ = 2 * Kap * N := by ring
  have h12 := MrgKit.WordR_seqC h1 h2
  have h123 := MrgKit.WordR_seqC h12 h3
  have h1234 := MrgKit.WordR_seqC h123 h4
  have h12345 := MrgKit.WordR_seqC h1234 h5
  refine MrgKit.WordR_weaken h12345 (fun vs h => h) (fun vs out h hout => hout) ?_
  intro vs hvs
  rw [hN]
  ring_nf
  omega

end Work.SynFFT
