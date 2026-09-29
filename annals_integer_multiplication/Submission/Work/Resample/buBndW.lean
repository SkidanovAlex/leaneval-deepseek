import Mathlib
import Submission.Work.Resample.buWtKit

namespace Work.Resample

open HvdH
open Work.Fx

/-!
# `Work.Resample.buBndW`: the word computing the guard bound `auBnd p + 1`

The guard bound of the `B̃` weight table is `auBnd p = (p+10)·2^(3p+100)`, an integer of about
`4p` bits.  This file builds the small word that, from the single value `p` (with `100 ≤ p`),
computes `auBnd p + 1` on the value stack.

The word is the chain

* `dup` (`[p] → [p,p]`), `pushVal 3`, `mulS` (`3p`), `pushVal 100`, `add` (`3p+100`),
* `swap` (`[p, 3p+100]`), `dup`, `pushVal 10`, `add` (`p+10`),
* `swap`, `drop` (removing the working copy of `p`), so that the window is `[p+10, 3p+100]`,
* `shl` (`(p+10)·2^(3p+100)`), `pushVal 1`, `add`.

Every intermediate value has `isz ≤ buSZ p` (`isz_le_buSZ_pow_p`, `isz_const_le_buSZ`,
`isz_le_buSZ_of_lin`, `isz_auBnd_le_buSZ`), so every step costs at most `buSBW p Λ`, where `Λ` is
the sum of the constants of the library words involved.  The fourteen steps cost at most
`14·buSBW p Λ ≤ 14·(Λ·10^12)·(p+1)^4`, which `le_powK` absorbs into a single `K (p+1)^K`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- `3p ≤ 4^p`, hence `3p < 2^(2p)`. -/
theorem buBndW_three_mul_le_four_pow (p : ℕ) : 3 * p ≤ 4 ^ p := by
  have hp : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
  rcases Nat.lt_or_ge p 2 with h | h
  · interval_cases p <;> norm_num
  · have h3 : (3 : ℕ) ≤ 2 ^ p := by
      calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h
    calc 3 * p ≤ 3 * 2 ^ p := Nat.mul_le_mul_left 3 hp
      _ = 2 ^ p * 3 := by ring
      _ ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul_left _ h3
      _ = 4 ^ p := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
          congr 1
          ring

theorem buBndW (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ), 100 ≤ p →
      Work.Resample.Pipe main prog [HvdH.Val.int (p : ℤ)] [HvdH.Val.int (Work.Resample.auBnd p + 1)]
        (K * (p + 1) ^ K) := by
  obtain ⟨dupProg, Kdup, hdup⟩ := KL.dup
  obtain ⟨dropProg, Kdr, hdr⟩ := KL.drop
  obtain ⟨swapProg, Ksw, hsw⟩ := KL.swap
  obtain ⟨pushProg, Kpv, hpv⟩ := KL.pushVal
  obtain ⟨addProg, Kadd, hadd⟩ := IL.add
  obtain ⟨mulProg, Kmul, hmul⟩ := IL.mulS
  obtain ⟨shlProg, Kshl, hshl⟩ := IL.shl
  let Λ : ℕ := Kdup + Kdr + Ksw + Kpv + Kadd + Kmul + Kshl + 1
  let K : ℕ := 8 * ((14 * (Λ * 1000000 ^ 2) + 1) + 4) + 8
  let prog : Cmd := Cmd.seq dupProg (Cmd.seq (pushProg (.int 3)) (Cmd.seq mulProg (Cmd.seq (pushProg (.int 100)) (Cmd.seq addProg (Cmd.seq swapProg (Cmd.seq dupProg (Cmd.seq (pushProg (.int 10)) (Cmd.seq addProg (Cmd.seq swapProg (Cmd.seq dropProg (Cmd.seq shlProg (Cmd.seq (pushProg (.int 1)) (addProg)))))))))))))
  refine ⟨prog, K, ?_⟩
  intro main p hp
  -- ## size bounds: every value occurring below has `isz ≤ buSZ p`
  have hzp : isz ((p : ℤ)) ≤ buSZ p :=
    isz_le_buSZ_pow_p (by rw [Int.natAbs_natCast]; exact le_of_lt (Nat.lt_two_pow_self (n := p)))
  have hz3 : isz ((3 : ℤ)) ≤ buSZ p := isz_const_le_buSZ p 3 (by omega)
  have hz100 : isz ((100 : ℤ)) ≤ buSZ p := isz_const_le_buSZ p 100 (by omega)
  have hz10 : isz ((10 : ℤ)) ≤ buSZ p := isz_const_le_buSZ p 10 (by omega)
  have hz1 : isz ((1 : ℤ)) ≤ buSZ p := isz_const_le_buSZ p 1 (by omega)
  have hz3p : isz (((3 * p : ℕ)) : ℤ) ≤ buSZ p := by
    refine isz_le_buSZ_pow_2p ?_
    rw [Int.natAbs_natCast]
    calc 3 * p ≤ 4 ^ p := buBndW_three_mul_le_four_pow p
      _ = 2 ^ (2 * p) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hzp10 : isz (((p + 10 : ℕ)) : ℤ) ≤ buSZ p := by
    refine isz_le_buSZ_of_lin (A := p + 4) (by omega) ?_
    rw [Int.natAbs_natCast]
    have hp1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    have hple : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
    calc p + 10 ≤ 16 * 2 ^ p := by nlinarith
      _ = 2 ^ (p + 4) := by rw [pow_add]; norm_num; ring
  have hzp3100n : 3 * p + 100 ≤ buSZ p := by simp only [buSZ]; omega
  have hzp3100 : isz (((3 * p + 100 : ℕ)) : ℤ) ≤ buSZ p := by
    refine isz_le_buSZ_of_lin (A := p + 8) (by omega) ?_
    rw [Int.natAbs_natCast]
    calc 3 * p + 100 ≤ 103 * 2 ^ p := three_mul_add_le p
      _ ≤ 256 * 2 ^ p := by nlinarith [Nat.two_pow_pos p]
      _ = 2 ^ (p + 8) := by rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_add, Nat.add_comm]
  have hzX : isz ((((p + 10 : ℕ)) : ℤ) * 2 ^ (3 * p + 100)) ≤ buSZ p := by
    simpa only [auBnd, auEn, auPrec] using isz_auBnd_le_buSZ p
  -- ## the constants are all `≤ Λ`
  have hΛdup : Kdup ≤ Λ := by simp only [Λ]; omega
  have hΛdr : Kdr ≤ Λ := by simp only [Λ]; omega
  have hΛsw : Ksw ≤ Λ := by simp only [Λ]; omega
  have hΛpv : Kpv ≤ Λ := by simp only [Λ]; omega
  have hΛadd : Kadd ≤ Λ := by simp only [Λ]; omega
  have hΛmul : Kmul ≤ Λ := by simp only [Λ]; omega
  have hΛshl : Kshl ≤ Λ := by simp only [Λ]; omega
  have hbig : 1 ≤ buSZ p := by have := buSZ_ge p; omega
  -- ## the fourteen steps, each of cost `≤ buSBW p Λ`
  have s1 : Pipe main dupProg [.int (p : ℤ)] [.int (p : ℤ), .int (p : ℤ)] (buSBW p Λ) := by
    refine Pipe.le (Pipe.dup main hdup (.int (p : ℤ))) ?_
    rw [vsz_int]
    exact le_buSBW_one hΛdup hzp
  have s2 : Pipe main (pushProg (.int 3)) [.int (p : ℤ), .int (p : ℤ)]
      [.int (3 : ℤ), .int (p : ℤ), .int (p : ℤ)] (buSBW p Λ) := by
    refine Pipe.le (Pipe.pushOnAny (hpv main (.int 3))) ?_
    rw [vsz_int]
    exact le_buSBW_one hΛpv hz3
  have s3 : Pipe main mulProg [.int (3 : ℤ), .int (p : ℤ), .int (p : ℤ)]
      [.int (((3 * p : ℕ)) : ℤ), .int (p : ℤ)] (buSBW p Λ) := by
    have h0 := Pipe.binOp (hmul main) (a := (3 : ℤ)) (b := (p : ℤ)) trivial
    have h1 : Pipe main mulProg ([.int (3 : ℤ), .int (p : ℤ)] ++ [.int (p : ℤ)])
        ([.int ((3 : ℤ) * (p : ℤ))] ++ [.int (p : ℤ)])
        (Kmul * isz (3 : ℤ) * isz (p : ℤ)) :=
      Pipe.appendTail [.int (p : ℤ)] h0
    have hcast : (3 : ℤ) * (p : ℤ) = (((3 * p : ℕ)) : ℤ) := by push_cast; ring
    refine Pipe.le (Pipe.rw h1 (by rw [hcast]; rfl)) ?_
    exact le_buSBW_mul hΛmul hz3 hzp
  have s4 : Pipe main (pushProg (.int 100))
      [.int (((3 * p : ℕ)) : ℤ), .int (p : ℤ)]
      [.int (100 : ℤ), .int (((3 * p : ℕ)) : ℤ), .int (p : ℤ)] (buSBW p Λ) := by
    refine Pipe.le (Pipe.pushOnAny (hpv main (.int 100))) ?_
    rw [vsz_int]
    exact le_buSBW_one hΛpv hz100
  have s5 : Pipe main addProg
      [.int (100 : ℤ), .int (((3 * p : ℕ)) : ℤ), .int (p : ℤ)]
      [.int (((3 * p + 100 : ℕ)) : ℤ), .int (p : ℤ)] (buSBW p Λ) := by
    have h0 := Pipe.binOp (hadd main) (a := (100 : ℤ)) (b := (((3 * p : ℕ)) : ℤ)) trivial
    have h1 : Pipe main addProg ([.int (100 : ℤ), .int (((3 * p : ℕ)) : ℤ)] ++ [.int (p : ℤ)])
        ([.int ((100 : ℤ) + (((3 * p : ℕ)) : ℤ))] ++ [.int (p : ℤ)])
        (Kadd * (isz (100 : ℤ) + isz (((3 * p : ℕ)) : ℤ))) :=
      Pipe.appendTail [.int (p : ℤ)] h0
    have hcast : (100 : ℤ) + (((3 * p : ℕ)) : ℤ) = (((3 * p + 100 : ℕ)) : ℤ) := by
      push_cast; ring
    refine Pipe.le (Pipe.rw h1 (by rw [hcast]; rfl)) ?_
    exact le_buSBW_two hΛadd hz100 hz3p
  have s6 : Pipe main swapProg
      [.int (((3 * p + 100 : ℕ)) : ℤ), .int (p : ℤ)]
      [.int (p : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)] (buSBW p Λ) := by
    refine Pipe.le (Pipe.swap main hsw (.int (((3 * p + 100 : ℕ)) : ℤ)) (.int (p : ℤ))) ?_
    rw [vsz_int, vsz_int]
    exact le_buSBW_three hΛsw hzp3100 hzp hbig
  have s7 : Pipe main dupProg
      [.int (p : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)]
      [.int (p : ℤ), .int (p : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)] (buSBW p Λ) := by
    refine Pipe.le
      (Pipe.appendTail [.int (((3 * p + 100 : ℕ)) : ℤ)] (Pipe.dup main hdup (.int (p : ℤ)))) ?_
    rw [vsz_int]
    exact le_buSBW_one hΛdup hzp
  have s8 : Pipe main (pushProg (.int 10))
      [.int (p : ℤ), .int (p : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)]
      [.int (10 : ℤ), .int (p : ℤ), .int (p : ℤ),
        .int (((3 * p + 100 : ℕ)) : ℤ)] (buSBW p Λ) := by
    refine Pipe.le (Pipe.pushOnAny (hpv main (.int 10))) ?_
    rw [vsz_int]
    exact le_buSBW_one hΛpv hz10
  have s9 : Pipe main addProg
      [.int (10 : ℤ), .int (p : ℤ), .int (p : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)]
      [.int (((p + 10 : ℕ)) : ℤ), .int (p : ℤ),
        .int (((3 * p + 100 : ℕ)) : ℤ)] (buSBW p Λ) := by
    have h0 := Pipe.binOp (hadd main) (a := (10 : ℤ)) (b := (p : ℤ)) trivial
    have h1 : Pipe main addProg
        ([.int (10 : ℤ), .int (p : ℤ)] ++ ([.int (p : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)]))
        ([.int ((10 : ℤ) + (p : ℤ))] ++ ([.int (p : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)]))
        (Kadd * (isz (10 : ℤ) + isz (p : ℤ))) :=
      Pipe.appendTail _ h0
    have hcast : (10 : ℤ) + (p : ℤ) = (((p + 10 : ℕ)) : ℤ) := by push_cast; ring
    refine Pipe.le (Pipe.rw h1 (by rw [hcast]; rfl)) ?_
    exact le_buSBW_two hΛadd hz10 hzp
  have s10 : Pipe main swapProg
      [.int (((p + 10 : ℕ)) : ℤ), .int (p : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)]
      [.int (p : ℤ), .int (((p + 10 : ℕ)) : ℤ),
        .int (((3 * p + 100 : ℕ)) : ℤ)] (buSBW p Λ) := by
    refine Pipe.le (Pipe.appendTail [.int (((3 * p + 100 : ℕ)) : ℤ)]
      (Pipe.swap main hsw (.int (((p + 10 : ℕ)) : ℤ)) (.int (p : ℤ)))) ?_
    rw [vsz_int, vsz_int]
    exact le_buSBW_three hΛsw hzp10 hzp hbig
  have s11 : Pipe main dropProg
      [.int (p : ℤ), .int (((p + 10 : ℕ)) : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)]
      [.int (((p + 10 : ℕ)) : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)] (buSBW p Λ) := by
    refine Pipe.le (Pipe.appendTail [.int (((p + 10 : ℕ)) : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)]
      (Pipe.drop main hdr (.int (p : ℤ)))) ?_
    rw [vsz_int]
    exact le_buSBW_one hΛdr hzp
  have s12 : Pipe main shlProg
      [.int (((p + 10 : ℕ)) : ℤ), .int (((3 * p + 100 : ℕ)) : ℤ)]
      [.int ((((p + 10 : ℕ)) : ℤ) * 2 ^ (3 * p + 100))] (buSBW p Λ) := by
    have hab : (0 : ℤ) ≤ (((3 * p + 100 : ℕ)) : ℤ) := by positivity
    have h0 := Pipe.binOp (hshl main) (a := (((p + 10 : ℕ)) : ℤ))
      (b := (((3 * p + 100 : ℕ)) : ℤ)) hab
    have hD : (((p + 10 : ℕ)) : ℤ) * 2 ^ ((((3 * p + 100 : ℕ)) : ℤ)).toNat
        = (((p + 10 : ℕ)) : ℤ) * 2 ^ (3 * p + 100) := by
      rw [Int.toNat_natCast]
    refine Pipe.le (Pipe.rw h0 (by rw [hD])) ?_
    rw [Int.toNat_natCast]
    exact le_buSBW_three hΛshl hzp10 hzp3100n hzp3100
  have s13 : Pipe main (pushProg (.int 1))
      [.int ((((p + 10 : ℕ)) : ℤ) * 2 ^ (3 * p + 100))]
      [.int (1 : ℤ), .int ((((p + 10 : ℕ)) : ℤ) * 2 ^ (3 * p + 100))] (buSBW p Λ) := by
    refine Pipe.le (Pipe.pushOnAny (hpv main (.int 1))) ?_
    rw [vsz_int]
    exact le_buSBW_one hΛpv hz1
  have s14 : Pipe main addProg
      [.int (1 : ℤ), .int ((((p + 10 : ℕ)) : ℤ) * 2 ^ (3 * p + 100))]
      [.int (auBnd p + 1)] (buSBW p Λ) := by
    have h0 := Pipe.binOp (hadd main) (a := (1 : ℤ))
      (b := (((p + 10 : ℕ)) : ℤ) * 2 ^ (3 * p + 100)) trivial
    have hval : (1 : ℤ) + (((p + 10 : ℕ)) : ℤ) * 2 ^ (3 * p + 100) = auBnd p + 1 := by
      rw [auBnd_eq p, auPrec_eq p]
      ring
    refine Pipe.le (Pipe.rw h0 (by rw [hval])) ?_
    exact le_buSBW_two hΛadd hz1 hzX
  -- ## assembly: the chain of the fourteen words
  have hchain : Pipe main prog [.int (p : ℤ)] [.int (auBnd p + 1)] (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ)))))))))))))) :=
    Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 (Pipe.comp s6 (Pipe.comp s7 (Pipe.comp s8 (Pipe.comp s9 (Pipe.comp s10 (Pipe.comp s11 (Pipe.comp s12 (Pipe.comp s13 (s14)))))))))))))
  have hcb : buSBW p Λ ≤ (Λ * 1000000 ^ 2) * (p + 1) ^ 4 := buSBW_le_pow p Λ
  have h14 : 14 * ((Λ * 1000000 ^ 2) * (p + 1) ^ 4) ≤ K * (p + 1) ^ K := by
    have h1 : 14 * ((Λ * 1000000 ^ 2) * (p + 1) ^ 4)
        = (14 * (Λ * 1000000 ^ 2)) * (p + 1) ^ 4 := by ring
    rw [h1]
    have hpK := le_powK (p := p) (c := 14 * (Λ * 1000000 ^ 2) + 1) (d := 4)
      (by omega) (by omega)
    refine le_trans (Nat.mul_le_mul_right _ (Nat.le_succ _)) ?_
    simpa only [K] using hpK
  exact Pipe.le hchain (le_trans (by omega : (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ)))))))))))))) ≤ 14 * ((Λ * 1000000 ^ 2) * (p + 1) ^ 4)) h14)

end Work.Resample
