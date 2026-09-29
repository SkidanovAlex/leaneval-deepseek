import Mathlib
import Submission.Work.Resample.buDivDefs

namespace Work.Resample

open HvdH

/-!
# Final step of the shift word of `Work.Resample.buWdDiv`

`Work.Resample.buWdDiv` forms the shift exponent
`k = auPrec p - p + (2α² - 2) = buDivK p α` on top of the dividend `Ad`, then applies
`IntLib.shrT` to compute `Ad /ᵗ 2^k`.  This module isolates the very last step: given the
window `[int (buDivK p α), int Ad, int p, int α]`, swap the top two entries and shift,
producing `[int (tdiv Ad 2^k), int p, int α]`.

The arithmetic facts are `buDivK_eq` (the value of `buDivK p α` as a natural number cast to `ℤ`),
`buDivK_toNat` (its `toNat` is exactly the exponent `auPrec p - p + (2α² - 2)` of the target
statement) and `isz_buDivK_le` (its size never exceeds the uniform bound `buSZ p`).
-/

/-- The shift exponent formed by the word equals `2p + 98 + 2α²`. -/
theorem buDivK_eq (p α : ℕ) : buDivK p α = ((2 * p + 98 + 2 * α ^ 2 : ℕ) : ℤ) := by
  simp only [buDivK, buDivZ5, buDivZ4, buDivZ3, buDivZ2, buDivZ1]
  push_cast
  ring

/-- `buDivK p α` is the exponent `auPrec p - p + (2α² - 2)` written in `ℕ`. -/
theorem buDivK_toNat {p α : ℕ} (hα : 1 ≤ α) :
    (buDivK p α).toNat = auPrec p - p + (2 * α ^ 2 - 2) := by
  rw [buDivK_eq]
  simp only [Int.toNat_natCast, auPrec]
  have h2 : 2 ≤ 2 * α ^ 2 := by nlinarith
  rw [show 2 * α ^ 2 = (2 * α ^ 2 - 2) + 2 from (Nat.sub_add_cancel h2).symm]
  omega

/-- `buDivK p α` is nonnegative. -/
theorem buDivK_nonneg (p α : ℕ) : 0 ≤ buDivK p α := by
  rw [buDivK_eq]; exact Int.natCast_nonneg _

/-- The shift exponent fits in the uniform size bound `buSZ p` (when `α² < p`). -/
theorem isz_buDivK_le {p α : ℕ} (hαp : α ^ 2 < p) : isz (buDivK p α) ≤ buSZ p := by
  rw [buDivK_eq]
  refine isz_natCast_le_buSZ_of (A := p + 8) ?_ ?_
  · simp only [buSZ]; omega
  · have h1 : α ^ 2 ≤ p := le_of_lt hαp
    have hpow : p + 1 ≤ 2 ^ p := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := p))
    have h3 : 4 * p + 98 ≤ 2 ^ (p + 8) := by
      have h4 : 2 ^ (p + 8) = 2 ^ p * 256 := by rw [pow_add]; norm_num
      rw [h4]
      nlinarith [hpow, Nat.one_le_two_pow (n := p)]
    nlinarith

theorem buDivStepD (KL : HvdH.KernelLib) (IL : HvdH.IntLib) : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) (Ad : ℤ) (hAd : HvdH.isz Ad ≤ Work.Resample.buSZ p) (V : List HvdH.Val), Work.Resample.Pipe main prog ([HvdH.Val.int (Work.Resample.buDivK p α), HvdH.Val.int Ad, HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)] ++ V) ([HvdH.Val.int (Int.tdiv Ad ((2 : ℤ) ^ (Work.Resample.auPrec p - p + (2 * α ^ 2 - 2)))), HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)] ++ V) (K * (Work.Resample.buSZ p + 8) ^ 2) := by
  obtain ⟨swapP, KSw, hswap⟩ := KL.swap
  obtain ⟨shrP, KSr, hshr⟩ := IL.shrT
  refine ⟨.seq swapP shrP, KSw + KSr + 1, ?_⟩
  intro main p α hα hαp Ad hAd V
  have hKn : (buDivK p α).toNat = auPrec p - p + (2 * α ^ 2 - 2) := buDivK_toNat (by omega)
  have hszK : isz (buDivK p α) ≤ buSZ p := isz_buDivK_le hαp
  have hKn0 : 0 ≤ buDivK p α := buDivK_nonneg p α
  -- step 1: swap the exponent `k` and the dividend `Ad`
  have H1 : Pipe main swapP [.int (buDivK p α), .int Ad, .int (p : ℤ), .int (α : ℤ)]
      [.int Ad, .int (buDivK p α), .int (p : ℤ), .int (α : ℤ)]
      (KSw * (2 * buSZ p + 1)) := by
    have h := Pipe.appendTail (T := [.int (p : ℤ), .int (α : ℤ)])
      (Pipe.swap (main := main) hswap (.int (buDivK p α)) (.int Ad))
    refine Pipe.le h ?_
    rw [Work.Fx.vsz_int, Work.Fx.vsz_int]
    exact Nat.mul_le_mul_left _ (by omega)
  -- step 2: shift the dividend right by `k` bits
  have H2 : Pipe main shrP [.int Ad, .int (buDivK p α), .int (p : ℤ), .int (α : ℤ)]
      [.int (Int.tdiv Ad (2 ^ (buDivK p α).toNat)), .int (p : ℤ), .int (α : ℤ)]
      (KSr * (2 * buSZ p)) := by
    have h := Pipe.appendTail (T := [.int (p : ℤ), .int (α : ℤ)])
      (Pipe.binOp (main := main) (hshr main) (a := Ad) (b := buDivK p α) hKn0)
    refine Pipe.le h ?_
    exact Nat.mul_le_mul_left _ (by omega)
  have H := Pipe.comp H1 H2
  refine Pipe.le (Pipe.rw (Pipe.appendTail V H) ?_) ?_
  · rw [hKn]
  · have h2 : 2 * buSZ p + 1 ≤ (buSZ p + 8) ^ 2 := by nlinarith [buSZ_ge p]
    have e1 : KSw * (2 * buSZ p + 1) ≤ KSw * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ h2
    have e2 : KSr * (2 * buSZ p) ≤ KSr * (buSZ p + 8) ^ 2 :=
      Nat.mul_le_mul_left _ (le_trans (by omega) h2)
    calc KSw * (2 * buSZ p + 1) + KSr * (2 * buSZ p)
        ≤ KSw * (buSZ p + 8) ^ 2 + KSr * (buSZ p + 8) ^ 2 := add_le_add e1 e2
      _ = (KSw + KSr) * (buSZ p + 8) ^ 2 := by ring
      _ ≤ (KSw + KSr + 1) * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_right _ (by omega)

end Work.Resample
