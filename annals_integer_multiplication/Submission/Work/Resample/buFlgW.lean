import Mathlib
import Submission.Work.Resample.buWtKit
import Submission.Work.Resample.buBndW
import Submission.Work.Resample.buFlgSizes

set_option maxHeartbeats 2000000

namespace Work.Resample

open HvdH

/-!
# `Work.Resample.buFlgW`: the guard-flag word of the weight table

From the window `[Z, p]` this word produces `[flag, Z, p]` where
`flag = if Z < auBnd p + 1 then 1 else 0`, i.e. `flag ≠ 0` exactly when `Z ≤ auBnd p`
(`Work.Resample.auFlgV_ne_zero_iff` of `buWtKit`), the guard under which the Horner recursion of
`buWt` is the value of `buWt`.

The word is `dup` (a copy of `Z`), `pick 2` (a copy of `p`), the bound word
`Work.Resample.buBndW` (computing `auBnd p + 1`), `swap` (bringing `Z` on top of the bound), and
`IntLib.lt` (the comparison `Z < auBnd p + 1`).

## Cost

Every value occurring in the word has `isz ≤ buSZ p` (`Work.Resample.buFlgSizes` and the `p`
component of it), so each of the four library steps costs at most `buSBW p Λ` with
`Λ = kd + kp + kw + klt + 1` the sum of the four library constants; the bound word costs
`kb (p+1)^kb`.  `buSBW_le_pow` gives `buSBW p Λ ≤ Λ·10^12·(p+1)^4`, so the total is
`≤ 4 (Λ·10^12) (p+1)^4 + kb (p+1)^kb`, absorbed into `K (p+1)^K` with `K = 2^(4Λ10^12 + kb + 30)`
by `buFlg_budget`.
-/

/-- `K * (u + v + 1) ≤ buSBW p KS` for two values of size `≤ buSZ p` (the `+1` of `swap`). -/
theorem buFlg_le_buSBW_two_one {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ}
    (hu : u ≤ buSZ p) (hv : v ≤ buSZ p) : K * (u + v + 1) ≤ buSBW p KS := by
  rw [buSBW]
  calc K * (u + v + 1) ≤ KS * (2 * buSZ p + 1) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by
        have h := buSZ_ge_big p
        have hexp : (buSZ p + 8) ^ 2 = buSZ p * buSZ p + 16 * buSZ p + 64 := by ring
        rw [hexp]; nlinarith)

/-- Arithmetic absorption of a four-step `p`-polynomial budget and one `(p+1)^d` term into a single
`K (p+1)^K`, with `K = 2^(c+d+30)`. -/
theorem buFlg_budget (p c d : ℕ) (hp : 2 ≤ p + 1) (hc : 1 ≤ c) :
    c * (p + 1) ^ 4 + d * (p + 1) ^ d ≤ (2 ^ (c + d + 30)) * (p + 1) ^ (2 ^ (c + d + 30)) := by
  have hE : (2 : ℕ) ^ 30 ≤ 2 ^ (c + d + 30) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4E : 4 ≤ 2 ^ (c + d + 30) := le_trans (by norm_num) hE
  have hdE : d ≤ 2 ^ (c + d + 30) :=
    le_trans (le_of_lt (Nat.lt_two_pow_self (n := d)))
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hcdE : c + d ≤ 2 ^ (c + d + 30) :=
    le_trans (le_of_lt (Nat.lt_two_pow_self (n := c + d)))
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h1 : c * (p + 1) ^ 4 ≤ c * (p + 1) ^ (2 ^ (c + d + 30)) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h4E)
  have h2 : d * (p + 1) ^ d ≤ d * (p + 1) ^ (2 ^ (c + d + 30)) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hdE)
  calc c * (p + 1) ^ 4 + d * (p + 1) ^ d
      ≤ c * (p + 1) ^ (2 ^ (c + d + 30)) + d * (p + 1) ^ (2 ^ (c + d + 30)) :=
        add_le_add h1 h2
    _ = (c + d) * (p + 1) ^ (2 ^ (c + d + 30)) := by ring
    _ ≤ (2 ^ (c + d + 30)) * (p + 1) ^ (2 ^ (c + d + 30)) := Nat.mul_le_mul_right _ hcdE

/-- The assembly of the guard-flag word from the bound word `buBndW` and the size certificate. -/
theorem buFlgW_of (KL : HvdH.KernelLib) (IL : HvdH.IntLib)
    (hSizes : ∀ (p : ℕ), 100 ≤ p →
      HvdH.isz (p : ℤ) ≤ buSZ p ∧
      HvdH.isz ((3 : ℤ) * (p : ℤ)) ≤ buSZ p ∧
      HvdH.isz ((100 : ℤ) + (3 : ℤ) * (p : ℤ)) ≤ buSZ p ∧
      HvdH.isz ((10 : ℤ) + (p : ℤ)) ≤ buSZ p ∧
      3 * p + 100 ≤ buSZ p ∧
      HvdH.isz ((3 * p + 100 : ℕ) : ℤ) ≤ buSZ p ∧
      HvdH.isz (((10 : ℤ) + (p : ℤ)) * (2 : ℤ) ^ (3 * p + 100)) ≤ buSZ p ∧
      HvdH.isz (auBnd p + 1) ≤ buSZ p)
    (hBndW : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ), 100 ≤ p →
      Work.Resample.Pipe main prog [HvdH.Val.int (p : ℤ)] [HvdH.Val.int (auBnd p + 1)]
        (K * (p + 1) ^ K)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (Z : ℤ), 100 ≤ p →
      HvdH.isz Z ≤ Work.Resample.buSZ p →
      Work.Resample.Pipe main prog
        [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
        [HvdH.Val.int (if Z < Work.Resample.auBnd p + 1 then 1 else 0), HvdH.Val.int Z,
          HvdH.Val.int (p : ℤ)]
        (K * (p + 1) ^ K) := by
  obtain ⟨dupP, kd, hDup⟩ := KL.dup
  obtain ⟨pickP, kp, hPick⟩ := KL.pick
  obtain ⟨swapP, kw, hSwap⟩ := KL.swap
  obtain ⟨ltP, klt, hLt⟩ := IL.lt
  obtain ⟨bndP, kb, hBndP⟩ := hBndW
  refine ⟨Cmd.seq dupP (Cmd.seq (pickP 2) (Cmd.seq bndP (Cmd.seq swapP ltP))),
    2 ^ (4 * ((kd + kp + kw + klt + 1) * 1000000 ^ 2) + kb + 30), ?_⟩
  intro main p Z hp hZ
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hSizes p hp
  have hZv : vsz (Val.int Z) ≤ buSZ p := by rw [Work.Fx.vsz_int]; exact hZ
  have hpv : vsz (Val.int (p : ℤ)) ≤ buSZ p := by rw [Work.Fx.vsz_int]; exact s1
  -- step 1: duplicate `Z`
  have h1 : Pipe main dupP [Val.int Z, Val.int (p : ℤ)] [Val.int Z, Val.int Z, Val.int (p : ℤ)]
      (buSBW p (kd + kp + kw + klt + 1)) :=
    Pipe.appendTail [Val.int (p : ℤ)]
      (Pipe.le (Pipe.dup main hDup (Val.int Z))
        (by rw [Work.Fx.vsz_int]; exact le_buSBW_one (by omega) hZ))
  -- step 2: `pick 2`, a copy of `p`
  have h2 : Pipe main (pickP 2) [Val.int Z, Val.int Z, Val.int (p : ℤ)]
      [Val.int (p : ℤ), Val.int Z, Val.int Z, Val.int (p : ℤ)]
      (buSBW p (kd + kp + kw + klt + 1)) := by
    have h0 := Pipe.pickAt (prog := pickP) (K := kp) main hPick
      (A := [Val.int Z, Val.int Z, Val.int (p : ℤ)]) (k := 2) (v := Val.int (p : ℤ))
      (by simp) (by simp)
    refine Pipe.le h0 ?_
    refine le_buSBW_roll (K := kp) (by omega) (A := [Val.int Z, Val.int Z, Val.int (p : ℤ)])
      (k := 2) (by norm_num) (by simp) ?_
    intro v hv
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hZv
    · exact hZv
    · exact hpv
  -- step 3: the bound word `auBnd p + 1`
  have h3 : Pipe main bndP [Val.int (p : ℤ), Val.int Z, Val.int Z, Val.int (p : ℤ)]
      [Val.int (auBnd p + 1), Val.int Z, Val.int Z, Val.int (p : ℤ)] (kb * (p + 1) ^ kb) :=
    Pipe.appendTail [Val.int Z, Val.int Z, Val.int (p : ℤ)] (hBndP main p hp)
  -- step 4: `swap`, bringing `Z` on top of the bound
  have h4 : Pipe main swapP [Val.int (auBnd p + 1), Val.int Z, Val.int Z, Val.int (p : ℤ)]
      [Val.int Z, Val.int (auBnd p + 1), Val.int Z, Val.int (p : ℤ)]
      (buSBW p (kd + kp + kw + klt + 1)) := by
    have h0 := Pipe.swap (prog := swapP) (K := kw) main hSwap
      (Val.int (auBnd p + 1)) (Val.int Z)
    have h0' := Pipe.appendTail [Val.int Z, Val.int (p : ℤ)] h0
    refine Pipe.le h0' ?_
    rw [Work.Fx.vsz_int, Work.Fx.vsz_int]
    exact buFlg_le_buSBW_two_one (by omega) s8 hZ
  -- step 5: `lt`, the comparison `Z < auBnd p + 1`
  have h5 : Pipe main ltP [Val.int Z, Val.int (auBnd p + 1), Val.int Z, Val.int (p : ℤ)]
      [Val.int (if Z < auBnd p + 1 then 1 else 0), Val.int Z, Val.int (p : ℤ)]
      (buSBW p (kd + kp + kw + klt + 1)) := by
    have h0 := Pipe.binOp (hLt main) (a := Z) (b := auBnd p + 1) trivial
    have h0' := Pipe.appendTail [Val.int Z, Val.int (p : ℤ)] h0
    refine Pipe.le h0' ?_
    exact le_buSBW_two (by omega) hZ s8
  -- the composition
  have hcomp : Pipe main (Cmd.seq dupP (Cmd.seq (pickP 2) (Cmd.seq bndP (Cmd.seq swapP ltP))))
      [Val.int Z, Val.int (p : ℤ)]
      [Val.int (if Z < auBnd p + 1 then 1 else 0), Val.int Z, Val.int (p : ℤ)]
      (buSBW p (kd + kp + kw + klt + 1) +
        (buSBW p (kd + kp + kw + klt + 1) +
          (kb * (p + 1) ^ kb + (buSBW p (kd + kp + kw + klt + 1) +
            buSBW p (kd + kp + kw + klt + 1))))) :=
    Pipe.comp h1 (Pipe.comp h2 (Pipe.comp h3 (Pipe.comp h4 h5)))
  refine Pipe.le hcomp ?_
  have hcb : buSBW p (kd + kp + kw + klt + 1) ≤
      (kd + kp + kw + klt + 1) * 1000000 ^ 2 * (p + 1) ^ 4 :=
    buSBW_le_pow p (kd + kp + kw + klt + 1)
  calc buSBW p (kd + kp + kw + klt + 1) +
        (buSBW p (kd + kp + kw + klt + 1) +
          (kb * (p + 1) ^ kb + (buSBW p (kd + kp + kw + klt + 1) +
            buSBW p (kd + kp + kw + klt + 1))))
      = 4 * buSBW p (kd + kp + kw + klt + 1) + kb * (p + 1) ^ kb := by ring
    _ ≤ 4 * ((kd + kp + kw + klt + 1) * 1000000 ^ 2 * (p + 1) ^ 4) + kb * (p + 1) ^ kb :=
        add_le_add (Nat.mul_le_mul_left 4 hcb) le_rfl
    _ = (4 * ((kd + kp + kw + klt + 1) * 1000000 ^ 2)) * (p + 1) ^ 4 +
          kb * (p + 1) ^ kb := by ring
    _ ≤ (2 ^ (4 * ((kd + kp + kw + klt + 1) * 1000000 ^ 2) + kb + 30)) *
          (p + 1) ^ (2 ^ (4 * ((kd + kp + kw + klt + 1) * 1000000 ^ 2) + kb + 30)) :=
        buFlg_budget p (4 * ((kd + kp + kw + klt + 1) * 1000000 ^ 2)) kb (by omega) (by omega)

/-- The word computing the guard flag `if Z < auBnd p + 1 then 1 else 0` (which is `1` exactly when
`Z ≤ auBnd p`, the guard under which `buWt p α s t ℓ h` is the value of the Horner recursion and not `0`).
It maps `[Z, p]` to `[flag, Z, p]`, i.e. it duplicates `Z`.

Intended implementation: duplicate `Z`, compute `auBnd p + 1 = (p+10)·2^(3p+100) + 1` from the copy of
`p` (`IntLib.add/mulS/pow2`), then `IntLib.lt` on `[Z, auBnd p + 1]`. -/
theorem buFlgW (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (Z : ℤ), 100 ≤ p →
      HvdH.isz Z ≤ Work.Resample.buSZ p →
      Work.Resample.Pipe main prog
        [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)]
        [HvdH.Val.int (if Z < Work.Resample.auBnd p + 1 then 1 else 0), HvdH.Val.int Z,
          HvdH.Val.int (p : ℤ)]
        (K * (p + 1) ^ K) :=
  buFlgW_of KL IL buFlgSizes (buBndW KL IL)

end Work.Resample
