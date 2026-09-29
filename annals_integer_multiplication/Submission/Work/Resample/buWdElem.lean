import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buWdKit
import Submission.Work.Resample.buZbWord
import Submission.Work.Resample.buWdDiv

/-!
# `Work.Resample.buWdElem`

Assembly of the diagonal-weight element word of the one-dimensional `B̃` resampling from its three
phases:

* `Work.Resample.buZbWord` — computes `buZb p α s t ℓ` on top of `[ℓ] ++ buCB p α s t`,
* `Work.Resample.buHeadBracket` (`buWdKit`) — removes the `ℓ` entry and duplicates the `p` entry,
* the given Horner word `hornerProg` — turns `[buZb p α s t ℓ, p, p]` into `[auH p (buZb…) (auNstep p), p]`,
* `Work.Resample.buWdDiv` — divides by `2^(auPrec p - p + (2α²-2))` (only `p` and `α` are needed,
  both entries of `buCB`).

The four costs are absorbed by `Work.Resample.buCostFinal`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH
open Work.Fx

theorem buWdElem (KL : HvdH.KernelLib) (IL : HvdH.IntLib)
    (hornerProg : HvdH.Cmd) (Kh : ℕ)
    (hornerSpec : ∀ (main : HvdH.Cmd) (p : ℕ), 100 ≤ p → ∀ (Z : ℤ),
      Z.natAbs ≤ 2 ^ (11 * p + 210) →
      ∀ rest : List HvdH.Val, HvdH.WordR main hornerProg
        (fun vs => vs = [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] ++ rest)
        (fun vs out => vs = [HvdH.Val.int Z, HvdH.Val.int (p : ℤ)] ++ rest ∧
          out = [HvdH.Val.int (Work.Resample.auH p Z (Work.Resample.auNstep p))] ++ rest)
        (fun _ => Kh * (p + 1) ^ Kh)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (hs : 2 ≤ s)
      (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)),
      ∀ rest : List HvdH.Val, HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.int ℓ] ++ Work.Resample.buCB p α s t ++ rest)
        (fun vs out => vs = [HvdH.Val.int ℓ] ++ Work.Resample.buCB p α s t ++ rest ∧
          out = [HvdH.Val.int (Work.Resample.buWd p α s t ℓ)] ++ Work.Resample.buCB p α s t ++ rest)
        (fun _ => K * (p + 1) ^ K) := by
  obtain ⟨progZ, Kz, hZ⟩ := buZbWord KL IL
  obtain ⟨progB, Kb, hBracket⟩ := buHeadBracket KL
  obtain ⟨progD, Kt, hD⟩ := buWdDiv KL IL
  refine ⟨Cmd.seq progZ (Cmd.seq progB (Cmd.seq hornerProg progD)),
    2 ^ (Kz + Kh + Kt + Kb + 102), ?_⟩
  intro main p α s t hs hst hα hp htp hαp ℓ hℓ hℓs rest
  have hsp : s < 2 ^ p := by omega
  have hZabs : (buZb p α s t ℓ).natAbs ≤ 2 ^ (11 * p + 210) := by
    refine le_trans (natAbs_buZb_le p α s t ℓ (le_of_lt hαp) (by omega) hsp hp) ?_
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the four phases
  have h1 : Pipe main progZ ([.int ℓ] ++ buCB p α s t)
      ([.int (buZb p α s t ℓ), .int ℓ] ++ buCB p α s t) (Kz * (p + 1) ^ Kz) :=
    hZ main p α s t hs hst hα hp htp hαp ℓ hℓ hℓs
  have h2 : Pipe main progB ([.int (buZb p α s t ℓ), .int ℓ] ++ buCB p α s t)
      ([.int (buZb p α s t ℓ), .int (p : ℤ), .int (p : ℤ)] ++ buTail p α s t)
      (Kb * (vsz (.int (buZb p α s t ℓ)) + vsz (.int ℓ) + vsz (.int (p : ℤ)) + 1)) :=
    hBracket main (.int (buZb p α s t ℓ)) (.int ℓ) (.int (p : ℤ)) (buTail p α s t)
  have h3 : Pipe main hornerProg
      ([.int (buZb p α s t ℓ), .int (p : ℤ), .int (p : ℤ)] ++ buTail p α s t)
      ([.int (auH p (buZb p α s t ℓ) (auNstep p)), .int (p : ℤ)] ++ buTail p α s t)
      (Kh * (p + 1) ^ Kh) := by
    intro rest' vs hvs st R hR
    have hvs' : vs = [.int (buZb p α s t ℓ), .int (p : ℤ)] ++
        ([.int (p : ℤ)] ++ buTail p α s t ++ rest') := by
      rw [hvs]
      rfl
    obtain ⟨out, st', n, hpost, hev, hn, hstk, hoth⟩ :=
      hornerSpec main p hp (buZb p α s t ℓ) hZabs
        ([.int (p : ℤ)] ++ buTail p α s t ++ rest') vs hvs' st R hR
    refine ⟨out, st', n, ?_, hev, hn, hstk, hoth⟩
    rw [hpost.2]
    rfl
  have h4 : Pipe main progD ([.int (auH p (buZb p α s t ℓ) (auNstep p))] ++ buCB p α s t)
      ([.int (buWd p α s t ℓ)] ++ buCB p α s t) (Kt * (p + 1) ^ Kt) :=
    hD main p α s t hs hst hα hp htp hαp ℓ hℓ hℓs
  have hall : Pipe main (Cmd.seq progZ (Cmd.seq progB (Cmd.seq hornerProg progD)))
      ([.int ℓ] ++ buCB p α s t)
      ([.int (buWd p α s t ℓ)] ++ buCB p α s t)
      (Kz * (p + 1) ^ Kz
        + (Kb * (vsz (.int (buZb p α s t ℓ)) + vsz (.int ℓ) + vsz (.int (p : ℤ)) + 1)
          + (Kh * (p + 1) ^ Kh + Kt * (p + 1) ^ Kt))) :=
    Pipe.comp h1 (Pipe.comp h2 (Pipe.comp h3 h4))
  -- cost bookkeeping
  have hv : vsz (.int (buZb p α s t ℓ)) + vsz (.int ℓ) + vsz (.int (p : ℤ)) + 1
      ≤ 2 * buSZ p + 1 := by
    rw [vsz_int, vsz_int, vsz_int]
    have h1' : isz (buZb p α s t ℓ) ≤ buSZ p :=
      isz_buZb_le p α s t ℓ (le_of_lt hαp) (by omega) hsp hp
    have h2' : isz ℓ + isz ((p : ℤ)) ≤ 2 * p + 4 := by
      have hℓn : ℓ.natAbs < 2 ^ p := by
        have h1 : ℓ.natAbs ≤ s := natAbs_le_of ℓ (s : ℤ) (by positivity) (by omega) (by omega)
        exact lt_of_le_of_lt h1 hsp
      have hℓsz : isz ℓ ≤ p + 2 := by
        have := Nat.size_le.mpr hℓn
        simp only [isz]
        omega
      have hpsz : isz ((p : ℤ)) ≤ p + 2 := by
        have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
        simp only [isz, Int.natAbs_natCast]
        omega
      omega
    have hbu : 2 * p + 5 ≤ buSZ p := by simp only [buSZ]; omega
    omega
  have hcost := buCostFinal (Kz := Kz) (Kh := Kh) (Kt := Kt) (C := Kb) (p := p) hp
  have hb : Kb * (vsz (.int (buZb p α s t ℓ)) + vsz (.int ℓ) + vsz (.int (p : ℤ)) + 1)
      ≤ Kb * (2 * buSZ p + 1) := Nat.mul_le_mul_left _ hv
  refine pipe_to_wordR rest (Pipe.le hall ?_)
  omega

end Work.Resample
