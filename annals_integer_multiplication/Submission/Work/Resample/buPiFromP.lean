import Mathlib
import Submission.Work.Resample.buKit
import Submission.Work.Resample.auPreKit

/-!
# `Work.Resample.buPiFromP`: the fixed-point π word read off the small parameter `p`

The one-dimensional `B̃` resampling word (`Work.Resample.buPrep`) is parameterised by the *precision
parameter* `p` (paper §4–§5: the working precision is `auPrec p = 3p + 100`), and every sub-word of
it reads `p` off the value stack.  The `π` sub-word must therefore turn the *small* integer `p` into
the *large* fixed-point value

`auPi p = uval (auPrec p) = ⌊2^{3p+100}·π⌋`   (`Work.Resample.auDefs`).

This module proves that this is possible with a cost polynomial in `p`:

`∃ prog K, ∀ main p, 100 ≤ p → Pipe main prog [int p] [int (auPi p)] (K·(p+1)^K)`.

The program is the straight-line chain

`pushVal 3 ; mulS ; pushVal 100 ; add ; piProg`

where `piProg` is the π word of `Work.Resample.auPiWord`, which computes `int P ↦ int (uval P)` for
every precision `P ≥ 100`.  Since `auPrec p = 3p+100 ≥ 100` and `auPrec p + 1 = 3p + 101`, the cost
is `O(p)` for the four arithmetic steps plus `Kpi·(3p+101)^Kpi` for the π word; both are bounded by
`K·(p+1)^K` for a suitable constant `K` (see `buPi_cost_bound`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## Size bounds for the small integer values occurring in the program -/

/-- `vsz` of an integer value is `isz` (`Work.IntLib.vsz_int`). -/
theorem buPi_vsz_int_eq (z : ℤ) : vsz (Val.int z) = isz z := Work.IntLib.vsz_int z

theorem buPi_isz_three_le : isz (3 : ℤ) ≤ 4 := by
  have h : (3 : ℤ).natAbs = 3 := by norm_num
  simp only [isz, h]
  have h2 : Nat.size 3 ≤ 2 := Nat.size_le.mpr (by norm_num)
  omega

theorem buPi_isz_hundred_le : isz (100 : ℤ) ≤ 9 := by
  have h : (100 : ℤ).natAbs = 100 := by norm_num
  simp only [isz, h]
  have h2 : Nat.size 100 ≤ 7 := Nat.size_le.mpr (by norm_num)
  omega

theorem buPi_isz_natCast_le (p : ℕ) : isz (p : ℤ) ≤ p + 2 := by
  simp only [isz, Int.natAbs_natCast]
  have h2 : Nat.size p ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self)
  omega

theorem buPi_isz_three_mul_le (p : ℕ) : isz ((3 : ℤ) * (p : ℤ)) ≤ p + 4 := by
  have h1 : ((3 : ℤ) * (p : ℤ)) = ((3 * p : ℕ) : ℤ) := by push_cast; ring
  rw [h1, isz, Int.natAbs_natCast]
  have hb : 3 * p < 2 ^ (p + 2) := by
    calc 3 * p < 3 * 2 ^ p :=
          Nat.mul_lt_mul_of_pos_left Nat.lt_two_pow_self (by norm_num)
      _ ≤ 4 * 2 ^ p := by omega
      _ = 2 ^ (p + 2) := by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.add_comm]
  have h2 : Nat.size (3 * p) ≤ p + 2 := Nat.size_le.mpr hb
  omega

/-! ## The cost bound -/

/-- The four arithmetic steps of the program cost at most `(Kpush+Kadd+Kmul+1)·35·(p+1)`. -/
theorem buPi_small_cost (Kpush Kadd Kmul p : ℕ) :
    (((Kpush * (vsz (Val.int (3 : ℤ)) + 1) + Kmul * isz (3 : ℤ) * isz (p : ℤ)) +
        Kpush * (vsz (Val.int (100 : ℤ)) + 1)) +
        Kadd * (isz (100 : ℤ) + isz ((3 : ℤ) * (p : ℤ))))
      ≤ (Kpush + Kadd + Kmul + 1) * 35 * (p + 1) := by
  have h1 : Kpush * (vsz (Val.int (3 : ℤ)) + 1) ≤ Kpush * 5 :=
    Nat.mul_le_mul_left _ (by rw [buPi_vsz_int_eq]; have := buPi_isz_three_le; omega)
  have h2 : Kmul * isz (3 : ℤ) * isz (p : ℤ) ≤ Kmul * (4 * p + 8) := by
    calc Kmul * isz (3 : ℤ) * isz (p : ℤ) ≤ Kmul * 4 * (p + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ buPi_isz_three_le) (buPi_isz_natCast_le p)
      _ = Kmul * (4 * p + 8) := by ring
  have h3 : Kpush * (vsz (Val.int (100 : ℤ)) + 1) ≤ Kpush * 10 :=
    Nat.mul_le_mul_left _ (by rw [buPi_vsz_int_eq]; have := buPi_isz_hundred_le; omega)
  have h4 : Kadd * (isz (100 : ℤ) + isz ((3 : ℤ) * (p : ℤ))) ≤ Kadd * (p + 13) :=
    Nat.mul_le_mul_left _
      (by have := buPi_isz_hundred_le; have := buPi_isz_three_mul_le p; omega)
  nlinarith [h1, h2, h3, h4, Nat.zero_le Kpush, Nat.zero_le Kadd, Nat.zero_le Kmul,
    Nat.zero_le p]

/-- The total cost `(Kpush+Kadd+Kmul+1)·35·(p+1) + Kpi·(3p+101)^Kpi` of the five-step program is
`≤ K·(p+1)^K` with `K = 2·(35·(Kpush+Kadd+Kmul+1) + 2·Kpi + 2)`. -/
theorem buPi_cost_bound (Kpi KP p : ℕ) (hp : 100 ≤ p) :
    KP * 35 * (p + 1) + Kpi * (3 * p + 101) ^ Kpi
      ≤ 2 * (35 * KP + 2 * Kpi + 2) * (p + 1) ^ (2 * (35 * KP + 2 * Kpi + 2)) := by
  set K0 : ℕ := 35 * KP + 2 * Kpi + 2 with hK0def
  have hK0 : KP * 35 ≤ K0 := by rw [hK0def]; omega
  have hKpi0 : Kpi ≤ K0 := by rw [hK0def]; omega
  have hK0le : K0 ≤ 2 * K0 := by omega
  have hp0 : 0 < p + 1 := by omega
  have hA : KP * 35 * (p + 1) ≤ K0 * (p + 1) ^ K0 := by
    calc KP * 35 * (p + 1) ≤ K0 * (p + 1) := Nat.mul_le_mul hK0 le_rfl
      _ ≤ K0 * (p + 1) ^ K0 := by
          refine Nat.mul_le_mul_left _ ?_
          simpa using Nat.pow_le_pow_right hp0 (show 1 ≤ K0 by omega)
  have hB : Kpi * (3 * p + 101) ^ Kpi ≤ K0 * (p + 1) ^ K0 := by
    have h4 : 3 * p + 101 ≤ 4 * (p + 1) := by omega
    have hpow : (3 * p + 101) ^ Kpi ≤ (4 * (p + 1)) ^ Kpi := Nat.pow_le_pow_left h4 Kpi
    have hmul : (4 * (p + 1)) ^ Kpi = 4 ^ Kpi * (p + 1) ^ Kpi := Nat.mul_pow 4 (p + 1) Kpi
    have h4K : 4 ^ Kpi ≤ (p + 1) ^ (K0 - Kpi) := by
      have h1 : 4 ^ Kpi ≤ 101 ^ Kpi := Nat.pow_le_pow_left (by norm_num) Kpi
      have h2 : 101 ^ Kpi ≤ (p + 1) ^ Kpi := Nat.pow_le_pow_left (by omega) Kpi
      have h3 : (p + 1) ^ Kpi ≤ (p + 1) ^ (K0 - Kpi) :=
        Nat.pow_le_pow_right hp0 (by omega)
      exact le_trans h1 (le_trans h2 h3)
    have hsplit : (p + 1) ^ (K0 - Kpi) * (p + 1) ^ Kpi = (p + 1) ^ K0 := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hKpi0]
    calc Kpi * (3 * p + 101) ^ Kpi
        ≤ Kpi * (4 ^ Kpi * (p + 1) ^ Kpi) :=
          Nat.mul_le_mul_left _ (le_trans hpow (le_of_eq hmul))
      _ ≤ Kpi * ((p + 1) ^ (K0 - Kpi) * (p + 1) ^ Kpi) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4K)
      _ = Kpi * (p + 1) ^ K0 := by rw [hsplit]
      _ ≤ K0 * (p + 1) ^ K0 := Nat.mul_le_mul_right _ hKpi0
  have hsum : KP * 35 * (p + 1) + Kpi * (3 * p + 101) ^ Kpi ≤ 2 * K0 * (p + 1) ^ K0 := by
    calc KP * 35 * (p + 1) + Kpi * (3 * p + 101) ^ Kpi
        ≤ K0 * (p + 1) ^ K0 + K0 * (p + 1) ^ K0 := Nat.add_le_add hA hB
      _ = 2 * K0 * (p + 1) ^ K0 := by ring
  have hfin : 2 * K0 * (p + 1) ^ K0 ≤ 2 * K0 * (p + 1) ^ (2 * K0) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp0 hK0le)
  exact le_trans hsum hfin

/-! ## The program -/

theorem buPiFromP (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p : ℕ) (hp : 100 ≤ p),
      Work.Resample.Pipe main prog [HvdH.Val.int (p : ℤ)] [HvdH.Val.int (Work.Resample.auPi p)]
        (K * (p + 1) ^ K) := by
  obtain ⟨pushProg, Kpush, hPush⟩ := KL.pushVal
  obtain ⟨addProg, Kadd, hAdd⟩ := IL.add
  obtain ⟨mulProg, Kmul, hMul⟩ := IL.mulS
  obtain ⟨piProg, Kpi, hPi⟩ := auPiWord KL IL
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (pushProg (Val.int 3)) mulProg)
      (pushProg (Val.int 100))) addProg) piProg,
    2 * (35 * (Kpush + Kadd + Kmul + 1) + 2 * Kpi + 2), ?_⟩
  intro main p hp
  have hprec : auPrec p = 3 * p + 100 := rfl
  have h100 : 100 ≤ auPrec p := by omega
  have hpre : auPrec p + 1 = 3 * p + 101 := by omega
  have hpre' : (100 : ℤ) + (3 : ℤ) * (p : ℤ) = ((auPrec p : ℕ) : ℤ) := by
    rw [auPrec]; push_cast; ring
  have h1 : Pipe main (pushProg (Val.int 3)) [Val.int (p : ℤ)] [Val.int (3 : ℤ), Val.int (p : ℤ)]
      (Kpush * (vsz (Val.int (3 : ℤ)) + 1)) :=
    Pipe.pushOnAny (T := [Val.int (p : ℤ)]) (hPush main (Val.int 3))
  have h2 : Pipe main mulProg [Val.int (3 : ℤ), Val.int (p : ℤ)] [Val.int ((3 : ℤ) * (p : ℤ))]
      (Kmul * isz (3 : ℤ) * isz (p : ℤ)) :=
    Pipe.binOp (hMul main) (a := (3 : ℤ)) (b := (p : ℤ)) trivial
  have h3 : Pipe main (pushProg (Val.int 100)) [Val.int ((3 : ℤ) * (p : ℤ))]
      [Val.int (100 : ℤ), Val.int ((3 : ℤ) * (p : ℤ))]
      (Kpush * (vsz (Val.int (100 : ℤ)) + 1)) :=
    Pipe.pushOnAny (T := [Val.int ((3 : ℤ) * (p : ℤ))]) (hPush main (Val.int 100))
  have h4 : Pipe main addProg [Val.int (100 : ℤ), Val.int ((3 : ℤ) * (p : ℤ))]
      [Val.int ((100 : ℤ) + (3 : ℤ) * (p : ℤ))]
      (Kadd * (isz (100 : ℤ) + isz ((3 : ℤ) * (p : ℤ)))) :=
    Pipe.binOp (hAdd main) (a := (100 : ℤ)) (b := (3 : ℤ) * (p : ℤ)) trivial
  have h4' : Pipe main addProg [Val.int (100 : ℤ), Val.int ((3 : ℤ) * (p : ℤ))]
      [Val.int ((auPrec p : ℕ) : ℤ)]
      (Kadd * (isz (100 : ℤ) + isz ((3 : ℤ) * (p : ℤ)))) :=
    Pipe.rw h4 (by rw [hpre'])
  have h5 : Pipe main piProg [Val.int ((auPrec p : ℕ) : ℤ)] [Val.int (auPi p)]
      (Kpi * (auPrec p + 1) ^ Kpi) :=
    Pipe.ofWordR (hPi main (auPrec p) h100)
  refine Pipe.le (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp h1 h2) h3) h4') h5) ?_
  have h5c : Kpi * (auPrec p + 1) ^ Kpi = Kpi * (3 * p + 101) ^ Kpi := by rw [hpre]
  have hsmall := buPi_small_cost Kpush Kadd Kmul p
  have hbig := buPi_cost_bound Kpi (Kpush + Kadd + Kmul + 1) p hp
  calc (((Kpush * (vsz (Val.int (3 : ℤ)) + 1) + Kmul * isz (3 : ℤ) * isz (p : ℤ)) +
        Kpush * (vsz (Val.int (100 : ℤ)) + 1)) +
        Kadd * (isz (100 : ℤ) + isz ((3 : ℤ) * (p : ℤ)))) + Kpi * (auPrec p + 1) ^ Kpi
      ≤ (Kpush + Kadd + Kmul + 1) * 35 * (p + 1) + Kpi * (3 * p + 101) ^ Kpi := by
        rw [h5c]; exact add_le_add hsmall le_rfl
    _ ≤ 2 * (35 * (Kpush + Kadd + Kmul + 1) + 2 * Kpi + 2) *
          (p + 1) ^ (2 * (35 * (Kpush + Kadd + Kmul + 1) + 2 * Kpi + 2)) := hbig

end Work.Resample
