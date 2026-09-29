import Mathlib
import Submission.Work.CNum.SerDnDefs

/-!
# `Work.CNum.SerDnInit` — the base case of the `serDn` invariant

`SDInv x y e σ k s` is the invariant maintained by the `serDn` recursion (see
`Work.CNum.SerDnDefs`).  This file proves it at `k = 0` for the initial state
`sd0 x y = (x, y, 0, SC)`.

The only non-trivial component of the invariant at `k = 0` is the mantissa bound
`|SC + x| ≤ 2^34`: it is *not* implied by `|x| ≤ 2^34` alone, but the hypotheses
`he : 0 ≤ e`, `hσ1 : m2r σ ≤ 79/100` and `hRσ : srad x y e ≤ m2r σ` together give
`‖spt x y‖ ≤ 79/100 < 1`, hence `|x| < SC = 2^30` and therefore
`|SC + x| ≤ 2·SC < 2^34` (and likewise `|y| < 2^30`, which is weaker than the
given `|y| ≤ 2^34`).
-/

namespace Work.CNum

open Work.ANum

/-- If the mantissa point `spt x y = (x + i y)/SC` has norm `< 1`, then both mantissas
satisfy `|x|, |y| < 2^30` (i.e. `|x|, |y| < SC`). -/
lemma natAbs_lt_of_spt_norm_lt {x y : ℤ} (h : ‖spt x y‖ < 1) :
    Int.natAbs x < 2 ^ 30 ∧ Int.natAbs y < 2 ^ 30 := by
  have h1 : Real.sqrt ((x * x + y * y).toNat : ℝ) / (SC : ℝ) < 1 := by
    rwa [spt, norm_pt] at h
  rw [div_lt_one SC_posR] at h1
  have h3 : ((x * x + y * y).toNat : ℝ) < (SC : ℝ) ^ 2 := by
    calc ((x * x + y * y).toNat : ℝ)
        = (Real.sqrt ((x * x + y * y).toNat : ℝ)) ^ 2 := by rw [Real.sq_sqrt (by positivity)]
      _ < (SC : ℝ) ^ 2 := pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) (by norm_num)
  have h4 : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 < (SC : ℝ) ^ 2 := by
    rw [← cast_sq_add]; exact h3
  have hx2 : (x : ℝ) ^ 2 < (SC : ℝ) ^ 2 :=
    lt_of_le_of_lt (le_add_of_nonneg_right (sq_nonneg _)) h4
  have hy2 : (y : ℝ) ^ 2 < (SC : ℝ) ^ 2 :=
    lt_of_le_of_lt (le_add_of_nonneg_left (sq_nonneg _)) h4
  have hxa : |(x : ℝ)| < (SC : ℝ) := by
    rw [sq_lt_sq] at hx2
    rwa [abs_of_pos SC_posR] at hx2
  have hya : |(y : ℝ)| < (SC : ℝ) := by
    rw [sq_lt_sq] at hy2
    rwa [abs_of_pos SC_posR] at hy2
  have hSC30 : SC = (2 : ℤ) ^ 30 := by norm_num [Work.ANum.SC]
  have hxl : -(SC : ℤ) < x := by
    have := (abs_lt.mp hxa).1
    exact_mod_cast this
  have hxu : x < SC := by
    have := (abs_lt.mp hxa).2
    exact_mod_cast this
  have hyl : -(SC : ℤ) < y := by
    have := (abs_lt.mp hya).1
    exact_mod_cast this
  have hyu : y < SC := by
    have := (abs_lt.mp hya).2
    exact_mod_cast this
  rw [hSC30] at hxl hxu hyl hyu
  constructor <;> omega

theorem SerDnInit {x y e σ : ℤ} (he : 0 ≤ e) (hσ1 : Work.ANum.m2r σ ≤ 79 / 100) (hx : Int.natAbs x ≤ 2 ^ 34) (hy : Int.natAbs y ≤ 2 ^ 34) (hRσ : Work.CNum.srad x y e ≤ Work.ANum.m2r σ) : Work.CNum.SDInv x y e σ 0 (Work.CNum.sd0 x y) := by
  have heR : (0 : ℝ) ≤ m2r e := div_nonneg (by exact_mod_cast he) SC_posR.le
  have hnorm : ‖spt x y‖ ≤ 79 / 100 := by
    have h := hRσ
    rw [srad] at h
    linarith
  have hlt : ‖spt x y‖ < 1 := by linarith
  have hxa : Int.natAbs x < 2 ^ 30 := (natAbs_lt_of_spt_norm_lt hlt).1
  have hSC30 : Int.natAbs SC = 2 ^ 30 := by
    rw [show SC = (2 : ℤ) ^ 30 by norm_num [Work.ANum.SC]]
    exact Int.natAbs_natCast _
  refine ⟨le_refl 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show m2r (0 : ℤ) ≤ 1 / 100
    rw [m2r_zero]; norm_num
  · show srad x y e ^ 0 ≤ m2r SC
    rw [pow_zero, m2r_SC]
  · show m2r SC ≤ 2
    rw [m2r_SC]; norm_num
  · show ‖spt x y ^ (0 + 1) - spt x y‖ ≤ m2r (0 : ℤ)
    simp [m2r_zero]
  · show Int.natAbs (SC + x) ≤ 2 ^ 34
    have h1 := Int.natAbs_add_le SC x
    omega
  · show Int.natAbs y ≤ 2 ^ 34
    exact hy

end Work.CNum
