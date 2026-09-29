import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.SerUpDefs

/-!
# `Work.CNum.SerDnDefs` — the state of the `serDn` certificate

`Work.CNum.serDnAux` (in `Work.CNum.Fx`) evaluates the *lower* bound of `log ‖h w‖` from a ball
of centre `c = (x + iy)/SC` and radius `ρ = e/SC` by the recursion

  `acc ↦ acc + 24 · logDnM (nrmDn (SC+px) py - pe - m · mulU e sg - 4)`

where at the `j`-th step `(px, py)` approximates `SC · c^(j+1)`, `pe` bounds the accumulated
error and `sg` bounds `σ^j` (`σ = nrmUp x y + e`); the multiplier of the error term is the
*decreasing* counter `m` of the recursion.

This file only *defines* the objects so that the lemmas about them can be stated and proved in
parallel.  The state is `SD` with fields `(px, py, pe, sg)`, its step is `sdNext`, and `SDInv`
is the invariant maintained along the recursion:

* `0 ≤ pe` and `m2r pe ≤ 1/100`;
* `R^k ≤ m2r sg ≤ 2`, `R = srad x y e = ‖c‖ + ρ`;
* `‖c^(k+1) - (px + i py)/SC‖ ≤ m2r pe`;
* `|SC + px| ≤ 2^34`, `|py| ≤ 2^34` (so that `NrmUpSpec`/`NrmDnSpec` apply).
-/

namespace Work.CNum

open Work.ANum

/-- Mantissa (floor-rounded) real part of `SC · (p · c)`. -/
def sdx (x y px py : ℤ) : ℤ := Int.ediv (px * x - py * y) SC

/-- Mantissa (floor-rounded) imaginary part of `SC · (p · c)`. -/
def sdy (x y px py : ℤ) : ℤ := Int.ediv (px * y + py * x) SC

/-- The state of the `serDn` recursion. -/
structure SD where
  px : ℤ
  py : ℤ
  pe : ℤ
  sg : ℤ
  deriving DecidableEq

/-- Initial state: `px = x`, `py = y`, `pe = 0`, `sg = SC` (i.e. `m2r sg = 1`). -/
def sd0 (x y : ℤ) : SD := ⟨x, y, 0, SC⟩

/-- One step of the `serDn` state recursion. -/
def sdNext (x y σ : ℤ) (s : SD) : SD :=
  ⟨Int.ediv (s.px * x - s.py * y) SC, Int.ediv (s.px * y + s.py * x) SC,
   mulU σ s.pe + 2, mulU s.sg σ⟩

/-- `k` steps of `sdNext` starting from an arbitrary state. -/
def sdIterFrom (x y σ : ℤ) (s : SD) : ℕ → SD
  | 0 => s
  | (k + 1) => sdNext x y σ (sdIterFrom x y σ s k)

/-- `k` steps of `sdNext` starting from the initial state. -/
def sdIter (x y σ : ℤ) (k : ℕ) : SD := sdIterFrom x y σ (sd0 x y) k

/-- The mantissa subtracted in the `j`-th series term, with counter `m`. -/
def sdLo (σ e : ℤ) (m : ℤ) (s : SD) : ℤ :=
  nrmDn (SC + s.px) s.py - s.pe - m * mulU e s.sg - 4

/-- The invariant maintained along the `serDn` recursion. -/
def SDInv (x y e σ : ℤ) (k : ℕ) (s : SD) : Prop :=
  0 ≤ s.pe ∧ m2r s.pe ≤ 1 / 100 ∧ srad x y e ^ k ≤ m2r s.sg ∧ m2r s.sg ≤ 2 ∧
  ‖spt x y ^ (k + 1) - spt s.px s.py‖ ≤ m2r s.pe ∧
  Int.natAbs (SC + s.px) ≤ 2 ^ 34 ∧ Int.natAbs s.py ≤ 2 ^ 34

lemma sdIterFrom_succ (x y σ : ℤ) (s : SD) (k : ℕ) :
    sdIterFrom x y σ s (k + 1) = sdNext x y σ (sdIterFrom x y σ s k) := rfl

lemma sdIter_succ (x y σ : ℤ) (k : ℕ) :
    sdIter x y σ (k + 1) = sdNext x y σ (sdIter x y σ k) := rfl

lemma sdIter_zero (x y σ : ℤ) : sdIter x y σ 0 = sd0 x y := rfl


/-! ## The floor-rounding step -/

/-- The norm of a real number cast to `ℂ`. -/
lemma sdNormC (r : ℝ) : ‖((r:ℝ):ℂ)‖ = |r| := by
  have h : ‖((r:ℝ):ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
    ring
  calc ‖((r:ℝ):ℂ)‖ = Real.sqrt (‖((r:ℝ):ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h]
    _ = |r| := Real.sqrt_sq_eq_abs r

/-- Floor-rounding the product of the mantissa points `(px,py)` and `(x,y)` is correct to within
`2/SC = m2r 2`. -/
lemma sdRound (x y px py : ℤ) :
    ‖spt px py * spt x y - spt (sdx x y px py) (sdy x y px py)‖ ≤ m2r 2 := by
  set A : ℤ := px * x - py * y with hA
  set B : ℤ := px * y + py * x with hB
  set U : ℤ := A - sdx x y px py * SC with hU
  set V : ℤ := B - sdy x y px py * SC with hV
  have hnA : sdx x y px py = A / SC := by
    show (px * x - py * y) / SC = A / SC
    rw [hA]
  have hnB : sdy x y px py = B / SC := by
    show (px * y + py * x) / SC = B / SC
    rw [hB]
  have hUA : U = A % SC := by
    rw [hU, hnA]
    have h := Int.ediv_mul_add_emod A SC
    omega
  have hVB : V = B % SC := by
    rw [hV, hnB]
    have h := Int.ediv_mul_add_emod B SC
    omega
  have hU0 : (0:ℝ) ≤ (U:ℝ) := by
    rw [hUA]; exact_mod_cast Int.emod_nonneg A SC_ne_zero
  have hU1 : (U:ℝ) < (SC:ℝ) := by
    rw [hUA]; exact_mod_cast Int.emod_lt_of_pos A SC_pos
  have hV0 : (0:ℝ) ≤ (V:ℝ) := by
    rw [hVB]; exact_mod_cast Int.emod_nonneg B SC_ne_zero
  have hV1 : (V:ℝ) < (SC:ℝ) := by
    rw [hVB]; exact_mod_cast Int.emod_lt_of_pos B SC_pos
  have hUle : |(U : ℝ)| ≤ (SC : ℝ) := by
    rw [abs_of_nonneg hU0]; exact hU1.le
  have hVle : |(V : ℝ)| ≤ (SC : ℝ) := by
    rw [abs_of_nonneg hV0]; exact hV1.le
  have heq : spt px py * spt x y - spt (sdx x y px py) (sdy x y px py)
      = ((U : ℂ) + (V : ℂ) * Complex.I) / ((((SC:ℝ) * (SC:ℝ) : ℝ)) : ℂ) := by
    simp only [spt, sdx, sdy, hU, hV, hA, hB]
    field_simp
    push_cast
    ring_nf
    rw [show (Complex.I:ℂ)^2 = -1 by rw [pow_two, Complex.I_mul_I]]
    ring
  rw [heq, norm_div]
  have hw : ‖(((((SC:ℝ) * (SC:ℝ) : ℝ)) : ℂ))‖ = (SC:ℝ) * SC := by
    rw [sdNormC, abs_of_nonneg (le_of_lt (mul_pos SC_posR SC_posR))]
  rw [hw]
  have hz : ‖((U : ℂ) + (V : ℂ) * Complex.I)‖ ≤ |(U:ℝ)| + |(V:ℝ)| := by
    have := Complex.norm_le_abs_re_add_abs_im ((U : ℂ) + (V : ℂ) * Complex.I)
    simpa using this
  have hz2 : ‖((U : ℂ) + (V : ℂ) * Complex.I)‖ ≤ (SC:ℝ) + SC :=
    le_trans hz (by linarith [hUle, hVle])
  have hden : (0:ℝ) < (SC:ℝ) * SC := mul_pos SC_posR SC_posR
  refine le_trans (div_le_div_of_nonneg_right hz2 hden.le) ?_
  rw [show (SC:ℝ) + SC = 2 * (SC:ℝ) by ring]
  have hgoal : (2 * (SC:ℝ)) / ((SC:ℝ) * SC) = m2r 2 := by
    rw [m2r,
      div_eq_div_iff (mul_ne_zero (ne_of_gt SC_posR) (ne_of_gt SC_posR)) (ne_of_gt SC_posR)]
    ring
  rw [hgoal]

end Work.CNum
