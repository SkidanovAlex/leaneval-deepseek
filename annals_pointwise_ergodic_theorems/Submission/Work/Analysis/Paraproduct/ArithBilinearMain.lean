/-
# The arithmetic bilinear estimate of Section 10: the assembled estimates

This module assembles the two proven ingredients of the Section 10 proof of the paper's
Theorem `bile` (Krause--Mirek--Tao, Annals 195 (2022)) in the finite-cyclic model set up in
`Submission.Work.Analysis.Paraproduct.ArithBilinear`:

* `bilinearAverageLq_of_fiber` : (avg-1) of the paper — from the Appendix C concentration bound
  `‖h‖_{L^s(ℤ/Qℤ)} ≤ C` on the fibre-counting function `h(m) = #{n : P(n) = m}`, the arithmetic
  bilinear average satisfies `‖A(f,g)‖_{L^{2s}} ≤ √C ‖f‖₂ ‖g‖₂` (so for
  `s < d/(d-1)`, i.e. `2s < 2d/(d-1)`, an exponent slightly above `2`);
* `bile_of_r1` : the paper's interpolation step — (avg-1) together with the `r = 1` estimate
  (Proposition `bile-2`, whose proof uses Theorem `improv`) gives the estimate of Theorem `bile`
  at every intermediate exponent `1 ≤ r ≤ 2s`, by log-convexity of the `L^p` norms
  (`LpNormZMod_logconvex`).
-/
import Mathlib
import Submission.Work.Analysis.Paraproduct.bilinAverage_lq_fiber
import Submission.Work.Analysis.Paraproduct.LpNormZMod_logconvex
import Submission.Work.Analysis.Paraproduct.CrtFactor

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace Work.Analysis.Paraproduct

noncomputable section

open Work.Analysis.Concentration
open Polynomial

/-- **(avg-1) of Section 10.**  The concentration bound on the fibres of `P` gives the arithmetic
bilinear estimate of Theorem `bile` at the exponent `2s` (unconditionally, i.e. without any
minor-arc support hypothesis). -/
theorem bilinearAverageLq_of_fiber (P : ℤ[X]) (Q : ℕ) [NeZero Q] {s C : ℝ} (hs : 1 ≤ s)
    (hC : LpNormZMod Q s (fun m => (polyFiberCard P Q m : ℂ)) ≤ C) :
    BilinearAverageLq P Q (2 * s) (Real.sqrt C) :=
  bilinAverage_lq_fiber P Q hs hC


/-- **The Appendix C concentration input, in the form used above.**  The colleague's
`FiberLpBound P Q s C` (the bound `∑_y h(y)^s ≤ C^s Q` on the fibre-counting function
`h(y) = #{x : P(x) = y}`) implies the normalised-`L^s` bound
`‖h‖_{L^s(ℤ/Qℤ)} ≤ C` which is the hypothesis `hC` of the Section 10 estimates. -/
theorem lpNorm_fiberCard_le_of_fiberLpBound (P : ℤ[X]) (Q : ℕ) [NeZero Q] {s C : ℝ}
    (hs : 0 < s) (hC : 0 ≤ C) (h : FiberLpBound P Q s C) :
    LpNormZMod Q s (fun m => (polyFiberCard P Q m : ℂ)) ≤ C := by
  have hnorm : ∀ m : ZMod Q, ‖((polyFiberCard P Q m : ℕ) : ℂ)‖ = (polyFiberCard P Q m : ℝ) :=
    fun m => by simp
  have hQ : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast NeZero.pos Q
  have hsum : (∑ m : ZMod Q, ‖((polyFiberCard P Q m : ℕ) : ℂ)‖ ^ s)
      = ∑ m : ZMod Q, (polyFiberCard P Q m : ℝ) ^ s := by
    exact Finset.sum_congr rfl (fun m _ => by rw [hnorm m])
  rw [LpNormZMod, hsum]
  have hbound : ((Q : ℝ))⁻¹ * ∑ m : ZMod Q, (polyFiberCard P Q m : ℝ) ^ s ≤ C ^ s := by
    rw [inv_mul_le_iff₀ hQ]
    exact h.trans_eq (mul_comm _ _)
  refine le_trans (Real.rpow_le_rpow (mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun m _ => by positivity))) hbound (by positivity)) ?_
  rw [← Real.rpow_mul hC]
  rw [show s * (1 / s) = 1 from by rw [mul_one_div, div_self hs.ne'], Real.rpow_one C]

end

end Work.Analysis.Paraproduct
