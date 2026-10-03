/-
# `FIArea2/R6/Pack6.lean` — the compactly supported interpolant of a round-6 majorant

`IsMajorant6 Pa f` asserts the *existence* of a `C⁴` interpolant `F` with `F|_ℤ = f` and
`|F^{(j)}| ≤ cMaj j·M^{-j}`, but without compact support (which §7's Poisson expansion and the
(9.1) estimate need).  `majorant6_trunc` sharpens this: it produces such an `F` supported in
`[M/64, 64M]` with a single absolute derivative constant `Cder`.  This module names the two
objects (`Cder6`, `majF`) and their specifications, so that the §9/§10 assemblies can be stated
without re-choosing them.
-/
import Mathlib
import Submission.Work.FIArea2.R6.majorant6_trunc
import Submission.Work.FITop4.Defs6

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

/-- The absolute derivative constant of `majorant6_trunc`, enlarged to be `≥ 1` (so that it can
serve as the `Cder` of `Fint_sub_Fhat_logFac6_le` and of the (9.1) estimate). -/
def Cder6 : ℝ := max majorant6_trunc.choose 1

theorem Cder6_pos : 0 < Cder6 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)

theorem one_le_Cder6 : 1 ≤ Cder6 := le_max_right _ _

theorem Cder6_le : majorant6_trunc.choose ≤ Cder6 := le_max_left _ _

/-- The compactly supported `C⁴` interpolant of a round-6 majorant: `majF Pa f hf` agrees with
`f` at the integers, is supported in `[M/64, 64M]` and has `|F^{(j)}| ≤ Cder6·M^{-j}`. -/
def majF (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f) : ℝ → ℝ :=
  (majorant6_trunc.choose_spec.2 Pa f hf).choose

theorem majF_spec (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f) :
    ContDiff ℝ 4 (majF Pa f hf) ∧ HasCompactSupport (majF Pa f hf) ∧
      (∀ n : ℤ, majF Pa f hf (n : ℝ) = f n) ∧
      (∀ u : ℝ, majF Pa f hf u ≠ 0 → Pa.M / 64 ≤ u ∧ u ≤ 64 * Pa.M) ∧
      (∀ j : ℕ, j ≤ 4 → ∀ u : ℝ,
        |iteratedDeriv j (majF Pa f hf) u| ≤ Cder6 * Pa.M ^ (-(j : ℝ))) := by
  obtain ⟨hcd, hcs, hint, hsupp, hder⟩ := (majorant6_trunc.choose_spec.2 Pa f hf).choose_spec
  refine ⟨hcd, hcs, hint, hsupp, ?_⟩
  intro j hj u
  refine le_trans (hder j hj u) ?_
  have hM1 : (1 : ℝ) ≤ Pa.M := Pa.hM1
  have hpow : (0 : ℝ) ≤ Pa.M ^ (-(j : ℝ)) := Real.rpow_nonneg (by linarith) _
  exact mul_le_mul_of_nonneg_right Cder6_le hpow

end

end Work.FIArea2.R6
