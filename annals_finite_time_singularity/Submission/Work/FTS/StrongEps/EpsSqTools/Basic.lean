/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/Basic.lean`

The two spellings of the weight of the `ε`-scheme (`epsW α z θ = w z / sin(2θ)^{γ/2}` of
`EpsSpace.lean` and `Wt α z θ = w z · sin(2θ)^{-γ/2}` of `Spaces.Defs`), their vanishing on the
boundary of the quadrant, and the two shifts in the log coordinates.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.HkSqAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The two spellings of the weight

`epsW α z θ = w z / sin(2θ)^{γ/2}` (`EpsSpace.lean`) and `Wt α z θ = w z · sin(2θ)^{-γ/2}`
(`Spaces.Defs`, `Weights.lean`) are the same function on the angular interval `[0,π/2]`, where
`sin(2θ) ≥ 0`. -/

theorem epsW_eq_Wt_of_mem_Iθ {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    epsW α z θ = Work.Spaces.Wt α z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [epsW, Work.Spaces.Wt, Work.Spaces.wTheta, div_eq_mul_inv,
    Real.rpow_neg hs (Work.Spaces.gam α / 2)]

/-- The integrand of `EpsSq` vanishes when the angular weight vanishes: `z = 0` or `θ = 0` or
`θ = π/2`. -/
theorem epsW_eq_zero_of_not_mem_quad {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) (h : ¬(0 < z ∧ θ ∈ Set.Ioo 0 (π / 2))) :
    epsW α z θ = 0 := by
  rw [Work.Spaces.Iz] at hz
  rw [Work.Spaces.Iθ] at hθ
  have hgam : (Work.Spaces.gam α / 2 : ℝ) ≠ 0 := by
    have : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    linarith
  rcases not_and_or.mp h with hz0 | hθbad
  · have hz' : z = 0 := le_antisymm (not_lt.mp hz0) hz
    subst hz'
    simp [epsW, Work.Spaces.w]
  · have hθbad' : θ ≤ 0 ∨ π / 2 ≤ θ := by
      rcases not_and_or.mp hθbad with hh | hh
      · exact Or.inl (not_lt.mp hh)
      · exact Or.inr (not_lt.mp hh)
    have hsin : Real.sin (2 * θ) = 0 := by
      rcases hθbad' with hh | hh
      · have h' : θ = 0 := le_antisymm hh hθ.1
        subst h'
        simp
      · have h' : θ = π / 2 := le_antisymm hθ.2 hh
        subst h'
        rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    rw [epsW, hsin]
    simp [Real.zero_rpow hgam]


theorem Wt_nonneg_Icc {α z θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    0 ≤ Work.Spaces.Wt α z θ := by
  rw [Work.Spaces.Wt]
  refine mul_nonneg ?_ ?_
  · rw [Work.Spaces.w]; positivity
  · rw [Work.Spaces.wTheta]
    exact Real.rpow_nonneg (sin_two_nonneg hθ) _

/-! ## The `z`- and `θ`-shifts in the log coordinates -/

theorem zShift_exp' (s p : ℝ) : zShift (Real.exp s) p = Real.exp (s - p) := by
  rw [zShift, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]

theorem thShift_arctan_exp' (ζ p : ℝ) :
    thShift (Real.arctan (Real.exp ζ)) p = Real.arctan (Real.exp (ζ - p)) := by
  rw [thShift, Real.tan_arctan, ← Real.exp_add, sub_eq_add_neg]

end Work.FTS.StrongEps.EpsSqTools
