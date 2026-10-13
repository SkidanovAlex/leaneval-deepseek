/-
Copyright: work module for the Elgindi finite-time singularity project.

# The near-zero bound on `∂_z f` and `∂_z² f`

For a function `f` smooth on an open neighbourhood of the closed quadrant
`[0,∞) × [0,π/2]` whose radial derivative vanishes at `z = 0` on the whole
angular interval,

  `∂_z f(0,θ) = 0`   for every `θ ∈ [0,π/2]`,

there is a neighbourhood `(0,δ)` of `z = 0` and a constant `M ≥ 0` with

  `|∂_z f(z,θ)| ≤ M z`  and  `|∂_z² f(z,θ)| ≤ M`   for all `z ∈ (0,δ)`, `θ ∈ [0,π/2]`.

This is the elementary second-order Taylor fact used in the coercivity chapter:
`∂_z f = O(z)` and `∂_z² f = O(1)` near the origin, uniformly in the angle.

The proof is a compactness argument.  Smoothness of `f` on the open
neighbourhood `U = (-1,∞) × (-1,π/2+1)` of the closed quadrant makes the second
radial derivative `∂_z² f` continuous on the box `[0,1] × [0,π/2]`, hence bounded
there by `M = boxSup 1 (∂_z² f)`.  The bound `|∂_z f(z,θ)| ≤ M z` then follows by
writing `∂_z f(z,θ) = ∫_0^z ∂_z² f(s,θ) ds` (fundamental theorem of calculus on
the `θ`-slice) and estimating the integrand by `M`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.SmoothCompact_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

theorem Dz_bound_near_zero (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (h0 : ∀ θ ∈ Spaces.Iθ, Spaces.pz f 0 θ = 0) :
    ∃ M δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ M ∧
      ∀ z ∈ Set.Ioo 0 δ, ∀ θ ∈ Spaces.Iθ,
        |Spaces.pz f z θ| ≤ M * z ∧ |Spaces.pz (Spaces.pz f) z θ| ≤ M := by
  -- `∂_z² f` is smooth on a neighbourhood of the closed quadrant.
  have hsm2 : Spaces.SmoothNbhd (Spaces.pz (Spaces.pz f)) :=
    (Spaces.SmoothNbhd.pz hsm).pz
  -- hence it is bounded on the box `[0,1] × [0,π/2]`.
  have hbdd : BddAbove (Spaces.boxSet 1 (Spaces.pz (Spaces.pz f))) :=
    Spaces.bddAbove_boxSup_of_continuousOn (Spaces.continuousOn_box_of_contDiffOn hsm2)
  refine ⟨Spaces.boxSup 1 (Spaces.pz (Spaces.pz f)), 1, one_pos, le_refl 1,
    Spaces.boxSup_nonneg zero_le_one hbdd, ?_⟩
  intro z hz θ hθ
  have hz01 : z ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  refine ⟨?_, Spaces.le_boxSup hbdd hz01 hθ⟩
  -- Fundamental theorem of calculus for the `θ`-slice of `∂_z f`.
  have hInt := Spaces.hardyZ_integral_pz_eq_sub (Spaces.pz f) (Spaces.SmoothNbhd.pz hsm) hθ
    (le_refl (0:ℝ)) (le_of_lt hz.1)
  have hkey : Spaces.pz f z θ = ∫ s in (0:ℝ)..z, Spaces.pz (Spaces.pz f) s θ := by
    rw [hInt, h0 θ hθ, sub_zero]
  rw [hkey]
  -- Bound the integral by `M * z`.
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => Spaces.pz (Spaces.pz f) s θ) (a := (0:ℝ)) (b := z)
    (C := Spaces.boxSup 1 (Spaces.pz (Spaces.pz f))) ?_
  · rw [Real.norm_eq_abs] at hb
    rwa [sub_zero, abs_of_pos hz.1] at hb
  · intro x hx
    rw [Set.uIoc_of_le (le_of_lt hz.1)] at hx
    have hxI : x ∈ Set.Icc (0:ℝ) 1 :=
      ⟨le_of_lt hx.1, le_trans hx.2 (le_of_lt hz.2)⟩
    rw [Real.norm_eq_abs]
    exact Spaces.le_boxSup hbdd hxI hθ

end Work.Coercivity
