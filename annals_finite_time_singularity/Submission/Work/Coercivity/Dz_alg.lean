/-
Copyright: work module for the Elgindi finite-time singularity project.

# Elementary facts about the near-zero behaviour of `z ↦ z (D_z f · w)²`

Two elementary ingredients used by the proof of `Dz_near_zero_bound`:

* `zw_sq_factor`: the algebraic identity

    `z (D_z f z θ · w z)² = (∂_z f z θ)² (1+z)^4 / z`     (`z ≠ 0`),

  which turns the boundary condition `z (D_z f · w)² → 0` at `0⁺` into a statement about
  the plain `z`-derivative `∂_z f`;

* `slice_sub_zero_bound`: the radial fundamental-theorem-of-calculus bound for a
  `SmoothNbhd` function: if the `z`-derivative of the slice `z ↦ H z θ` is bounded by `M`
  on `[0,z]`, then `|H z θ - H 0 θ| ≤ M z`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.HardyZ

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

/-- **Algebraic identity.**  With `D_z f z θ = z ∂_z f z θ` and `w z = (1+z)²/z²`,
for `z ≠ 0`

  `z (D_z f z θ · w z)² = (∂_z f z θ)² (1+z)^4 / z`. -/
theorem zw_sq_factor (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : z ≠ 0) :
    z * (Spaces.Dz f z θ * Spaces.w z) ^ 2
      = (Spaces.pz f z θ) ^ 2 * (1 + z) ^ 4 / z := by
  simp only [Spaces.Dz, Spaces.w]
  field_simp

/-- **Radial fundamental-theorem-of-calculus bound.**  If the `z`-derivative of the slice
`z ↦ H z θ` of a function smooth on a neighbourhood of the closed quadrant is bounded by
`M` on `[0,z]`, then the slice varies by at most `M z` over that interval. -/
theorem slice_sub_zero_bound (H : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd H) {θ z M : ℝ}
    (hθ : θ ∈ Spaces.Iθ) (hz : 0 ≤ z) (hM : ∀ u ∈ Set.Icc 0 z, |Spaces.pz H u θ| ≤ M) :
    |H z θ - H 0 θ| ≤ M * z := by
  have hsub : ∫ s in (0:ℝ)..z, Spaces.pz H s θ = H z θ - H 0 θ :=
    Spaces.hardyZ_integral_pz_eq_sub H hsm hθ (le_refl 0) hz
  have hle : |∫ s in (0:ℝ)..z, Spaces.pz H s θ| ≤ M * z := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun s => Spaces.pz H s θ) (a := (0:ℝ)) (b := z) (C := M) (fun x hx => by
        rw [Set.uIoc_of_le hz] at hx
        rw [Real.norm_eq_abs]
        exact hM x ⟨le_of_lt hx.1, hx.2⟩)
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hz] at h
  rwa [hsub] at hle

end Work.Coercivity
