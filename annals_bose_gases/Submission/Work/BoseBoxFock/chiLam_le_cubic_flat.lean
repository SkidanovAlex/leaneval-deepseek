import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseFixB1.chi_boundary_taylor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **Cubic flat decay of the box cutoff `χ_Λ` at the boundary of its support.**

`χ_Λ(x) = χ(x/ℓ)` (FS's `eq:Def_chi`, `χ_Λ` supported in the ball of radius `ℓ/2`), so with
`z = ℓ⁻¹ • x` the assertion reads `χ z ≤ C (max 0 (1/2 - ‖z‖))³`.  Inside the support this is
`Work.BoseFixB1.chi_boundary_taylor` at `N = 3` (the corpus bump is flat to all orders at
`‖z‖ = 1/2`, since it is `C^∞` and vanishes outside the ball); outside, both sides vanish —
`χ z = 0` for `‖z‖ ≥ 1/2` and `max 0 (1/2 - ‖z‖) = 0`. -/
theorem chiLam_le_cubic_flat {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin 3),
      Work.BoseK15.corpusBox.chiLam ℓ x ≤ C * (max 0 (ℓ / 2 - ‖x‖) / ℓ) ^ 3 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.BoseFixB1.chi_boundary_taylor 3
  refine ⟨C₀, le_of_lt hC₀pos, fun x => ?_⟩
  -- `(max 0 (ℓ/2 - ‖x‖)) / ℓ = max 0 (1/2 - ‖ℓ⁻¹ • x‖)`, i.e. the argument is invariant under
  -- the change of variables `x ↦ ℓ⁻¹ • x` with `ℓ > 0`.
  have harg : (max 0 (ℓ / 2 - ‖x‖)) / ℓ = max 0 (1 / 2 - ‖ℓ⁻¹ • x‖) := by
    rw [← max_div_div_right hℓ.le, zero_div]
    congr 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le), inv_mul_eq_div]
    field_simp
  rw [Work.BoseB4.BoxData.chiLam_apply, Work.BoseK15.corpusBox_chi, harg]
  rcases le_or_gt ‖ℓ⁻¹ • x‖ (1 / 2) with h | h
  · -- inside the support: the flat-decay bound at the rescaled point
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1 / 2 - ‖ℓ⁻¹ • x‖)]
    exact hC₀ _ h
  · -- outside the support: both sides are `0`
    rw [Submission.BoseGases.chi_eq_zero_of_norm_gt _ h,
      max_eq_left (by linarith : 1 / 2 - ‖ℓ⁻¹ • x‖ ≤ 0)]
    norm_num

end Work.BoseBoxFock
