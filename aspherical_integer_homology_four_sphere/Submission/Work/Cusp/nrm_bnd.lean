/-
# The sup norm of the radial projection to `∂Sq`

`bnd p = (nrm p)⁻¹ • p` is the radial projection of `p` to the boundary of the square `Sq`, so that
`p = nrm p • bnd p`.  For `p ≠ 0` the projection really lands on `∂Sq`: this file proves that its sup
norm is `1`.  (At `p = 0` the projection is `0`, which is why the hypothesis `p ≠ 0` is needed.)
-/
import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The sup norm of a nonzero point of `E2` is positive. -/
theorem nrm_pos {p : E2} (hp : p ≠ 0) : 0 < nrm p := by
  have h0 : p 0 ≠ 0 ∨ p 1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hp (by ext i; fin_cases i <;> simp [h.1, h.2])
  rw [nrm]
  rcases h0 with h | h
  · exact lt_of_lt_of_le (abs_pos.mpr h) (le_max_left _ _)
  · exact lt_of_lt_of_le (abs_pos.mpr h) (le_max_right _ _)

/-- The sup norm is homogeneous: `nrm (c • p) = |c| * nrm p`. -/
theorem nrm_smul_aux (c : ℝ) (p : E2) : nrm (c • p) = |c| * nrm p := by
  rw [nrm, nrm]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [abs_mul, abs_mul, ← mul_max_of_nonneg _ _ (abs_nonneg c)]

/-- **The radial projection of a nonzero point has sup norm `1`.** -/
theorem nrm_bnd {p : E2} (hp : p ≠ 0) : nrm (bnd p) = 1 := by
  have hpos : 0 < nrm p := nrm_pos hp
  rw [bnd, nrm_smul_aux, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]

end Work.Cusp
