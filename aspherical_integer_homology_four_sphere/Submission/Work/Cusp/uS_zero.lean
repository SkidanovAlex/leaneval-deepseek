import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The sup norm is homogeneous: `nrm (c • p) = |c| * nrm p`.  (Local copy, so that this file does
not depend on modules that are still in progress.) -/
theorem nrm_smul_aux' (c : ℝ) (p : E2) : nrm (c • p) = |c| * nrm p := by
  rw [nrm, nrm]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [abs_mul, abs_mul, ← mul_max_of_nonneg _ _ (abs_nonneg c)]

/-- **The radial projection `bnd p = (nrm p)⁻¹ • p` has sup norm `1`** as soon as `nrm p ≠ 0`.
Note that no membership `p ∈ Sq` is needed: any non-zero `p` is scaled onto the boundary `∂Sq`. -/
theorem nrm_bnd_aux {p : E2} (h0 : 0 < nrm p) : nrm (bnd p) = 1 := by
  rw [bnd, nrm_smul_aux', abs_of_pos (inv_pos.mpr h0), inv_mul_cancel₀ (ne_of_gt h0)]

/-- `uPerim` maps the boundary `∂Sq = {nrm = 1}` into `[0,1)`: the four branches of the definition
take the values `(1-q₁)/8 ∈ [0,1/4]`, `(3-q₀)/8 ∈ [1/4,1/2]`, `(5+q₁)/8 ∈ [1/2,3/4]` and
`(7+q₀)/8 ∈ (3/4,1)`.  (Local copy of `uPerim_mem`.) -/
theorem uPerim_mem_aux {q : E2} (hq : nrm q = 1) : 0 ≤ uPerim q ∧ uPerim q < 1 := by
  have hmax : max |q 0| |q 1| = 1 := by unfold nrm at hq; exact hq
  have h0 : |q 0| ≤ 1 := hmax ▸ le_max_left |q 0| |q 1|
  have h1 : |q 1| ≤ 1 := hmax ▸ le_max_right |q 0| |q 1|
  have hq0le : q 0 ≤ 1 := (abs_le.mp h0).2
  have hq0ge : -1 ≤ q 0 := (abs_le.mp h0).1
  have hq1le : q 1 ≤ 1 := (abs_le.mp h1).2
  have hq1ge : -1 ≤ q 1 := (abs_le.mp h1).1
  unfold uPerim
  by_cases hA : q 0 = 1
  · simp only [hA, ↓reduceIte]; constructor <;> nlinarith
  · simp only [hA, ↓reduceIte]
    by_cases hB : q 1 = -1
    · simp only [hB, ↓reduceIte]; constructor <;> nlinarith
    · simp only [hB, ↓reduceIte]
      by_cases hC : q 0 = -1
      · simp only [hC, ↓reduceIte]; constructor <;> nlinarith
      · simp only [hC, ↓reduceIte]
        have hq0lt : q 0 < 1 := lt_of_le_of_ne hq0le hA
        constructor <;> nlinarith

/-- **The perimeter lift `uS c` at the cut `c = 0` is the perimeter parameter `u` itself** off the
origin.  `uS 0 p = Int.fract (u p)`, and for `nrm p > 0` the radial projection `bnd p` lands on
`∂Sq`, where `u p = uPerim (bnd p) ∈ [0,1)`; hence `Int.fract (u p) = u p`. -/
theorem uS_zero {p : E2} (h0 : 0 < nrm p) : uS 0 p = u p := by
  have hb : nrm (bnd p) = 1 := nrm_bnd_aux h0
  have hu : 0 ≤ u p ∧ u p < 1 := by
    rw [u]; exact uPerim_mem_aux hb
  simp only [uS, zero_add, sub_zero]
  exact Int.fract_eq_self.mpr hu

end Work.Cusp
