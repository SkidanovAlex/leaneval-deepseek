import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- Positive rescalings do not change the perimeter parameter: `bnd` is scale invariant. -/
lemma nrm_smul_of_pos {c : ℝ} (hc : 0 < c) (p : E2) : nrm (c • p) = c * nrm p := by
  unfold nrm
  rw [PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, abs_mul, abs_mul,
    abs_of_pos hc]
  exact (mul_max_of_nonneg _ _ (le_of_lt hc)).symm

/-- The radial projection `bnd` is invariant under positive rescalings. -/
lemma bnd_smul_of_pos {c : ℝ} (hc : 0 < c) (p : E2) : bnd (c • p) = bnd p := by
  unfold bnd
  rw [nrm_smul_of_pos hc, smul_smul]
  congr 1
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), mul_one]

theorem u_smul {c : ℝ} (hc : 0 < c) (p : E2) : u (c • p) = u p := by
  unfold u
  rw [bnd_smul_of_pos hc]

end Work.Cusp
