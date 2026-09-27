import Mathlib
import Submission.Work.Drive.projImmersion
import Submission.Work.Drive.ProjectiveChartDefs

namespace Work.Drive

/-!
# `projCoordFunDerivE` is homogeneous of degree `-1` in its base point

The projective coordinate derivative `Work.Drive.projCoordFunDerivE i v` (the derivative of the
projective chart `projCoordFun i` at `v`, see `Submission/Work/Drive/projImmersion.lean`) computes
`w ↦ ((v_i w_j - v_j w_i)/v_i²)_j`; it therefore scales as `t⁻¹` when the base point is multiplied
by `t ≠ 0`:

* `projCoordFunDeriv_smul_inv` / `projCoordFunDerivE_smul_inv` — the linear maps themselves;
* `map_projCoordFunDerivE_smul` — the consequence used by the chain route: the **image** of any
  submodule `S` under `projCoordFunDerivE i` does not change when the base point is rescaled.  This
  is what lets `Submission/Work/Drive/classTripleConversion.lean` use one and the same chart index
  `i` for the three class derivatives `projCoordFunDerivE i (v k)` of the three proportional base
  points `v k` (see `Work.Drive.range_mfderiv_projMk`), without having to compare the chosen
  representatives: changing the representative rescales the linear map by a non-zero scalar, hence
  leaves every image untouched.
-/

/-- **`projCoordFunDeriv` is homogeneous of degree `-1` in its base point.** -/
lemma projCoordFunDeriv_smul_inv {n : ℕ} (i : Fin (n + 1)) (v : Eucl n) {t : ℝ} (ht : t ≠ 0) :
    projCoordFunDeriv i (t • v) = t⁻¹ • projCoordFunDeriv i v := by
  ext w j
  simp only [projCoordFunDeriv_apply, smul_apply, Pi.smul_apply, smul_eq_mul, PiLp.smul_apply]
  field_simp

/-- **`projCoordFunDerivE` is homogeneous of degree `-1` in its base point.** -/
lemma projCoordFunDerivE_smul_inv {n : ℕ} (i : Fin (n + 1)) (v : Eucl n) {t : ℝ} (ht : t ≠ 0) :
    projCoordFunDerivE i (t • v) = t⁻¹ • projCoordFunDerivE i v := by
  simp only [projCoordFunDerivE, projCoordFunDeriv_smul_inv i v ht]
  ext w
  simp

theorem map_projCoordFunDerivE_smul {n : ℕ} (i : Fin (n + 1)) (v : Work.Drive.Eucl n) {t : ℝ}
    (ht : t ≠ 0) (S : Submodule ℝ (Work.Drive.Eucl n)) :
    Submodule.map (Work.Drive.projCoordFunDerivE i (t • v)).toLinearMap S
      = Submodule.map (Work.Drive.projCoordFunDerivE i v).toLinearMap S := by
  rw [projCoordFunDerivE_smul_inv i v ht, ContinuousLinearMap.toLinearMap_smul,
    Submodule.map_smul _ S _ (inv_ne_zero ht)]

end Work.Drive
