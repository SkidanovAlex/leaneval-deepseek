import Mathlib
import Submission.Work.Milnor.ChartDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for the critical points of `Re : S³ → ℝ`

The unit quaternions `QS3 = S³ ⊂ ℍ` are a charted space modelled on `E3 = ℝ³` through the
stereographic projection of Mathlib (`EuclideanSpace.instChartedSpaceSphere`), so that

* `chartAt E3 y = stereographic' 3 (-y)` is the stereographic projection from `-y`, and
* the inverse chart at `y` sends `w : E3` to the point whose linearised version is
  `chartLin y w`, a linear isometry `E3 → ℍ` with image the orthogonal complement of `y`.

This file collects those definitions and the elementary facts about them, which are used to
compute the derivative of `z ↦ (z : ℍ).re` on `S³`.
-/

open scoped Manifold ContDiff Topology RealInnerProductSpace
open Metric (sphere)
open TopologicalSpace Set

namespace Work.Milnor

noncomputable section

/-- The real part of a quaternion, as a continuous linear map. -/
def qreCLM : Quaternion ℝ →L[ℝ] ℝ where
  toFun q := q.re
  map_add' a b := by simp
  map_smul' a b := by simp
  cont := Quaternion.continuous_re

@[simp] lemma qreCLM_apply (q : Quaternion ℝ) : qreCLM q = q.re := rfl

/-- The linear isometry `E3 → (ℍ ⊖ ℝ·(-y))` underlying the stereographic chart at `y`. -/
def chartLinEquiv (y : Submission.Milnor.QS3) :
    E3 ≃ₗᵢ[ℝ] (ℝ ∙ ((-y : Submission.Milnor.QS3) : Quaternion ℝ))ᗮ :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere (-y))).repr.symm

/-- The chart at `y` of `S³`, linearised.  Its image is the orthogonal complement of `y`, so it
identifies `E3` with the tangent space of `S³` at `y`. -/
def chartLin (y : Submission.Milnor.QS3) : E3 →ₗᵢ[ℝ] Quaternion ℝ :=
  (Submodule.subtypeₗᵢ (ℝ ∙ ((-y : Submission.Milnor.QS3) : Quaternion ℝ))ᗮ).comp
    (chartLinEquiv y).toLinearIsometry

lemma chartLin_apply (y : Submission.Milnor.QS3) (w : E3) :
    (chartLin y w : Quaternion ℝ) =
      ((chartLinEquiv y w : (ℝ ∙ ((-y : Submission.Milnor.QS3) : Quaternion ℝ))ᗮ) :
        Quaternion ℝ) := rfl

lemma chartLin_mem (y : Submission.Milnor.QS3) (w : E3) :
    chartLin y w ∈ (ℝ ∙ ((-y : Submission.Milnor.QS3) : Quaternion ℝ))ᗮ := by
  rw [chartLin_apply]
  exact (chartLinEquiv y w).2

lemma chartLin_surj (y : Submission.Milnor.QS3) {z : Quaternion ℝ}
    (hz : z ∈ (ℝ ∙ ((-y : Submission.Milnor.QS3) : Quaternion ℝ))ᗮ) :
    ∃ w : E3, chartLin y w = z := by
  refine ⟨(chartLinEquiv y).symm ⟨z, hz⟩, ?_⟩
  rw [chartLin_apply, LinearIsometryEquiv.apply_symm_apply]

lemma chartLin_norm (y : Submission.Milnor.QS3) (w : E3) : ‖chartLin y w‖ = ‖w‖ := by

  exact (chartLinEquiv y).norm_map w

end

end Work.Milnor
