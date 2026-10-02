import Mathlib
import Submission.Work.Milnor.ChartDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology RealInnerProductSpace
open TopologicalSpace Set Metric
open Submission.Milnor

namespace Work.Milnor

/-- Elements of the orthogonal complement of the span of a *real* unit quaternion `y` (i.e. `y = 1`
or `y = -1`) have zero real part.  Equivalently, for `y = ±1`, `(ℝ ∙ y)ᗮ` is the space of purely
imaginary quaternions. -/
lemma orthogonal_span_re (y : Submission.Milnor.QS3)
    (hy : (y : Quaternion ℝ) = 1 ∨ (y : Quaternion ℝ) = -1)
    (u : ↥(ℝ ∙ (↑(-y) : Quaternion ℝ))ᗮ) : (↑u : Quaternion ℝ).re = 0 := by
  have hinner : inner ℝ (-(↑y) : Quaternion ℝ) (↑u : Quaternion ℝ) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp u.2
  rcases hy with h | h
  · rw [h] at hinner
    simpa [Quaternion.inner_def] using hinner
  · rw [h] at hinner
    simpa [Quaternion.inner_def] using hinner

theorem stereo_chart_re (y : Submission.Milnor.QS3)
    (hy : (y : Quaternion ℝ) = 1 ∨ (y : Quaternion ℝ) = -1) :
    ((chartAt E3 y) y = 0) ∧
    (∀ w : E3, (((chartAt E3 y).symm w : Submission.Milnor.QS3) : Quaternion ℝ).re
        = (y : Quaternion ℝ).re * hfun w) := by
  constructor
  · rw [show chartAt E3 y = stereographic' 3 (-y) from rfl, stereographic',
      OpenPartialHomeomorph.trans_apply]
    rw [stereographic_neg_apply y]
    rw [Homeomorph.toOpenPartialHomeomorph_apply, LinearIsometryEquiv.coe_toHomeomorph]
    exact map_zero _
  · intro w
    rw [show chartAt E3 y = stereographic' 3 (-y) from rfl]
    rw [stereographic'_symm_apply]
    set U : ↥(ℝ ∙ (↑(-y) : Quaternion ℝ))ᗮ ≃ₗᵢ[ℝ] E3 :=
      (OrthonormalBasis.fromOrthogonalSpanSingleton 3
        (ne_zero_of_mem_unit_sphere (-y))).repr with hU
    have hre : (↑(U.symm w) : Quaternion ℝ).re = 0 := orthogonal_span_re y hy (U.symm w)
    have hnorm : ‖(↑(U.symm w) : Quaternion ℝ)‖ = ‖w‖ := by
      rw [← Submodule.coe_norm (U.symm w), ← U.norm_map (U.symm w), U.apply_symm_apply]
    have hnegre : (↑(-y) : Quaternion ℝ).re = -((y : Quaternion ℝ)).re := by simp
    simp only [Quaternion.re_add, Quaternion.re_smul]
    rw [hre, hnorm, hnegre, hfun]
    simp only [smul_eq_mul]
    ring_nf

end Work.Milnor
