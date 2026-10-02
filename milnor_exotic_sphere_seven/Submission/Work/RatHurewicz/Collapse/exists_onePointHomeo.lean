import Mathlib
import Submission.Work.RatHurewicz.Collapse.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The one-point compactification of `ℝ^d` as the sphere `S^d`, with `∞ ↦ cornerPt d`

The one-point compactification of `ℝ^d` is homeomorphic to the unit sphere `S^d ⊆ ℝ^{d+1}`; here we
produce such a homeomorphism (the inverse of the stereographic projection from the pole
`cornerPt d`) which sends `∞` to the prescribed sphere point `cornerPt d`, the direction of the
corner of the cube.  This is the `d`-dimensional version of
`Work.Stems.Hur2b.CollapseC2.onePointHomeo` (the case `d = 2`).
-/

open scoped unitInterval Topology

namespace Work.RatHurewicz.Collapse

noncomputable section

variable (d : ℕ)

theorem finrank_eq : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) =
    Module.finrank ℝ ↥(ℝ ∙ cornerVec d)ᗮ := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) := ⟨by simp⟩
  rw [Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := d) (cornerVec_ne_zero d)]
  simp

/-- A continuous linear equivalence `ℝ^d ≅ (ℝ ∙ cornerPt d)ᗮ`. -/
def linEquiv : EuclideanSpace ℝ (Fin d) ≃L[ℝ] ↥(ℝ ∙ cornerVec d)ᗮ :=
  (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (finrank_eq d)).some

/-- **The one-point compactification of `ℝ^d` as the unit sphere, with `∞ ↦ cornerPt d`:** the
inverse stereographic projection from the pole `cornerPt d`. -/
def onePointHomeo : OnePoint (EuclideanSpace ℝ (Fin d)) ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 :=
  (linEquiv d).toHomeomorph.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere (norm_cornerVec d))

theorem onePointHomeo_infty : onePointHomeo d OnePoint.infty = cornerPt d := by
  simp only [onePointHomeo, Homeomorph.trans_apply, Homeomorph.onePointCongr_apply,
    OnePoint.map_infty, cornerPt]
  rw [onePointHyperplaneHomeoUnitSphere, OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty]

/-- **The one-point compactification of `ℝ^d` is the sphere `S^d`, with `∞ ↦ cornerPt d`.** -/
theorem exists_onePointHomeo (d : ℕ) :
    ∃ e : OnePoint (EuclideanSpace ℝ (Fin d)) ≃ₜ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1,
      e OnePoint.infty = cornerPt d :=
  ⟨onePointHomeo d, onePointHomeo_infty d⟩

end

end Work.RatHurewicz.Collapse
