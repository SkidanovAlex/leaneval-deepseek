import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

namespace Work.Endgame

/-- Stereographic projection: the unit sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹` with *any* one of its points removed is
homeomorphic to `ℝⁿ`.

Suggested route: `q : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1` gives
`v := (q : EuclideanSpace ℝ (Fin (n + 1)))` with `hv : ‖v‖ = 1` (from `q.2`); Mathlib's
`isOpenEmbedding_stereographic_symm hv` and `range_stereographic_symm hv`
(`Mathlib/Geometry/Manifold/Instances/Sphere.lean`) give a homeomorphism from the hyperplane
`(ℝ ∙ v)ᗮ` onto `Metric.sphere 0 1 \ {v}`, which is the complement of `q` inside the subtype
`Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1`; and `(ℝ ∙ v)ᗮ` is an `n`-dimensional
inner product space, hence homeomorphic to `EuclideanSpace ℝ (Fin n)` via
`FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq` and
`ContinuousLinearEquiv.toHomeomorph` (with `finrank_orthogonal_span_singleton` for the
dimension count). -/
theorem nonempty_compl_homeomorph_euclideanSpace (n : ℕ)
    (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (({q}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ≃ₜ
      EuclideanSpace ℝ (Fin n)) := by
  -- Write `v` for the point of the sphere and record that it is a unit vector.
  let v : EuclideanSpace ℝ (Fin (n + 1)) := q.1
  have hv : ‖v‖ = 1 := norm_eq_of_mem_sphere q
  have hvne : v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact one_ne_zero hv.symm
  -- The stereographic projection from `v` identifies the orthogonal hyperplane `(ℝ ∙ v)ᗮ`
  -- with the sphere minus `v`, i.e. with the complement of `q` (the two subtypes are the same,
  -- since `⟨v, _⟩ = q`).
  have hrange : Set.range (↑(stereographic hv).symm) =
      ({q}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)) := by
    rw [range_stereographic_symm hv]
  have e : (ℝ ∙ v)ᗮ ≃ₜ ({q}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)) :=
    (isOpenEmbedding_stereographic_symm hv).toIsEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)
  -- The orthogonal complement of a line in `ℝⁿ⁺¹` is `n`-dimensional, so it is linearly
  -- (hence topologically) isomorphic to `ℝⁿ`.
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  have hdim : Module.finrank ℝ (ℝ ∙ v)ᗮ = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [Submodule.finrank_orthogonal_span_singleton (n := n) hvne, finrank_euclideanSpace_fin]
  obtain ⟨L⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hdim
  exact ⟨e.symm.trans L.toHomeomorph⟩

end Work.Endgame
