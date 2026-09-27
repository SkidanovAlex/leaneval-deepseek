/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Brown
-/
import Mathlib
import Submission.Work.Brown.Basic

/-!
# The complement of a point in `𝕊ⁿ` is an open `n`-cell

The sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹` with a single point `p` removed is an open `n`-cell in the sense of
`Work.Brown.IsOpenCell`, i.e. it is an open subset of `𝕊ⁿ` homeomorphic to `ℝⁿ`.

**Proof.** Stereographic projection.  Write `v : ℝⁿ⁺¹` for the vector underlying `p`, so that
`hv : ‖v‖ = 1`.  Mathlib's `stereographic hv` is an open partial homeomorphism from `𝕊ⁿ` to the
hyperplane `(ℝ ∙ v)ᗮ` with source the complement of the north pole `⟨v, _⟩` of the projection;
its inverse is therefore an open embedding

* `(ℝ ∙ v)ᗮ → 𝕊ⁿ`, with range `{⟨v, _⟩}ᶜ = {p}ᶜ`
  (`isOpenEmbedding_stereographic_symm`, `range_stereographic_symm`),

which exhibits `({p}ᶜ : Set 𝕊ⁿ)` as homeomorphic to `(ℝ ∙ v)ᗮ`.  The orthogonal complement of the
line through the unit vector `v` is an `n`-dimensional real inner product space, and
`OrthonormalBasis.fromOrthogonalSpanSingleton` provides an orthonormal basis of it with `n`
elements, whose `OrthonormalBasis.repr` is a linear isometry equivalence
`(ℝ ∙ v)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)` and hence a homeomorphism.

Openness is the only other ingredient: a singleton in the (metric, hence T1) sphere is closed, so
its complement is open.

## Main result

* `Work.Brown.Cell.isOpenCell_compl_point_sphere`
-/

open Metric Set
open scoped EuclideanSpace

namespace Work.Brown.Cell

/-- **The complement of a point of `𝕊ⁿ` is homeomorphic to `ℝⁿ`** (stereographic projection).

The inverse of the stereographic projection from the point `p` is an open embedding of the
hyperplane orthogonal to `(p : ℝⁿ⁺¹)` with range `{p}ᶜ`; composing it with the orthonormal-basis
identification of that hyperplane with `ℝⁿ` gives a homeomorphism `{p}ᶜ ≃ₜ ℝⁿ`. -/
theorem nonempty_homeomorph_compl_point_sphere {n : ℕ}
    (p : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Nonempty (({p}ᶜ : Set ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ≃ₜ
      EuclideanSpace ℝ (Fin n)) := by
  -- The vector underlying `p`, and its norm.
  let v : EuclideanSpace ℝ (Fin (n + 1)) := p
  have hv : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hv
    simp at hv
  -- The inverse of stereographic projection is an open embedding with range `{p}ᶜ`.
  have hrange : Set.range ⇑(stereographic hv).symm = {p}ᶜ := by
    rw [range_stereographic_symm]
  -- The hyperplane orthogonal to `v` is an `n`-dimensional inner product space.
  refine ⟨((Topology.IsEmbedding.toHomeomorph
      (isOpenEmbedding_stereographic_symm hv).toIsEmbedding).trans
      (Homeomorph.setCongr hrange)).symm.trans
    (OrthonormalBasis.fromOrthogonalSpanSingleton n hv0).repr.toHomeomorph⟩

/-- **The complement of a point in `𝕊ⁿ` is an open `n`-cell.** -/
theorem isOpenCell_compl_point_sphere {n : ℕ}
    (p : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Work.Brown.IsOpenCell n ({x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) |
      x ≠ p}) := by
  refine ⟨?_, ?_⟩
  · show IsOpen ({p}ᶜ : Set ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    exact isOpen_compl_singleton
  · exact nonempty_homeomorph_compl_point_sphere p

end Work.Brown.Cell
