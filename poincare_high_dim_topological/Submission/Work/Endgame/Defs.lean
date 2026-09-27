import Mathlib

/-!
# Endgame: a compact Hausdorff space with `ℝⁿ` as a puncture is `𝕊ⁿ`

This chapter packages the last step of the proof of the generalized topological
Poincaré conjecture in dimensions `≥ 5` (`poincare_high_dim_topological`).

If `M` is a compact Hausdorff space, `p : M`, and the complement of `p` (with the
subspace topology) is homeomorphic to `ℝⁿ`, then `M` is homeomorphic to the unit
sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`.

The route is the one-point compactification:

* `onePointComplHomeomorph p : OnePoint ({p}ᶜ : Set M) ≃ₜ M` — a compact
  Hausdorff space with one point removed is the one-point compactification of the
  complement (`OnePoint.equivOfIsEmbeddingOfRangeEq`, the universal property of
  `OnePoint`).
* `Homeomorph.onePointCongr` — the one-point compactification is functorial, so
  a homeomorphism `{p}ᶜ ≃ₜ ℝⁿ` induces `OnePoint ({p}ᶜ) ≃ₜ OnePoint ℝⁿ`.
* `onePointEuclideanHomeomorphSphere n : OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ 𝕊ⁿ`
  — the one-point compactification of `ℝⁿ` is `𝕊ⁿ`
  (`onePointEquivSphereOfFinrankEq`, stereographic projection).

The main results are `Work.Endgame.homeomorphSphereOfComplHomeomorph` and its
`Nonempty` form `Work.Endgame.nonempty_homeomorph_sphere_of_compl_homeomorph`.

## Conventions

* `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`.
* `𝕊ⁿ` is `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1`, the same type as
  in the challenge statement `Challenge.lean`.
* The complement of a point is written `({p}ᶜ : Set M)`, i.e. the subtype of `M`
  on the open set `{p}ᶜ`; it is definitionally `{x : M // x ≠ p}`.
-/

open Metric (sphere)
open Set Filter Topology
open scoped OnePoint

namespace Work.Endgame

universe u

variable {M : Type*}

/-- A compact Hausdorff space `M` is the one-point compactification of the complement of any
point `p : M`: the map `∞ ↦ p`, `x ↦ x` is a homeomorphism. This is the universal property of
`OnePoint` (`OnePoint.equivOfIsEmbeddingOfRangeEq`) applied to the open embedding
`({p}ᶜ : Set M) ↪ M`, whose range misses exactly `p`. -/
noncomputable def onePointComplHomeomorph [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (p : M) : OnePoint ({p}ᶜ : Set M) ≃ₜ M :=
  OnePoint.equivOfIsEmbeddingOfRangeEq p (Subtype.val : ({p}ᶜ : Set M) → M)
    IsEmbedding.subtypeVal (by rw [Subtype.range_val])

/-- The one-point compactification of `ℝⁿ` is the unit sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`, by stereographic
projection. -/
noncomputable def onePointEuclideanHomeomorphSphere (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  onePointEquivSphereOfFinrankEq (by simp)

/-- The complement of the point at infinity in `OnePoint X` is `X`. -/
noncomputable def complInftyHomeomorph (X : Type u) [TopologicalSpace X] :
    ({∞}ᶜ : Set (OnePoint X)) ≃ₜ X :=
  ((OnePoint.isOpenEmbedding_coe.toIsEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (by
      rw [← OnePoint.compl_range_coe, compl_compl]))).symm

end Work.Endgame
