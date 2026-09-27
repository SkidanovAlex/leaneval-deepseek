import Mathlib

/-!
# A compact Hausdorff space with `ℝⁿ` as a puncture is `𝕊ⁿ`

If `M` is compact Hausdorff, `p : M`, and the complement of `p` (with the subspace topology)
is homeomorphic to `ℝⁿ = EuclideanSpace ℝ (Fin n)`, then `M` is homeomorphic to the unit
sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`.

The proof is the uniqueness of the one-point compactification:

* `({p}ᶜ : Set M) ↪ M` is an embedding with range exactly the complement of `p`, so by
  `OnePoint.equivOfIsEmbeddingOfRangeEq` the compact Hausdorff space `M` is the one-point
  compactification of `{p}ᶜ`; hence `M ≃ₜ OnePoint ({p}ᶜ)`.
* The homeomorphism `h : {p}ᶜ ≃ₜ ℝⁿ` is functorial under the one-point compactification,
  giving `OnePoint ({p}ᶜ) ≃ₜ OnePoint ℝⁿ`.
* The one-point compactification of `ℝⁿ` is `𝕊ⁿ` (`onePointEquivSphereOfFinrankEq`,
  stereographic projection).

This is the last step of `poincare_high_dim_topological`.
-/

open Metric (sphere)
open Topology
open scoped OnePoint

namespace Work.Endgame

/-- A compact Hausdorff space `M` whose complement of a point `p` is homeomorphic to `ℝⁿ` is
homeomorphic to the unit sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`. -/
theorem nonempty_homeomorph_sphere_of_compl_homeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] (p : M) (h : ({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  -- `M` is the one-point compactification of the puncture `{p}ᶜ`.
  have e : OnePoint ({p}ᶜ : Set M) ≃ₜ M :=
    OnePoint.equivOfIsEmbeddingOfRangeEq p (Subtype.val : ({p}ᶜ : Set M) → M)
      IsEmbedding.subtypeVal (by rw [Subtype.range_val])
  -- Compose: `M ≃ OnePoint {p}ᶜ ≃ OnePoint ℝⁿ ≃ 𝕊ⁿ`.
  exact ⟨(e.symm.trans h.onePointCongr).trans (onePointEquivSphereOfFinrankEq (by simp))⟩

end Work.Endgame
