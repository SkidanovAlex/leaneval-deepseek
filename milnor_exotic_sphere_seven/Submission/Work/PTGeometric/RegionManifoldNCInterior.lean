import Submission.Work.PTGeometric.RegionManifoldNC

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the region-charting theorem with an *interior-only* submersion hypothesis

`Work.PTGeometric.SourceRegionPhiFn_false` (see
`Submission/Work/PTGeometric/exists_sourceRegionPhi_DIAGNOSIS.md`) shows that Mathlib's
`Manifold.IsSubmersionAt` at a *boundary* point is incompatible with the source region's boundary
tangency: a submersion at a boundary zero has the boundary of the ambient as its local fibre, which
forces the region `{Φ ≤ 0}` to contain a whole neighbourhood of that point, and then (the boundary
being connected) the region is unbounded.  The region that the null-bordism needs is instead
*tangent* to the boundary at the pieces (a cusp region), where `Φ` is a submersion only at its
**interior** zeros.

This file records that variant of the region-charting theorem, with exactly the statement of
`Work.PTGeometric.RegionManifoldTheoremOfIsCompact` except that `hsub` is required only at the
interior zeros of `Φ`.

## Main definitions

* `Work.PTGeometric.RegionManifoldTheoremOfIsCompactInterior`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

def RegionManifoldTheoremOfIsCompactInterior (k : ℕ) : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) A]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ A] [T2Space A] (Φ : A → ℝ),
    ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ Φ →
    (∀ x : A, Φ x = 0 → x ∈ (𝓡∂ ((8 + k) + 1)).interior A →
      IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ Φ x) →
    (∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary A, Φ x = 0 →
      ∃ (e : OpenPartialHomeomorph A (EuclideanHalfSpace ((8 + k) + 1))) (c : ℝ),
        e ∈ IsManifold.maximalAtlas (𝓡∂ ((8 + k) + 1)) ∞ A ∧ x ∈ e.source ∧ c < 0 ∧
        (∀ y ∈ e.source, (e y).1 0 = 0 ↔ y ∈ (𝓡∂ ((8 + k) + 1)).boundary A) ∧
        mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) Φ x
          = c • mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) (fun y : A => (e y).1 0) x) →
    IsCompact {x : A | Φ x ≤ 0} →
    ∃ (M : Type) (_ : TopologicalSpace M)
      (_ : ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M)
      (_ : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M) (_ : CompactSpace M) (_ : T2Space M)
      (e : M ≃ₜ ↥{x : A | Φ x ≤ 0}),
      (∀ m : M, m ∈ (𝓡∂ ((8 + k) + 1)).boundary M ↔
        ((e m : A) ∈ (𝓡∂ ((8 + k) + 1)).boundary A ∨ Φ (e m) = 0)) ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : A → F),
        ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ f →
        ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ (fun m : M => f (e m))) ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : A → F) (W : Set A),
        ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ f W →
        ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ (fun m : M => f (e m))
          {m : M | (e m : A) ∈ W}) ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : A → F) (m : M),
        m ∉ (𝓡∂ ((8 + k) + 1)).boundary M →
        IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ f (e m) →
        IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ (fun y : M => f (e y)) m) ∧
      (∀ (f : A → EuclideanSpace ℝ (Fin k)) (m : M)
        (hm : m ∈ (𝓡∂ ((8 + k) + 1)).boundary M)
        (he : (e m : A) ∈ (𝓡∂ ((8 + k) + 1)).boundary A),
        IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
          (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary A) => f y) ⟨e m, he⟩ →
        IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
          (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => f (e y)) ⟨m, hm⟩)

end

end Work.PTGeometric
