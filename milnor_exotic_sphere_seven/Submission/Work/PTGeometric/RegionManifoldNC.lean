import Submission.Work.PTGeometric.regionManifoldTheorem

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the region-charting theorem for a non-compact ambient

`Work.PTGeometric.RegionManifoldTheorem k` (`SourceRegion.lean`, proved in
`regionManifoldTheorem.lean`) charts the region `{Φ ≤ 0}` of a smooth `Φ` on a **compact** `T2` smooth
manifold with boundary `A`, under the hypotheses

* `Φ` is a submersion at every zero,
* `Φ` is one-sided at the boundary zeros (`∂A ∩ {Φ = 0}` is tangent to `{Φ = 0}` with the region on
  the interior side).

The source construction of the last mile (README §29) needs the same theorem with the ambient
`A = EuclideanHalfSpace ((8+k)+1)`, which is **not compact** (the source of the null-homotopy is the
half-space, so that the cube coordinate — in which TUBULAR's collapse data are smooth — is an honest
coordinate there; see README §29.1).  The only place where compactness of the ambient was used in the
proof is the compactness of the *region*, so the theorem below replaces `[CompactSpace A]` by the
hypothesis `IsCompact {x | Φ x ≤ 0}`.

## Main results

* `Work.PTGeometric.RegionManifoldTheoremOfIsCompact`
* `Work.PTGeometric.regionManifoldTheorem_of_isCompact`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **The region-charting theorem for a non-compact ambient with a compact region.**

Everything is as in `Work.PTGeometric.RegionManifoldTheorem`, except that the ambient `A` is assumed
only `T2` (so that it may be the half-space `EuclideanHalfSpace ((8+k)+1)`) and the *region*
`{x | Φ x ≤ 0}` is assumed compact. -/
def RegionManifoldTheoremOfIsCompact (k : ℕ) : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) A]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ A] [T2Space A] (Φ : A → ℝ),
    ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ Φ →
    (∀ x : A, Φ x = 0 → IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ Φ x) →
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

/-- **The region-charting theorem for a non-compact ambient with a compact region** (proof): the
region `{Φ ≤ 0}` of `RegionSetup` needs only `hK`, and the remaining hypotheses of
`RegionManifoldTheorem` are produced by the generalized setup. -/
theorem regionManifoldTheorem_of_isCompact (k : ℕ) : RegionManifoldTheoremOfIsCompact k := by
  intro A _ _ _ _ Φ hΦ hsub hone hK
  let S : RegionSetup k := { A := A, Φ := Φ, hΦ := hΦ, hsub := hsub, hone := hone, hK := hK }
  refine ⟨S.Region, inferInstance, S.chartedSpaceOfRegion, S.isManifoldOfRegion,
    S.compactSpaceOfRegion, S.t2SpaceOfRegion, Homeomorph.refl S.Region, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact S.mem_boundary_iff m
  · intro F _ _ f hf
    intro m
    exact S.contMDiffOn_comp_val F f univ hf.contMDiffOn m (Set.mem_univ m)
  · intro F _ _ f W hf
    exact S.contMDiffOn_comp_val F f W hf
  · intro F _ _ f m hm hf
    exact S.isSubmersionAt_comp_val f m hm hf
  · intro f m hm he hf
    exact S.isSubmersionAt_comp_val_boundary f m hm he hf

end

end Work.PTGeometric
