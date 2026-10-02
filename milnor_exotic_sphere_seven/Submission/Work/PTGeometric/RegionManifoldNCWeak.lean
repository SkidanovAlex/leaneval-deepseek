import Submission.Work.PTGeometric.RegionManifoldNCInterior

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the region-charting theorem in the form the source region needs

The two earlier forms are unusable for the source region, for proved reasons:

* `Work.PTGeometric.RegionManifoldTheoremOfIsCompact` requires `Manifold.IsSubmersionAt` at **all**
  zeros.  At a *boundary* zero that is the local-normal-form notion, which forces the region to
  contain a whole neighbourhood of the point; then the set of boundary points of the region is clopen
  in the connected `∂A`, so a compact region cannot meet `∂A` at all
  (`Work.PTGeometric.sourceRegionPhiFn_false`, `exists_sourceRegionPhi_DIAGNOSIS.md`).  But the source
  region *must* meet `∂A` (the pieces are there).
* `Work.PTGeometric.RegionManifoldTheoremOfIsCompactInterior` (the submersion hypothesis restricted to
  the interior zeros) is **false**: with only the tangency clause at the boundary zeros the region can
  have a `C²`-but-not-`C³` corner (e.g. `Φ (t, u) = -t + u₁³` on the half-space: every interior zero
  is regular, the tangential derivative vanishes at the boundary zeros so `hone` holds, but
  `{Φ ≤ 0} = {t ≥ max (0, u₁³)}` is not a smooth hypersurface).

The form below is the one that both holds and is satisfied by the explicit `Φ` of the diagnosis
(`Φ = a² θ - x₀ (C - ρ)`):

* the **weak** derivative condition `mfderiv Φ x ≠ 0` at every zero (no normal-form requirement), and
* at every boundary zero, `Φ ≥ 0` on the boundary **near** the point (the "sign/definiteness"
  condition that rules out the corner: it says that the level set `{Φ = 0}`, which is a graph
  `{x₀ = g (u)}` over the boundary by the weak condition plus the tangency, lies on the *interior*
  side, so that `{Φ ≤ 0} ∩ A = {x₀ ≥ g (u)}` is a smooth region), together with
* the tangency clause `hone`.

## What is *not* in this definition

The strong form `Work.PTGeometric.RegionManifoldTheoremOfIsCompact` also has a fifth conjunct,
transferring a submersion of a function `f : A → ℝᵏ` on `∂A` to the boundary `∂M`.  That conjunct
**cannot** hold in the weak setting: at a *boundary* zero of `Φ` the region is only *tangent* to
`∂A` (in a chart it is the epigraph `{t ≥ g (u)}` with `g ≥ 0`, `g (u₀) = 0`), so `∂M` near the
point is the hypersurface `{Φ = 0}`, which for `g (u) > 0` consists of *interior* points of `A`; a
function that is only smooth on `∂A` need not be smooth (or even continuous) there.  A concrete
counterexample was produced by a reviewer (`Φ x = (x 0)^3 - x 0 + Σ_{i ≠ 0} (x i)^2` on
`EuclideanHalfSpace 10`, `f x = x 1 + (if x 0 = 0 then 0 else 1)`).

Consequently the boundary-transfer conjunct is **not** part of the definition below; a consumer
that needs it must supply it as an explicit hypothesis, derived from the geometry of its situation
(for the source construction that is the normal coordinate of the tube at the pieces).

## Main definitions

* `Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

def RegionManifoldTheoremOfIsCompactWeak (k : ℕ) : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) A]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ A] [T2Space A] (Φ : A → ℝ),
    ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ Φ →
    (∀ x : A, Φ x = 0 →
      mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) Φ x ≠ 0) →
    (∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary A, Φ x = 0 →
      ∀ᶠ y in 𝓝 x, y ∈ (𝓡∂ ((8 + k) + 1)).boundary A → 0 ≤ Φ y) →
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
        IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ (fun y : M => f (e y)) m)

end

end Work.PTGeometric
