import Mathlib
import Submission.Work.PTGeometric.RegionManifoldNC

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the defining function of the source region — the *repaired* statement

`Submission/Work/PTGeometric/SourceRegionPhiFn_false.lean` (module
`Submission.Work.PTGeometric.sourceRegionPhiFn_false`) proves, sorry-free, that the original
interface `Work.PTGeometric.SourceRegionPhiProp` is **FALSE** as soon as the set `Z` meets the
boundary `∂A = {x | x.1 0 = 0}` of the half-space: Mathlib's `Manifold.IsSubmersionAt` at a
*boundary* point is the local-normal-form notion, which forces the zero set of `Φ` to contain the
boundary near that point; combined with the tangency clause (`hone`: `dΦ = c • d(boundary
coordinate)`, `c < 0`) it forces `Φ ≤ 0` on a whole relative neighbourhood of every boundary zero;
the set of boundary zeros is then clopen in the connected `∂A ≅ ℝ^{k+8}`, and `{Φ ≤ 0}` is unbounded
— contradicting compactness.  See `Submission/Work/PTGeometric/exists_sourceRegionPhi_DIAGNOSIS.md`.

The repair — which is the statement below — is to ask for the submersivity only at the **interior**
zeros of `Φ`.  Then the interface is satisfiable, and the explicit construction of the diagnosis
works:

  `Φ x := a (tail (k+8) (srcCast k x.1)) ^ 2 * θ (x.1 0) - x.1 0 * (C (x.1 0) - ρ x)`,

with `a` a Urysohn function of the core tail `B` (`Work.PTGeometric.exists_coreDefiningFunction`),
`ρ` a defining function of `Z` saturated against the closed set to be avoided
(`Work.PTGeometric.exists_sourceDefiningFunction` with `T := H ⁻¹' {t₀}`), `θ t = (1 + t ^ 2) ^ (-8)`
and `C t = 1 / 2 + t ^ 2 / (4 * (1 + t ^ 2))`; at the boundary zeros the tangential derivative of `Φ`
vanishes (because `a = 0` there) while the normal derivative is `-1 / 2 < 0`, which is exactly the
`hone` clause, and at the interior zeros the normal derivative is strictly negative.

The statement below therefore takes the set `T` to be avoided (rather than an arbitrary open `U`),
which is exactly what the construction delivers: `{Φ ≤ 0} ⊆ {ρ ≤ 3 / 4}` and `ρ ≥ 1` on `T`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **The repaired defining-function interface of the source region.**  Compared with the false
`Work.PTGeometric.SourceRegionPhiProp`, the submersivity is asked for only at the *interior* zeros,
and the "avoided set" `T` replaces the prescribed open `U`. -/
def SourceRegionPhiInterior (k : ℕ) (Z T : Set (EuclideanHalfSpace ((8 + k) + 1))) : Prop :=
  ∃ Φ : EuclideanHalfSpace ((8 + k) + 1) → ℝ,
    ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
    Z ⊆ {x | Φ x ≤ 0} ∧
    ({x | Φ x ≤ 0} ∩ T) = ∅ ∧
    IsCompact {x | Φ x ≤ 0} ∧
    (Z ∩ {x | Φ x = 0} ⊆ {x | x.1 0 = 0}) ∧
    (∀ x : EuclideanHalfSpace ((8 + k) + 1), Φ x = 0 → x.1 0 ≠ 0 →
      IsSubmersionAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ x) ∧
    (∀ x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
        (EuclideanHalfSpace ((8 + k) + 1)), Φ x = 0 →
      ∃ (e : OpenPartialHomeomorph (EuclideanHalfSpace ((8 + k) + 1))
            (EuclideanHalfSpace ((8 + k) + 1))) (c : ℝ),
        e ∈ IsManifold.maximalAtlas (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
              ((⊤ : ℕ∞) : WithTop ℕ∞) (EuclideanHalfSpace ((8 + k) + 1)) ∧
        x ∈ e.source ∧ c < 0 ∧
        (∀ y ∈ e.source, (e y).1 0 = 0 ↔
          y ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
            (EuclideanHalfSpace ((8 + k) + 1))) ∧
        mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
            (modelWithCornersSelf ℝ ℝ) Φ x
          = c • mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
              (modelWithCornersSelf ℝ ℝ)
              (fun y : EuclideanHalfSpace ((8 + k) + 1) => (e y).1 0) x)

end

end Work.PTGeometric
