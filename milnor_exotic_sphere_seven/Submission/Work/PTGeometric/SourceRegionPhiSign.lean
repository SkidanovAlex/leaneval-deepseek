import Mathlib
import Submission.Work.PTGeometric.SourceRegionPhiInterior

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the defining function of the source region, with the boundary sign clause

`Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak` (the corrected region-charting theorem)
needs, besides the clauses of `Work.PTGeometric.SourceRegionPhiInterior`, the **sign condition**

  at every boundary zero `x` of `Φ`, `Φ ≥ 0` on the boundary near `x`

(the condition that rules out the `C²`-but-not-`C³` corner of the refuted
`RegionManifoldTheoremOfIsCompactInterior`).  The explicit `Φ` of
`Submission/Work/PTGeometric/exists_sourceRegionPhi_DIAGNOSIS.md` satisfies it trivially: on the
boundary `x 0 = 0` it equals `a (tail x) ^ 2 ≥ 0` (`a` the Urysohn function of the core tail).

This file records the strengthened interface as `Work.PTGeometric.SourceRegionPhiInteriorSign`.

## Main definitions

* `Work.PTGeometric.SourceRegionPhiInteriorSign`
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **The defining function of the source region, with the boundary sign clause.**  Clauses (1)–(7)
are those of `Work.PTGeometric.SourceRegionPhiInterior`; clause (8) is the sign condition needed by
`Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak`. -/
def SourceRegionPhiInteriorSign (k : ℕ) (Z T : Set (EuclideanHalfSpace ((8 + k) + 1))) : Prop :=
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
              (fun y : EuclideanHalfSpace ((8 + k) + 1) => (e y).1 0) x) ∧
    (∀ x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
        (EuclideanHalfSpace ((8 + k) + 1)), Φ x = 0 →
      ∀ᶠ y in 𝓝 x, y ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
        (EuclideanHalfSpace ((8 + k) + 1)) → 0 ≤ Φ y)

end

end Work.PTGeometric
