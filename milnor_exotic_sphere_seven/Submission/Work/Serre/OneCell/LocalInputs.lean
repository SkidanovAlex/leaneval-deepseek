import Mathlib
import Submission.Work.Serre.OneCell.RatMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Elementary inputs of the local model of the `1`-cell step

The local model compares the pair `(q⁻¹B, q⁻¹(B∖P))` with `(B, B∖P)` through the pair sequences; the
ingredients are the comparisons of the fibres with a point.  This file records the elementary part
of that comparison: in positive degrees `1 ≤ m ≤ N` both `H_m(F;ℚ)` and `H_m(pt;ℚ)` vanish, so the
map is an isomorphism; in degree `0` it is the statement that `H_0(F;ℚ) ≅ ℚ` makes the
"sum of coefficients" map an isomorphism.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

/-- In positive degrees `≤ N` the fibre-to-point map is an isomorphism, both sides being zero. -/
theorem isIso_fibreToPoint_pos {F : Type} [TopologicalSpace F] (N m : ℕ) (hm0 : 0 < m)
    (hmN : m ≤ N)
    (hacyc : ∀ k : ℕ, 0 < k → k ≤ N →
      IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of F)).homology k)) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of F) (TopCat.of PUnit)
        (TopCat.ofHom (ContinuousMap.const F PUnit.unit))) m) := by
  refine Work.StemsB.isIso_of_isZero_of_isZero ?_ ?_
  · exact hacyc m hm0 hmN
  · exact Work.Cohomology.homologyContractible_ring ℚ m hm0

end

end Work.Serre.OneCell
