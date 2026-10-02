import Mathlib
import Submission.Work.Agree.Basic
import Submission.Work.Agree.crux
import Submission.Work.Agree.geometryB
import Submission.Work.Agree.geomSplitting
import Submission.Work.Agree.endgame
import Submission.Work.Agree.shiftToRankTwo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! Guidance from the project lead (the requester):

AREA AGREE. Prove `Work.Drive.AgreeAll`: for the capped manifold X = D(ξ) ∪_F D⁸ (any capping datum F, hF),
the Chern-defined class `Work.Thom.p1Tangent' 𝓘(ℝ,ℝ⁸) X` (= −c₂(TX ⊗ ℂ), Submission/Work/Thom/manifoldP1.lean)
equals ± `Work.Milnor.cappedPontryaginClass F hF` (the unique class of H⁴(X;ℤ) ≅ ℤ restricting to 6·τ).
Read Submission/Work/Thom/cappedAgreement.lean, TangentClasses/README.md (DiscSplitting, p1Tangent F hF S,
p1Tangent_eq_cappedPontryaginClass) and Thom/README.md ADDENDA 20-24.

The reduction of this statement to the mathematical content is in `Submission/Work/Agree/Basic.lean`:
`Work.Agree.DiscRestriction` (the restriction of `p1Tangent'` to the disc bundle is `± 6·τ`) implies the
target (`Work.Agree.agreeAll_of_discRestriction`).  The remaining work is the geometric/computational
content of `DiscRestriction`; see `Submission/Work/Agree/ROADMAP.md`.
-/

open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false

namespace Work.Agree

noncomputable section

/-- **AREA AGREE**: for the capped manifold `X = D(ξ) ∪_F D⁸`, the Chern-defined class
`p₁(TX) = Work.Thom.p1Tangent'` is `± Work.Milnor.cappedPontryaginClass F hF`. -/
theorem agreeAll : Work.Drive.AgreeAll :=
  -- The *geometric/plumbing* half is PROVED (`Work.Agree.geomSplitting` on top of
  -- `Work.Agree.geometryB`), so the only remaining input is the characteristic-class half
  -- `Work.Agree.Crux`.
  --
  -- `Submission/Work/Agree/endgame.lean` decomposes `Crux` into exactly TWO bricks, both
  -- deliverables of subprojects:
  --   * `Work.Agree.EulerClutch`   -- transgression subproject `Submission/Work/Transgression/`;
  --   * the degree-2 Whitney formula for rank-2 complex bundles over `S⁴` -- subproject
  --     `Submission/Work/Whitney/`.
  -- Everything else of AREA AGREE is PROVED: the geometry (`geomSplitting geometryB`), the
  -- Thom-class transport lemma (`eulerClassIso`), and the shift isomorphism `ℂ(L^aR^b) ≅ ℂ(L^{a-b})`
  -- (`clutchShift`, exposed as `ComplexificationShift`).  Concretely:
  -- `Work.Agree.agreeAll_of_crux_geom (Work.Agree.crux_of_two_bricks hE hW)
  -- (Work.Agree.geomSplitting Work.Agree.geometryB)`.
  Work.Agree.agreeAll_of_crux_geom
    (Work.Agree.crux_of_rankTwoShift
      (Work.Agree.rankTwoShift_of_cLine Work.Agree.shiftToRankTwo))
    (Work.Agree.geomSplitting Work.Agree.geometryB)

end

end Work.Agree
