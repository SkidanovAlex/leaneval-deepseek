import Mathlib
import Submission.Work.Thom.cappedAgreement
import Submission.Work.Milnor.CappedManifold
import Submission.Work.SignatureBordism.Obstruction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold Topology

/-!
# The global congruence implies the capped congruence, in the `p1Tangent'` vocabulary

`Submission/Work/Thom/smooth8.lean` (option F2 of `NOTES` §15.10) defines the dimension-`8`
signature theorem not as a statement about free classes `p₁`, `p₂` but as a statement about the
**tangent bundle**:

* `Work.Thom.ClosedOrientedSmooth8` — a closed oriented smooth `8`-manifold (the workspace's
  encoding: a charted space over `ℝ⁸` with a `C¹` structure, compact and connected, together with a
  generating fundamental class `c ∈ H₈`);
* `Work.Thom.ClosedOrientedSmooth8.p1`, `.p2` — **defined** as `Work.Thom.p1Tangent' 𝓘(ℝ,ℝ⁸) M`,
  `Work.Thom.p2Tangent' 𝓘(ℝ,ℝ⁸) M`;
* `Work.Thom.HirzebruchCongruence8` — the global statement `∀ M, 7 ∣ p₁(M)² − 4 σ(M)`.

The remaining gap of the project (`Work.Thom.CappedCongruenceTangent`, see
`Submission/Work/Thom/cappedAgreement.lean`) is the *same* divisibility statement, but for the
capped manifold `X = D(ξ) ∪_F D⁸` of `Submission/Work/Milnor/CappedManifold.lean`, and with
`p₁(TX)` read as the defined class `Work.Thom.p1Tangent' 𝓘(ℝ,ℝ⁸) X` rather than as the class
`Work.Milnor.cappedPontryaginClass` constructed by the delivered characteristic-classes chapter.

**This module closes that gap unconditionally**: the global statement *instantiates* at the capped
family, because the capped manifold is a compact connected `ℝ⁸`-charted smooth manifold
(`Work.Milnor.cappedChartedSpace`, `Work.Milnor.capped_isManifold`, `Work.Milnor.isCompact_capped`,
`Work.Milnor.isPathConnected_capped`), so it is a `ClosedOrientedSmooth8` as soon as a generator of
`H₈(X;ℤ)` is chosen — which is exactly the hypothesis of `CappedCongruenceTangent`.

Concretely, for `F : Mk (-2) → Sph⁸` a capping diffeomorphism and `c` a generator of `H₈(X;ℤ)`,

```
  M := { pt := X, c := c, c_generates := hc } : ClosedOrientedSmooth8
```

and `h M : 7 ∣ M.p1Sq - 4 * M.sigma` *is* the required divisibility, since
`M.p1 = p1Tangent' 𝓘(ℝ,ℝ⁸) X`, `M.p1Sq = p₁SqNumber (cappedSSet F hF) c (p1Tangent' … X)`,
`M.sigma = sigma 4 (cappedSSet F hF) c` and `M.sset = cappedSSet F hF` (`cappedSSet` is the
`abbrev` `TopCat.toSSet.obj (TopCat.of X)`, whence definitionally `M.sset`).  Nothing new has to be
proved about the capped manifold; the work is the bookkeeping that the four local instances above
are the ones the *goal statement* was elaborated with (that is what the `attribute [local instance]`
block is for; it is the same device as in `Submission/Work/Thom/cappedAgreement.lean`).
-/

namespace Work.Thom

section

attribute [local instance] Work.Milnor.cappedChartedSpace
attribute [local instance] Work.Milnor.capped_isManifold
attribute [local instance] Work.Milnor.isCompact_capped

/-- **The repaired global dimension-`8` congruence implies the capped one.**  If for every closed
oriented smooth `8`-manifold, with `p₁` the *tangent-bundle* class `Work.Thom.p1Tangent'`, one has
`7 ∣ p₁² − 4σ`, then for the capped `8`-manifold `X = D(ξ) ∪_F D⁸` and every generator `c` of
`H₈(X;ℤ)` one has the same divisibility — because `X`, with fundamental class `c`, *is* a closed
oriented smooth `8`-manifold in the sense of `Work.Thom.ClosedOrientedSmooth8`. -/
theorem cappedCongruenceTangent_of_hirzebruchCongruence8
    (h : Work.Thom.HirzebruchCongruence8) : Work.Thom.CappedCongruenceTangent := by
  intro F hF c hc
  letI : PathConnectedSpace (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    Work.Milnor.isPathConnected_capped F hF
  let M : ClosedOrientedSmooth8 :=
    { pt := Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF), c := c, c_generates := hc }
  simpa [M, ClosedOrientedSmooth8.congruence, ClosedOrientedSmooth8.p1Sq,
    ClosedOrientedSmooth8.sigma, ClosedOrientedSmooth8.p1] using h M

end

end Work.Thom
