/-
# `BridgeSquare/FinalInputsP.lean` — the final wiring from properties of the Mayer–Vietoris map

`Work.Final.FinalInputs` hard-codes the bridge square `hsq` with the concrete matrix
`Work.HomologyMV.wConcrete`.  `Submission/Work/NOTES_LEAD_aspherical_bridge.md` §1.2 observes that
**nothing downstream reads the entries of `wConcrete`**: the only consumer is
`Work.HomologyMV.mv_homology`, which works for an *arbitrary* model map `w` and uses only

* `SurjCert w` — `w k` surjective for `k ≥ 1`, and
* `KernelCert w` — `ker (w k) ≃ kerModel k` for `k ≥ 0`,

both of which are invariant under isomorphism of the source and the target.  Hence the whole bridge
reduces to **properties of the actual Mayer–Vietoris map** `L.d (k, 0)`:

| degree | needed |
|---|---|
| `0` | injective |
| `1, 2` | surjective (hence bijective: ranks `15 = 15`) |
| `3` | surjective (hence kernel `≃ ℤ`: ranks `5 → 4`) |
| `≥ 4` | trivial (`rankM = rankN = 0`) |

and the square can be satisfied *by construction*, for **any** identifications — including the
delivered opaque ones (`Work.HomologyMV.mv_homology_of_props`,
`Work.HomologyMV.intHomology_of_props`).  This file provides the corresponding final wiring:

* `Work.Final.FinalInputsP` — `FinalInputs` with `hsq` replaced by `hsurj` and `hker`;
* `Work.Final.Mhat4P`, `Work.Final.isAspherical_Mhat4P` — the asphericity (probe P1: the body of
  `isAspherical_Mhat4` reads only `rt`, `cov_smooth`, `curvLe`);
* `Work.Final.h0_of_hX` (in namespace `Work.Final.FinalInputsP`);
* the two remaining theorems (`isIntegerHomologySphere_Mhat4P`,
  `aspherical_integer_homology_four_sphere_P`) are in `FinalInputsPChallenge.lean`, once the
  consumer `Work.HomologyMV.intHomology_of_props` has landed.

`Work.Final.FinalInputs` and `Work.FinalWire` are left untouched: this is additive.
-/
import Submission.Work.Final.Framework
import Submission.Work.Final.Basic
import Submission.Work.Final.Mhat
import Submission.Work.Final.Homology
import Submission.Work.Final.Cover
import Submission.Work.Final.MhatCover
import Submission.Work.Final.Main
import Submission.Work.Final.mvRightX_zero_surjective
import Submission.Work.Final.secNonpos_of_chartModels
import Submission.Work.Final.curvLe_of_models
import Submission.Work.Final.CurvField
import Submission.Work.BridgeSquare.Spaces

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.defProp false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

open LeanEval.Topology
open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Work.Final

open Work.Space

noncomputable section

/-- **`Work.Final.FinalInputs` with the bridge square replaced by the two properties of the
Mayer–Vietoris map.**  The identifications `eM`, `eN` are now only *existential* (any isos will do,
since the consumer `Work.HomologyMV.intHomology_of_props` builds the square from them by
construction); `hsurj` and `hker` are statements about the actual map `L.d (k, 0)`, invariant under
those isos. -/
class FinalInputsP where
  /-- The assembled Ratcliffe–Tschantz space `M̂`. -/
  [rt : Work.Space.RTData]
  /-- The smoothness of the Levi-Civita connection. -/
  [cov_smooth : CovariantDerivative.ContMDiffCovariantDerivative (mhatCov (rt := rt)) ∞]
  /-- The curvature bound, in the parametric form consumed by Cartan–Hadamard. -/
  curvLe : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (mhatCov (rt := rt)) K
  /-- The Mayer–Vietoris long exact sequence of the cover `M̂ = A ∪ B`. -/
  L : Work.HomologyMV.MVLES
  /-- `H_k(A ∩ B)` is the free model `ℤ^{rankM k}` (existence of an identification is enough). -/
  eM : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelM k ≅ L.H (k, 0))
  /-- `H_k(A) ⊞ H_k(B)` is the free model `ℤ^{rankN k}`. -/
  eN : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelN k ≅ L.H (k, 1))
  /-- **The first Mayer–Vietoris map is surjective in degrees `≥ 1`.** -/
  hsurj : ∀ k : ℤ, 1 ≤ k → Function.Surjective (L.d (k, 0)).hom
  /-- **The kernel of the first Mayer–Vietoris map is `kerModel k` in degrees `≥ 0`.** -/
  hker : ∀ k : ℤ, 0 ≤ k → Nonempty ((L.d (k, 0)).hom.ker ≃ₗ[ℤ] ↥(Work.HomologyMV.kerModel k))
  /-- The `X`-slot of the sequence is the singular homology of `M̂`. -/
  hX : ∀ k : ℕ, L.H ((k : ℤ), 2) ≅
    LeanEval.Topology.intHomology k (TopCat.of rt.Mhat)

namespace FinalInputsP

/-- The space `M̂` of the final input. -/
abbrev Mhat (D : FinalInputsP) : Type _ := D.rt.Mhat

/-- The smoothness of the connection of the final chain. -/
theorem mhatCov_contMDiff [D : FinalInputsP] :
    CovariantDerivative.ContMDiffCovariantDerivative (mhatCov (rt := D.rt)) ∞ :=
  D.cov_smooth

/-- **`M̂` is path connected** — from the smooth chart structure of the assembled space and its
connectedness (the same argument as `Work.Final.pathConnectedSpace_Mhat`). -/
theorem pathConnectedSpace_Mhat [D : FinalInputsP] : PathConnectedSpace D.Mhat := by
  haveI : LocallyPathConnectedSpace D.Mhat :=
    ChartedSpace.locallyPathConnectedSpace Work.Space.E4 D.Mhat
  exact PathConnectedSpace.of_locallyPathConnectedSpace

instance instPathConnectedSpaceMhat [D : FinalInputsP] : PathConnectedSpace D.Mhat :=
  pathConnectedSpace_Mhat (D := D)

/-- **`H_0(M̂; ℤ) ≅ ℤ`.** -/
theorem intHomology_zero_Mhat [D : FinalInputsP] :
    Nonempty (LeanEval.Topology.intHomology 0 (TopCat.of D.Mhat) ≅ ModuleCat.of ℤ ℤ) :=
  ⟨Work.Homology.singHomologyZeroIsoOfPathConnected Work.Homology.ZMod (TopCat.of D.Mhat)⟩

/-- **The degree-`0` input of the Mayer–Vietoris computation**, derived from `hX`. -/
theorem h0_of_hX [D : FinalInputsP] : Nonempty (D.L.H (0, 2) ≅ Work.HomologyMV.Sol 0) :=
  ⟨(D.hX 0) ≪≫ (intHomology_zero_Mhat (D := D)).some⟩

end FinalInputsP

/-- **The manifold `M̂` of the `P` wiring.** -/
def Mhat4P [D : FinalInputsP] : Closed4Manifold :=
  { carrier := D.rt.Mhat }

/-- **`M̂` is aspherical.**  (Probe P1 of `NOTES_LEAD_aspherical_bridge.md`: the body of
`Work.Final.isAspherical_Mhat4` reads only `rt`, `cov_smooth` and `curvLe`, so it transfers
verbatim.) -/
theorem isAspherical_Mhat4P [D : FinalInputsP] : (Mhat4P (D := D)).IsAspherical := by
  haveI := D.mhatCov_contMDiff
  exact Work.CartanHadamard.aspherical_of_curvLe
    (E := E4) (H := E4) (I := I4) (M := D.rt.Mhat)
    (cov := mhatCov (rt := D.rt))
    (hmet := Work.LeviCivita.lcConn_compat)
    (htor := Work.LeviCivita.lcConn_torsion)
    D.curvLe

end

end Work.Final
