import Mathlib
import Submission.Work.SSGRoute.SSGate.wiringClean
import Submission.Work.SSGRoute.SSGate.detectorGlue
import Submission.Work.SSGate.concentratedLevelDataGate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Assembly: the concentrated level data gives the rank-one brick of `C6`

This file contains the *wiring* which turns the single remaining construction of the whole `C6`
chain — the concentrated level-and-character data — into `Work.SSGRoute.PTdualControl.RankOneBrick`,
and hence (through the already proved
`Work.SSGRoute.PTdualControl.pt_sha2_core_clean_via_brick`) into `Work.SSGRoute.stage_global_lifting`.

The two ingredients are both already proved and `sorry`-free:

* `Work.SSGRoute.SSGate.levelCocycleDatum_of_concentrated` — the concentrated data (as a
  hypothesis `hconc`) plus the `μ`-detection of a Dirac gives `LevelCocycleDatum`;
* `Work.SSGRoute.SSGate.exists_coindDirac_apply_ne_zero` — a nonzero functional detects some
  Dirac, so no case split on the "invariant" case is needed;
* `Work.SSGRoute.C6Detector.rankOneBrick_of_datum_and_transport_general` — the canonical-ambient
  datum plus the ambient transport gives the brick;
* `Work.SSGRoute.C6Detector.detectorAlgClosedExt` — the ambient transport, proved.

So `Work.SSGRoute.SSGate.concentratedLevelDataGate` (the level construction) alone implies the
brick, for every base field `k`.
-/

namespace Work.SSGRoute.SSGate

open CategoryTheory SSGRoute.PTExt

/-- **The canonical-ambient level datum, from the concentrated level data.** -/
theorem levelDatumCanonical_of_concentrated (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [NumberField k] : Work.SSGRoute.C6Detector.LevelDatumCanonical p k := by
  intro K _ _ _ _ _ w q hwq hpq N _ hNI ζ hζ hNζ μ hμ
  obtain ⟨γ, hγ⟩ := Work.SSGRoute.SSGate.exists_coindDirac_apply_ne_zero p N w μ hμ
  exact Work.SSGRoute.SSGate.levelCocycleDatum_of_concentrated p k K (AlgebraicClosure K)
    w q hwq N hNI μ γ hγ
    (Work.SSGate.concentratedLevelDataGate p k K (AlgebraicClosure K) w q hwq hpq N hNI ζ hζ hNζ γ)

/-- **The rank-one brick of `C6`, from the concentrated level data.** -/
theorem rankOneBrick_of_concentrated (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] :
    Work.SSGRoute.PTdualControl.RankOneBrick p k Ω :=
  Work.SSGRoute.C6Detector.rankOneBrick_of_datum_and_transport_general p k K
    (levelDatumCanonical_of_concentrated p k)
    (detectorAlgClosedExt_holds' p k) Ω

end Work.SSGRoute.SSGate
