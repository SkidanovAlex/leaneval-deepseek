import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.Sha2Lib.isUnramifiedDetector_of_induced
import Submission.Work.SSGRoute.Sha2Lib.detector_of_submodule
import Submission.Work.SSGRoute.Sha2Lib.detectsAt_of_coeff_surjection
import Submission.Work.SSGRoute.Sha2Lib.unramifiedDetector_trivial
import Submission.Work.SSGRoute.detectAbove_pgroup
import Submission.Work.SSGRoute.rightDetect_of_sylow
import Submission.Work.Sha2Lib.inertiaDeg_cyclotomic_level
import Submission.Work.Sha2Lib.residueField_cyclotomic_generated
import Submission.Work.Sha2Lib.nkCyclotomicClosed
import Submission.Work.SSGRoute.Sha2Lib.unramifiedDetector_of_indNormal
import Submission.Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_of_rankOne
import Submission.Work.SSGRoute.PTdualControl.zetaAdjoinDescent
import Submission.Work.SSGRoute.PTdualControl.C6_of_rankOneBrick
import Submission.Work.Sha2Lib.rankOneBrickViaDatum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Sha2Lib.unramifiedDetectorProved`: node `C6` for every finite `p`-torsion module

The assembly of the unramified detector (node `C6`) from the on-disk reductions and the one
remaining arithmetic brick, `Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne` (the
detector for the permutation module `Ind_N^{Γ} 𝔽_p`):

* `PTdualControl.unramifiedDetector_of_rankOneBrick` — the packaged chain
  (`unramifiedDetector_of_mup` = the `ζ_p`-adjoin base change;
  `Sha2Lib.unramifiedDetector_of_indNormal` = the leaf assembly through the normal closure of the
  inertia at `q`; `Sha2Lib.unramifiedDetector_indNormal_of_rankOne` = the multi-generator descent
  from `W = 𝔽_p` to an arbitrary trivial `p`-torsion `N`-module), which consumes the rank-one brick
  as a single hypothesis `RankOneBrick p k Ω`;
* the brick itself, in the exact spelling of its node, supplied by `Sha2Lib.rankOneBrickViaDatum`,
  which reduces it (through the *proved* assembly
  `TatePoitouRoute.unramifiedDetector_rankOne_of_levelCocycleDatum`) to the single open `Prop`
  `Work.Sha2Lib.rankOneLevelDatumExists` — the level-cocycle datum for every nonzero
  `D_w`-equivariant functional on the coinduced permutation module
  (see `Sha2Lib/NOTE_rankOneLevelDatum_route.md`).

So this theorem has **exactly one** open input, `Work.Sha2Lib.rankOneLevelDatumExists`, and no
dependency on any intermediate *statement* file: the moment that `Prop` is proved, this file and
`Sha2Lib/unramifiedDetector.lean` become `sorry`-free.
-/

open scoped IntermediateField

namespace Work.Sha2Lib

theorem unramifiedDetectorProved (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M := by
  classical
  refine Work.SSGRoute.PTdualControl.unramifiedDetector_of_rankOneBrick p k Ω ?_ K w q hwq hpq
    M hM hI
  intro K' _ _ _ _ _ _ _ w' q' hwq' hpq' N hN hNI ζ hζ hNζ
  haveI : N.Normal := hN
  exact Work.Sha2Lib.rankOneBrickViaDatum p k K' Ω w' q' hwq' hpq' N hNI ζ hζ hNζ

end Work.Sha2Lib
