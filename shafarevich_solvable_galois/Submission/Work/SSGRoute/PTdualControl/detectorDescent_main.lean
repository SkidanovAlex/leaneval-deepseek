import Mathlib
import Submission.Work.SSGRoute.PTdualControl.detectorDescent
import Submission.Work.SSGRoute.PTdualControl.detectorDescent_algebra
import Submission.Work.SSGRoute.PTdualControl.place_ramification_descent
import Submission.Work.SSGRoute.PTdualControl.baseChange_detectsAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unramified detector `C6` descends along `k ⊆ K ⊆ K'` with `p ∤ [K' : K]`

The `∀ φ ≠ 0` form of `Work.SSGRoute.PTdualControl.baseChange_detectsAt`
(`Submission/Work/SSGRoute/PTdualControl/baseChange_detectsAt.lean`).  Applied with
`K' = K(ζ_p)` — for which `[K' : K] ∣ p - 1`, hence `p ∤ [K' : K]` — this reduces the general node
`Work.Sha2Lib.unramifiedDetector` to its `μ_p ⊆ K` case, which is the shape the arithmetic lanes
(`SSGRoute/E7cC`, `Sha2Lib`) produce.
-/

namespace Work.SSGRoute.PTdualControl

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

section Detector

/-- **The base-change descent for the unramified detector, at the level of the detector.**

The `∀ φ ≠ 0` form of `Work.SSGRoute.PTdualControl.baseChange_detectsAt`: if the unramified
detector holds for `K'/k` at `w'` with the module `res_{K'/K} M` (and `p ∤ [K' : K]`, `w' | w`),
then it holds for `K/k` at `w` with `M`.  Applied with `K' = K(ζ_p)` this is what reduces the
general node `C6` to its `μ_p ⊆ K` case. -/
theorem IsUnramifiedDetector.of_baseChange (p : ℕ) [Fact p.Prime]
    (k K K' Ω : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field K'] [NumberField K']
    [Field Ω] [IsAlgClosed Ω]
    [Algebra k K] [Algebra k K'] [Algebra k Ω] [Algebra K K'] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower k K K'] [IsScalarTower k K Ω] [IsScalarTower k K' Ω] [IsScalarTower K K' Ω]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k K'] [IsGalois k K']
    [FiniteDimensional K K'] [IsGalois K K']
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (w' : NK.GlobalCFT.Place K')
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K'))
    (hwq' : w' = NK.GlobalCFT.Place.ofFinite q')
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (hp : ¬ p ∣ Module.finrank K K')
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (hdet : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K' Ω w' q' hwq'
      (Rep.res (galRes k K K') M)) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M :=
  fun φ hφ => baseChange_detectsAt p k K K' Ω w q hwq w' q' hwq' hw' hp M hM hdet φ hφ

end Detector

end Work.SSGRoute.PTdualControl
