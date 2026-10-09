import Mathlib
import Submission.Work.SSGcrux.rankOneBrick_ssg
import Submission.Work.SSGRoute.PTdualControl.C6_of_rankOneBrick
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unramified detector (node `C6`), proved from the rank-one brick

`Work.SSGcrux.rankOneBrick_ssg` proves the rank-one brick of `C6` (the detector for the permutation
module `Ind_N^Γ 𝔽_p`) from `Work.SSGcrux.noninvariantLevelDatum`, which in turn consumes the
concentrated level data `Work.SSGcrux.concentratedLevelData`.  This module is the one-line
consumer: the node `C6` in the exact spelling in which the E7cΩ assembly uses it.

It is axiom-clean (`[propext, Classical.choice, Quot.sound]`). -/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute

/-- **Node `C6`** (`Work.Sha2Lib.unramifiedDetector`): every nonzero
`φ ∈ Ext¹_{D_w}(res M, ℤ)` is detected at some level, for any finite `p`-torsion `Gal(K/k)`-module
`M` on which the inertia at `q` acts trivially. -/
theorem unramifiedDetector_closed (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M :=
  Work.SSGRoute.PTdualControl.unramifiedDetector_of_rankOneBrick p k Ω
    (Work.SSGcrux.rankOneBrick_ssg p k Ω) K w q hwq hpq M hM hI

end Work.SSGRoute
