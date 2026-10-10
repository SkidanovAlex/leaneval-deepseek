import Mathlib.GroupTheory.Nilpotent
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Induced
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.TatePoitouRoute.rankOneBrick_of_levelCocycleDatum
import Submission.Work.Sha2Lib.rankOneLevelDatumExists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rank-one brick from the level-cocycle datum, in the node's exact spelling

`Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne` is the last arithmetic brick of the
`C6` chain: the detector for the permutation module `Ind_N^Γ 𝔽_p`, for `N ⊴ Γ = Gal(K/k)`
containing the inertia at `q ∤ p` and fixing `ζ : K` with `IsPrimitiveRoot ζ p`.

The lane has reduced it (by proved reductions only) to a **single** `Prop`,
`Work.Sha2Lib.rankOneLevelDatumExists`: the level-cocycle datum for every nonzero `D_w`-equivariant
functional on the coinduced permutation module.  The chain is

* `Sha2Lib.rankOne_functionalDetection_of_levelCocycleDatum` (proved) — datum ⟹ `DetectsAt` at `δμ`;
* `E7cOmega.functional_of_ext_nonzero` (proved) — every nonzero `φ` is such a `δμ`;
* `Sha2Lib.rankOne_isUnramifiedDetector_of_coind` (proved) — the induced and coinduced models agree;

all packaged in `Work.SSGRoute.TatePoitouRoute.unramifiedDetector_rankOne_of_levelCocycleDatum`
(proved, `sorry`-free).

This file applies that package to the single open datum, so that the node's exact statement is
available with `rankOneLevelDatumExists` as its *only* open input — i.e. it removes the dependency
on any intermediate statement file: the moment `rankOneLevelDatumExists` is proved, this lemma (and
therefore `Sha2Lib.unramifiedDetectorProved`, which consumes it) is `sorry`-free.
-/

namespace Work.Sha2Lib

open CategoryTheory SSGRoute.PTExt

/-- **The rank-one brick of `C6`, from the level-cocycle datum.** -/
theorem rankOneBrickViaDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq
      (Rep.ind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) :=
  Work.SSGRoute.TatePoitouRoute.unramifiedDetector_rankOne_of_levelCocycleDatum p k K Ω w q hwq N
    (fun μ hμ => rankOneLevelDatumExists p k K Ω w q hwq hpq N hNI ζ hζ hNζ μ hμ)

end Work.Sha2Lib
