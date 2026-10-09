import Mathlib
import Submission.Work.SSGRoute.LevelInertiaProEll.Defs
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.NeukirchUchida.Local.DecompositionGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

namespace Work.SSGRoute.LevelInertiaProEll

open Submission.NeukirchUchida.Local

/-! ## The action on ideals agrees with the action on places

`Gal(L/K)` acts on the ideals of `𝓞 L` (pointwise, through the induced automorphism of `𝓞 L`) and
also on the finite places of `L` (via `placeSmul`, the image of the prime under the induced ring
automorphism).  The two actions agree at the level of the underlying ideals.  This is the only
"bookkeeping" input needed to identify the stabiliser of a valuation subring with the stabiliser
of the corresponding prime ideal. -/

/-- A Galois automorphism of `L` acts on `𝓞 L` by the restriction of the automorphism to the ring
of integers. -/
lemma smul_ringOfIntegers_eq_galRestrict {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (y : 𝓞 L) :
    (σ • y : 𝓞 L) = (galRestrict (𝓞 K) K L (𝓞 L) σ) y := by
  apply Subtype.ext
  show ((σ • y : 𝓞 L) : L) = (((galRestrict (𝓞 K) K L (𝓞 L) σ) y : 𝓞 L) : L)
  rw [show ((σ • y : 𝓞 L) : L) = σ • (y : L) from integralClosure.coe_smul σ y]
  rw [AlgEquiv.smul_def]
  exact (algebraMap_galRestrict_apply (𝓞 K) σ y).symm

/-- The action of `Gal(L/K)` on ideals of `𝓞 L` coincides with the action on places: the ideal
underlying `σ • P` is the ideal underlying `placeSmul σ P`. -/
lemma smul_asIdeal_eq_placeSmul_asIdeal {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (σ : L ≃ₐ[K] L) :
    σ • P.asIdeal = (placeSmul σ P).asIdeal := by
  rw [Ideal.pointwise_smul_def, placeSmul_asIdeal]
  congr 1
  apply RingHom.ext
  intro y
  exact smul_ringOfIntegers_eq_galRestrict σ y

theorem stabilizerValuationSubringAtPrime {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    MulAction.stabilizer (L ≃ₐ[K] L)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P) =
      MulAction.stabilizer (L ≃ₐ[K] L) P.asIdeal := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  -- The stabiliser of the valuation ring is the decomposition group of the place ...
  have h1 : (σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P) ↔
      σ ∈ decompositionSubgroup (K := K) P := by
    rw [← MulAction.mem_stabilizer_iff]
    exact mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup P σ
  -- ... and the decomposition group is the stabiliser of the underlying prime ideal.
  have h2 : (σ ∈ decompositionSubgroup (K := K) P) ↔ σ • P.asIdeal = P.asIdeal := by
    rw [mem_decompositionSubgroup]
    constructor
    · intro h
      rw [smul_asIdeal_eq_placeSmul_asIdeal P σ, h]
    · intro h
      exact IsDedekindDomain.HeightOneSpectrum.ext
        (by rw [← smul_asIdeal_eq_placeSmul_asIdeal P σ]; exact h)
  rw [h1, h2]

end Work.SSGRoute.LevelInertiaProEll
