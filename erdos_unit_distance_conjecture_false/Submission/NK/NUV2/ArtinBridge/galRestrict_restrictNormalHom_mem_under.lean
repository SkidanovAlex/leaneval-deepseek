import Mathlib
import Submission.NeukirchUchida.Local.Restriction

namespace NK.NUV2.ArtinBridge

/-- The restriction to a normal intermediate field of a `K`-automorphism of `L` acting trivially modulo a prime `q` of `L` acts trivially modulo the prime `q ∩ F` below it: the inertia subgroup of `Gal(L/K)` at `q` maps into the inertia subgroup of `Gal(F/K)` at `q ∩ F`. -/
theorem galRestrict_restrictNormalHom_mem_under {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (F : IntermediateField K L) [Normal K ↥F] [FiniteDimensional K ↥F] [NumberField ↥F]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (σ : L ≃ₐ[K] L)
    (hσ : ∀ x : NumberField.RingOfIntegers L,
      galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ x - x
        ∈ q.asIdeal) :
    ∀ y : NumberField.RingOfIntegers ↥F,
      galRestrict (NumberField.RingOfIntegers K) K ↥F (NumberField.RingOfIntegers ↥F)
          (AlgEquiv.restrictNormalHom F σ) y - y
        ∈ q.asIdeal.under (NumberField.RingOfIntegers ↥F) := by
  intro y
  rw [Ideal.mem_under, map_sub]
  rw [Submission.NeukirchUchida.Local.galRestrict_restrictNormalHom F σ y]
  exact hσ (algebraMap (NumberField.RingOfIntegers ↥F) (NumberField.RingOfIntegers L) y)

end NK.NUV2.ArtinBridge
