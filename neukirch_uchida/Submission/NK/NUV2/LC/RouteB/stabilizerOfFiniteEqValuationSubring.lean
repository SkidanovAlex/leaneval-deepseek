import Mathlib
import Submission.NK.GlobalCFT.GaloisAction
import Submission.NK.GlobalCFT.Galois.globalCFT_exists_localRingEquiv_smul
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective

namespace NK.NUV2.LC.RouteB

open scoped Pointwise NumberField

open NK.GlobalCFT IsDedekindDomain

/-- **The valuation ring of `σ • 𝔮` is the `σ`-image of the valuation ring of `𝔮`.**

For a number field `L`, an automorphism `σ` of `L` over any base field `K ⊆ L` and a nonzero prime
`𝔮` of `𝓞 L`, the image of the valuation subring `𝒪_{L,𝔮}` under the pointwise action of `σ` is
the valuation subring of the image prime `σ • 𝔮 = smulHeightOneSpectrum σ 𝔮`.

Indeed, by definition of the pointwise action `x ∈ σ • 𝒪_{L,𝔮} ↔ σ⁻¹ x ∈ 𝒪_{L,𝔮}`, and the
valuation at `σ • 𝔮` of `x` is the valuation at `𝔮` of `σ⁻¹ x`
(`NK.GlobalCFT.Galois.globalCFT_valuation_smulHeightOneSpectrum`), so membership becomes the
same inequality `≤ 1`. -/
theorem smul_valuationSubringAtPrime {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L q =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L
        (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q) := by
  -- The two valuations compared at `x` and at `σ⁻¹ x` agree.
  have hval : ∀ x : L, (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q).valuation L x =
      q.valuation L (σ⁻¹ • x) := by
    intro x
    have h := NK.GlobalCFT.Galois.globalCFT_valuation_smulHeightOneSpectrum (K := K) σ q
      (σ⁻¹ • x)
    simpa using h
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff, hval x]

/-- **The stabiliser of a finite place is the stabiliser of its valuation ring.**  For a number
field `L` and any base field `K` under it, the `Gal(L/K)`-stabiliser of the finite place
`Place.ofFinite q` (the prime `q` of `𝓞 L`) is the stabiliser of the corresponding valuation
subring `𝒪_{L,q} = valuationSubringAtPrime L q`. -/
theorem stabilizerOfFiniteEqValuationSubring {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    MulAction.stabilizer (L ≃ₐ[K] L) (NK.GlobalCFT.Place.ofFinite q) =
      MulAction.stabilizer (L ≃ₐ[K] L)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L q) := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · -- A stabiliser of the place fixes the underlying prime, hence also the valuation ring.
    intro h
    rw [NK.GlobalCFT.Place.smul_ofFinite] at h
    have hq : NK.GlobalCFT.Place.smulHeightOneSpectrum σ q = q :=
      (NK.GlobalCFT.Place.ofFinite_inj).mp h
    rw [smul_valuationSubringAtPrime, hq]
  · -- Conversely a stabiliser of the valuation ring fixes the place, since the map
    -- `q ↦ 𝒪_{L,q}` is injective.
    intro h
    have h1 : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L
        (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L q := by
      rw [← smul_valuationSubringAtPrime, h]
    have hq : NK.GlobalCFT.Place.smulHeightOneSpectrum σ q = q :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
        (R := NumberField.RingOfIntegers L) (K := L) h1
    rw [NK.GlobalCFT.Place.smul_ofFinite, hq]

end NK.NUV2.LC.RouteB
