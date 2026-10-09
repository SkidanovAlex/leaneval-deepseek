import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inverse Galois transform of a prime lies over the prime below

For a finite extension of number fields `K/k`, the Galois group `Gal(K/k) = (K ≃ₐ[k] K)` acts on
the nonzero primes `q` of `𝓞 K` by `q ↦ σ • q = Ideal.map (ringOfIntegersEquiv σ) q.asIdeal`
(`NK.GlobalCFT.Place.smulHeightOneSpectrum`).  This file records three elementary facts used
downstream (`Work.SSGRoute.Sha2Lib.kummer_conjugates_independent`):

* the contravariance `σ • (σ⁻¹ • q) = q`,
* a prime above a fixed prime of `k` stays above it, so `σ⁻¹ • q` lies over the prime below `q`,
* consequently, if `η • q ≠ q` then also `η⁻¹ • q ≠ q`.

The mathematical content is that `ringOfIntegersEquiv σ` is a ring automorphism of `𝓞 K` which
is `𝓞 k`-linear (`σ` is a `k`-algebra automorphism), so it permutes the primes above a fixed
prime of `𝓞 k`: contraction to `𝓞 k` is insensitive to it.
-/

namespace Work.SSGRoute.Sha2Lib

open scoped NumberField

noncomputable section

/-- The ring automorphism of `𝓞 K` induced by `σ : K ≃ₐ[k] K` is `𝓞 k`-linear, hence fixes the
image of `𝓞 k`. -/
lemma ringOfIntegersEquiv_algebraMap {k K : Type*} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] (σ : K ≃ₐ[k] K) (x : 𝓞 k) :
    NK.GlobalCFT.Place.ringOfIntegersEquiv σ (algebraMap (𝓞 k) (𝓞 K) x) =
      algebraMap (𝓞 k) (𝓞 K) x :=
  (NumberField.RingOfIntegers.mapAlgEquiv σ).commutes x

/-- **Pull back along a ring homomorphism fixed by a ring automorphism.**  If the ring
automorphism `g` of `S` fixes (pointwise) the image of `f : R →+* S`, then an ideal `I` of `S`
and its `g`-image have the same contraction to `R`. -/
lemma comap_map_eq_comap_of_comp_eq {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (g : S ≃+* S) (hgf : ∀ x, (g : S →+* S) (f x) = f x) (I : Ideal S) :
    Ideal.comap f (Ideal.map (g : S →+* S) I) = Ideal.comap f I := by
  refine Ideal.ext fun x => ?_
  rw [Ideal.mem_comap, Ideal.mem_comap,
    Ideal.mem_map_iff_of_surjective (g : S →+* S) (RingEquiv.surjective g)]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy' : y = f x := by
      have h1 : (g : S →+* S) y = (g : S →+* S) (f x) := hyx.trans (hgf x).symm
      exact RingEquiv.injective g h1
    rwa [hy'] at hy
  · intro hx
    exact ⟨f x, hx, hgf x⟩

/-- **The prime below a prime is unchanged by the Galois action.**  For `σ : K ≃ₐ[k] K` and a
nonzero prime `q` of `𝓞 K`, the prime `σ • q` has the same contraction to `𝓞 k` as `q`: both lie
over the same prime of the base field. -/
lemma under_smulHeightOneSpectrum {k K : Type*} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Ideal.under (𝓞 k) (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q).asIdeal =
      Ideal.under (𝓞 k) q.asIdeal := by
  rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal, Ideal.under_def, Ideal.under_def,
    ← Ideal.map_coe]
  exact comap_map_eq_comap_of_comp_eq (algebraMap (𝓞 k) (𝓞 K))
    (NK.GlobalCFT.Place.ringOfIntegersEquiv σ)
    (fun x => ringOfIntegersEquiv_algebraMap σ x) q.asIdeal

/-- The Galois action on the nonzero primes of `𝓞 K` is a group action: `σ • σ⁻¹ • q = q`. -/
lemma smulHeightOneSpectrum_inv_smul {k K : Type*} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    NK.GlobalCFT.Place.smulHeightOneSpectrum σ
        (NK.GlobalCFT.Place.smulHeightOneSpectrum σ⁻¹ q) = q := by
  have h : σ • (σ⁻¹ • NK.GlobalCFT.Place.ofFinite q) = NK.GlobalCFT.Place.ofFinite q :=
    smul_inv_smul σ _
  simpa only [NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj] using h

theorem smulHeightOneSpectrum_inv_liesOver (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (η : K ≃ₐ[k] K)
    (hη : NK.GlobalCFT.Place.smulHeightOneSpectrum η q ≠ q) :
    NK.GlobalCFT.Place.smulHeightOneSpectrum η⁻¹ q ≠ q ∧
    (NK.GlobalCFT.Place.smulHeightOneSpectrum η⁻¹ q).asIdeal.LiesOver
      (Ideal.under (NumberField.RingOfIntegers k) q.asIdeal) ∧
    NK.GlobalCFT.Place.smulHeightOneSpectrum η
      (NK.GlobalCFT.Place.smulHeightOneSpectrum η⁻¹ q) = q := by
  refine ⟨?_, ?_, smulHeightOneSpectrum_inv_smul η q⟩
  · intro h
    refine hη ?_
    calc NK.GlobalCFT.Place.smulHeightOneSpectrum η q
        = NK.GlobalCFT.Place.smulHeightOneSpectrum η
            (NK.GlobalCFT.Place.smulHeightOneSpectrum η⁻¹ q) := by rw [h]
      _ = q := smulHeightOneSpectrum_inv_smul η q
  · refine ⟨(under_smulHeightOneSpectrum η⁻¹ q).symm⟩

end

end Work.SSGRoute.Sha2Lib
