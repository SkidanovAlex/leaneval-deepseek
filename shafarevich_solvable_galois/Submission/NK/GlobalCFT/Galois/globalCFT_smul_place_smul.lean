import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT NumberField IsDedekindDomain

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The isomorphism `𝓞 L ≃ₐ[𝓞 K] 𝓞 L` induced by `σ` is multiplicative: restricting
`σ' * σ` to the ring of integers is the composite of the restrictions of `σ'` and `σ`. -/
lemma ringOfIntegersEquiv_mul_comp (σ σ' : L ≃ₐ[K] L) :
    (RingHom.comp (Place.ringOfIntegersEquiv σ' : 𝓞 L →+* 𝓞 L)
        (Place.ringOfIntegersEquiv σ : 𝓞 L →+* 𝓞 L)) =
      (Place.ringOfIntegersEquiv (σ' * σ) : 𝓞 L →+* 𝓞 L) := by
  ext x
  change ((Place.ringOfIntegersEquiv σ' (Place.ringOfIntegersEquiv σ x) : 𝓞 L) : L) =
    ((Place.ringOfIntegersEquiv (σ' * σ) x : 𝓞 L) : L)
  rw [Place.ringOfIntegersEquiv_apply, Place.ringOfIntegersEquiv_apply,
    Place.ringOfIntegersEquiv_apply, AlgEquiv.mul_apply]

/-- The action of `Gal(L/K)` on the nonarchimedean places of `L` is compatible with the group
structure: the prime `(σ' * σ) 𝔮` is the prime `σ' (σ 𝔮)`. -/
lemma smulHeightOneSpectrum_mul (σ σ' : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L)) :
    Place.smulHeightOneSpectrum σ' (Place.smulHeightOneSpectrum σ q) =
      Place.smulHeightOneSpectrum (σ' * σ) q := by
  apply HeightOneSpectrum.ext
  simp only [Place.smulHeightOneSpectrum_asIdeal]
  apply (Ideal.map_map (f := (Place.ringOfIntegersEquiv σ : 𝓞 L →+* 𝓞 L))
    (g := (Place.ringOfIntegersEquiv σ' : 𝓞 L →+* 𝓞 L)) (I := q.asIdeal)).trans
  rw [ringOfIntegersEquiv_mul_comp]
  rfl

theorem globalCFT_smul_place_smul {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ σ' : L ≃ₐ[K] L) (v : NK.GlobalCFT.Place L) :
    σ' • (σ • v) = (σ' * σ) • v := by
  cases v with
  | inl w =>
      simp only [Place.smul_ofInfinite]
      rw [mul_smul]
  | inr q =>
      simp only [Place.smul_ofFinite]
      rw [Place.ofFinite_inj]
      exact smulHeightOneSpectrum_mul σ σ' q

end NK.GlobalCFT.Galois
