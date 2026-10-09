import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.smulHeightOneSpectrum_inv_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead design (Claude) 10-05 10:50 (_lead_design/flags_1030/NOTE.md §2): copy the proved one-level Sha2Lib.under_smulHeightOneSpectrum, then restrictNormal_commutes + Ideal.map_comap_of_equiv (about 40 lines). [Normal k K] and the ringOfIntegersEquiv→+* coercion are pinned in the statement. Consumer: H7 (block↔place step, with the proved comap_algebraMap_smul_fixingSubgroup).

# The prime below a Galois conjugate of a prime, in a tower

For a tower of number fields `k ⊆ K ⊆ L` with `K/k` normal, the Galois group
`Gal(L/k) = (L ≃ₐ[k] L)` acts on the nonzero primes of `𝓞 L` by `Q ↦ σ • Q`
(`NK.GlobalCFT.Place.smulHeightOneSpectrum`).  This file proves that the contraction to `𝓞 K` is
compatible with this action: the prime below `σ • Q` is the `σ|_K`-image of the prime below `Q`.

The two ingredients are, on the one hand, the commutation `σ_L ∘ f = f ∘ σ_K` of the induced ring
maps of the rings of integers -- an instance of `AlgEquiv.restrictNormal_commutes` -- and, on the
other, the elementary fact about ideals that an automorphism `g` of `S` which commutes with a ring
map `f : R →+* S` along an automorphism `g'` of `R` transports `comap f` into `comap f`
(`comap_map_eq_map_comap_of_comp_eq`).
-/

namespace Work.SSGRoute.Sha2Lib

open scoped NumberField

/-- **Transport of a contraction along a commuting square of rings.**  Let `f : R →+* S` be a ring
homomorphism, `g` a ring automorphism of `S`, `g'` a ring automorphism of `R` such that
`g (f x) = f (g' x)` for all `x : R`.  Then for any ideal `I` of `S`, pulling back the `g`-image of
`I` along `f` is the `g'`-image of the pullback of `I`:

`comap f (map g I) = map g' (comap f I)`.

Both sides are obtained from the identity `map g I = comap g⁻¹ I` for an automorphism, which turns
the two sides into `comap (g⁻¹ ∘ f) I` and `comap (f ∘ g'⁻¹) I`; these agree by the commutation. -/
lemma comap_map_eq_map_comap_of_comp_eq {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (g : S ≃+* S) (g' : R ≃+* R)
    (h : ∀ x, (g : S →+* S) (f x) = f ((g' : R →+* R) x)) (I : Ideal S) :
    Ideal.comap f (Ideal.map (g : S →+* S) I) =
      Ideal.map (g' : R →+* R) (Ideal.comap f I) := by
  refine Ideal.ext fun x => ?_
  simp only [Ideal.mem_comap,
    Ideal.mem_map_iff_of_surjective (g : S →+* S) (RingEquiv.surjective g),
    Ideal.mem_map_iff_of_surjective (g' : R →+* R) (RingEquiv.surjective g')]
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨(g'.symm : R →+* R) x, ?_, RingEquiv.apply_symm_apply g' x⟩
    have h1 : f ((g'.symm : R →+* R) x) = y := by
      apply RingEquiv.injective g
      exact (h ((g'.symm : R →+* R) x)).trans
        ((congrArg f (RingEquiv.apply_symm_apply g' x)).trans hyx.symm)
    exact h1 ▸ hy
  · rintro ⟨z, hz, hzx⟩
    exact ⟨f z, hz, (h z).trans (congrArg f hzx)⟩

/-- **Commutation of the induced maps on rings of integers.**  For `σ : L ≃ₐ[k] L` in a tower
`k ⊆ K ⊆ L` with `K/k` normal, the induced automorphism `σ_L` of `𝓞 L` intertwines the inclusion
`𝓞 K → 𝓞 L` with the induced automorphism `σ_K = σ|_K` of `𝓞 K`; this is the ring-of-integers
shadow of `AlgEquiv.restrictNormal_commutes` for the field maps. -/
lemma ringOfIntegersEquiv_algebraMap_restrictNormal {k K L : Type} [Field k] [NumberField k]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [Normal k K] (σ : L ≃ₐ[k] L) (x : 𝓞 K) :
    NK.GlobalCFT.Place.ringOfIntegersEquiv σ (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap (𝓞 K) (𝓞 L)
        (NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormal σ K) x) := by
  apply NumberField.RingOfIntegers.ext
  rw [NK.GlobalCFT.Place.ringOfIntegersEquiv_apply]
  rw [show ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) from
    NumberField.RingOfIntegers.mapRingHom_apply (algebraMap K L) x]
  rw [show ((algebraMap (𝓞 K) (𝓞 L)
      (NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormal σ K) x) : 𝓞 L) : L)
      = algebraMap K L
        ((NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormal σ K) x : 𝓞 K) : K) from
    NumberField.RingOfIntegers.mapRingHom_apply (algebraMap K L) _]
  rw [NK.GlobalCFT.Place.ringOfIntegersEquiv_apply]
  exact (AlgEquiv.restrictNormal_commutes σ K x).symm

/-- Naturality of "the prime below" under the Galois action, in a tower `k ⊆ K ⊆ L` with `K/k`
normal.  For `σ ∈ Gal(L/k)` and a nonzero prime `Q` of `𝓞 L`, the contraction of `σ • Q` to `𝓞 K` is
the image, under `σ|_K`, of the contraction of `Q`.

Route.  `smulHeightOneSpectrum_asIdeal` writes `(σ • Q).asIdeal` as `Ideal.map σ_L Q`.  The contraction
is `Ideal.comap (algebraMap (𝓞 K) (𝓞 L))`.  `AlgEquiv.restrictNormal_commutes` gives
`σ_L ∘ algebraMap = algebraMap ∘ σ_K`.  For ring equivalences, `comap f ∘ map g = comap (g⁻¹ ∘ f)`
(`Ideal.map_comap_of_equiv` / `Ideal.comap_symm`), which turns the left side into
`map σ_K (comap f Q)`.  This is the two-level version of the proved
`Sha2Lib.under_smulHeightOneSpectrum` (where `σ_K` is the identity on `𝓞 k`); its helper
`comap_map_eq_comap_of_comp_eq` is the template.  About 40 lines. -/
theorem under_smul_heightOneSpectrum {k K L : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [Normal k K] (σ : L ≃ₐ[k] L)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    Ideal.under (NumberField.RingOfIntegers K)
        (NK.GlobalCFT.Place.smulHeightOneSpectrum σ Q).asIdeal =
      Ideal.map
        ((NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormal σ K) :
          NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers K) :
          NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
        (Ideal.under (NumberField.RingOfIntegers K) Q.asIdeal) := by
  rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal, Ideal.under_def, Ideal.under_def]
  exact comap_map_eq_map_comap_of_comp_eq (algebraMap (𝓞 K) (𝓞 L))
    (NK.GlobalCFT.Place.ringOfIntegersEquiv σ)
    (NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormal σ K))
    (fun x => ringOfIntegersEquiv_algebraMap_restrictNormal σ x) Q.asIdeal

end Work.SSGRoute.Sha2Lib
