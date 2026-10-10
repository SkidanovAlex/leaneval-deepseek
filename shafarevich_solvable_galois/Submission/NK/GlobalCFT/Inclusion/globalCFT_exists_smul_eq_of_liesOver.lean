import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Commons.NumberTheory.RamificationInertia.exists_map_galRestrict_eq
import Submission.NK.GlobalCFT.Inclusion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transitivity of the Galois action on the places above a fixed place

For `L / K` a finite Galois extension of number fields, the Galois group `Gal(L/K)` acts
transitively on the set of places `w` of `L` lying over a fixed place `v` of `K`
(`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver`).

The two cases are the classical ones:

* an archimedean place: the extensions of `v` to `L` correspond to the orbits of the
  `Gal(L/K)`-action on the infinite places of `L`, which is transitive by
  `InfinitePlace.exists_smul_eq_of_comap_eq` (Mathlib);
* a nonarchimedean place: the primes of `𝓞 L` above a prime `p` of `𝓞 K` are permuted
  transitively by `Gal(L/K)`, formalised in the shared commons as
  `Commons.NumberTheory.RamificationInertia.exists_map_galRestrict_eq`.

The only glue needed is that the action of `σ` on `𝓞 L` used in the definition of the
`Gal(L/K)`-action on the places (`NK.GlobalCFT.Place.ringOfIntegersEquiv`) agrees with the
`galRestrict` action of Mathlib's ramification theory; this is
`ringOfIntegersEquiv_eq_galRestrict` below.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain

namespace NK.GlobalCFT.Inclusion

/-- The action of `σ : L ≃ₐ[K] L` on the ring of integers of `L` used to define the
`Gal(L/K)`-action on the places of `L` (via `NumberField.RingOfIntegers.mapAlgEquiv`) coincides
with Mathlib's `galRestrict` action of ramification theory.  Both send `x : 𝓞 L` to the unique
element of `𝓞 L` mapping to `σ x` in `L`. -/
private lemma ringOfIntegersEquiv_eq_galRestrict {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) :
    (Place.ringOfIntegersEquiv σ : 𝓞 L →+* 𝓞 L) =
      (galRestrict (𝓞 K) K L (𝓞 L) σ : 𝓞 L →+* 𝓞 L) := by
  apply RingHom.ext
  intro x
  apply NumberField.RingOfIntegers.ext
  have h1 : (((galRestrict (𝓞 K) K L (𝓞 L) σ) : 𝓞 L →+* 𝓞 L) x : L) = σ (x : L) :=
    algebraMap_galRestrict_apply (𝓞 K) σ x
  have h2 : (((Place.ringOfIntegersEquiv σ) : 𝓞 L →+* 𝓞 L) x : L) = σ (x : L) := by
    change (NumberField.RingOfIntegers.mapRingHom (σ : L →+* L) x : L) = σ (x : L)
    rw [NumberField.RingOfIntegers.mapRingHom_apply]
    rfl
  rw [h1, h2]

/-- **Transitivity of the Galois action on the places above a fixed place.**  If `w` and `w'`
are places of `L` lying over a common place `v` of `K` in a finite Galois extension of number
fields `L / K`, then some `σ : Gal(L/K)` carries `w` to `w'`. -/
theorem globalCFT_exists_smul_eq_of_liesOver {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {w w' : Place L} {v : Place K} (hw : Place.LiesOver w v) (hw' : Place.LiesOver w' v) :
    ∃ σ : L ≃ₐ[K] L, σ • w = w' := by
  rcases hw with ⟨w₁, v₁, rfl, rfl, hL1⟩ | ⟨q, Q, rfl, rfl, hL1⟩
  · -- `w` and `v` are archimedean
    rcases hw' with ⟨w₂, v₂, h2, h3, hL2⟩ | ⟨q', Q', h2, h3, hL2⟩
    · -- `w'` is archimedean too
      rw [Place.ofInfinite_inj] at h3
      subst v₂
      subst w'
      haveI : w₁.LiesOver v₁ := hL1
      haveI : w₂.LiesOver v₁ := hL2
      obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq
        ((InfinitePlace.LiesOver.comap_eq w₁ v₁).trans
          (InfinitePlace.LiesOver.comap_eq w₂ v₁).symm)
      exact ⟨σ, by rw [Place.smul_ofInfinite, hσ]⟩
    · -- `w'` finite over an infinite place: impossible
      exact absurd h3 (Place.ofInfinite_ne_ofFinite v₁ Q')
  · -- `w` and `v` are nonarchimedean
    rcases hw' with ⟨w₂, v₂, h2, h3, hL2⟩ | ⟨q', Q', h2, h3, hL2⟩
    · -- `w'` infinite over a finite place: impossible
      exact absurd h3.symm (Place.ofInfinite_ne_ofFinite v₂ Q)
    · -- `w'` is nonarchimedean too: transitivity of the action on the primes above `Q`
      rw [Place.ofFinite_inj] at h3
      subst Q'
      subst w'
      haveI : q.asIdeal.LiesOver Q.asIdeal := hL1
      haveI : q'.asIdeal.LiesOver Q.asIdeal := hL2
      obtain ⟨σ, hσ⟩ := Commons.NumberTheory.RamificationInertia.exists_map_galRestrict_eq Q q q'
      refine ⟨σ, ?_⟩
      rw [Place.smul_ofFinite, Place.ofFinite_inj]
      apply HeightOneSpectrum.ext
      rw [Place.smulHeightOneSpectrum_asIdeal]
      have hmap : Ideal.map (Place.ringOfIntegersEquiv σ : 𝓞 L →+* 𝓞 L) q.asIdeal = q'.asIdeal := by
        rw [ringOfIntegersEquiv_eq_galRestrict σ]
        exact hσ
      exact hmap

end NK.GlobalCFT.Inclusion
