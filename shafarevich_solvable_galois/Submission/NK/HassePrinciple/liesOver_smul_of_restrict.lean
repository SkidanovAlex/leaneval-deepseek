import Mathlib
import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The "lies over" relation is equivariant under `Gal`-equivariant pairs

Let `K → F → L` be a tower of number fields and let `τ : L ≃ₐ[K] L`, `A : F ≃ₐ[K] F` be
automorphisms such that `τ` restricts to `A` on `F`, i.e.

`algebraMap F L (A y) = τ (algebraMap F L y)` for all `y : F`.

Then `τ` and `A` act compatibly on the places: if `w` is a place of `L` lying over the place `v`
of `F`, then `τ • w` lies over `A • v`.

The proof splits into the two kinds of places.

* For an archimedean (infinite) place the action of the Galois group is precomposition with the
  inverse automorphism, so the statement reduces to the pointwise identity
  `τ.symm (algebraMap F L y) = algebraMap F L (A.symm y)`, which is a reformulation of `hA`.
* For a nonarchimedean (finite) place, `w` and `v` correspond to nonzero primes `q ⊆ 𝓞 L` and
  `Q ⊆ 𝓞 F`; the action sends a prime to its image under the induced automorphism of the ring of
  integers. The commutativity of the square

  `𝓞 F --algebraMap--> 𝓞 L`
  `|ringOfIntegersEquiv A      |ringOfIntegersEquiv τ`
  `𝓞 F --algebraMap--> 𝓞 L`

  (which is `hA` read on integral elements) implies that the image of a prime over `Q` is a prime
  over the image of `Q`.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace NK.HassePrinciple

open NK.GlobalCFT

variable {K F L : Type*} [Field K] [NumberField K] [Field F]
    [NumberField F] [Field L] [NumberField L] [Algebra K F] [Algebra F L] [Algebra K L]
    [IsScalarTower K F L]

/-- **Commutativity of the ring-of-integers square.**  If `τ : L ≃ₐ[K] L` restricts to
`A : F ≃ₐ[K] F` on `F` (hypothesis `hA`), then the induced automorphisms of the rings of integers
commute with the inclusion `𝓞 F → 𝓞 L`:
`ringOfIntegersEquiv τ (algebraMap x) = algebraMap (ringOfIntegersEquiv A x)`. -/
lemma ringOfIntegersEquiv_algebraMap (τ : L ≃ₐ[K] L) (A : F ≃ₐ[K] F)
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y)) (x : 𝓞 F) :
    Place.ringOfIntegersEquiv τ (algebraMap (𝓞 F) (𝓞 L) x) =
      algebraMap (𝓞 F) (𝓞 L) (Place.ringOfIntegersEquiv A x) := by
  apply NumberField.RingOfIntegers.ext
  rw [show ((Place.ringOfIntegersEquiv τ) ((algebraMap (𝓞 F) (𝓞 L)) x) : L) =
      τ (((algebraMap (𝓞 F) (𝓞 L)) x : 𝓞 L) : L) from rfl]
  rw [show (((algebraMap (𝓞 F) (𝓞 L)) x : 𝓞 L) : L) = algebraMap F L (x : F) from rfl]
  rw [show (((algebraMap (𝓞 F) (𝓞 L)) ((Place.ringOfIntegersEquiv A) x) : 𝓞 L) : L)
      = algebraMap F L (((Place.ringOfIntegersEquiv A) x : 𝓞 F) : F) from rfl]
  rw [show (((Place.ringOfIntegersEquiv A) x : 𝓞 F) : F) = A (x : F) from rfl]
  exact (hA (x : F)).symm

/-- The inverse form of `ringOfIntegersEquiv_algebraMap`: the inverse automorphism
`(ringOfIntegersEquiv τ)⁻¹` corresponds to `A⁻¹` on `F`. -/
lemma ringOfIntegersEquiv_symm_algebraMap (τ : L ≃ₐ[K] L) (A : F ≃ₐ[K] F)
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y)) (x : 𝓞 F) :
    (Place.ringOfIntegersEquiv τ).symm (algebraMap (𝓞 F) (𝓞 L) x) =
      algebraMap (𝓞 F) (𝓞 L) ((Place.ringOfIntegersEquiv A).symm x) := by
  apply (Place.ringOfIntegersEquiv τ).injective
  rw [RingEquiv.apply_symm_apply,
    ringOfIntegersEquiv_algebraMap τ A hA ((Place.ringOfIntegersEquiv A).symm x),
    RingEquiv.apply_symm_apply]

/-- **Finite places.**  The image of a prime of `𝓞 L` over `Q` under `τ` is a prime over the
image of `Q` under `A`. -/
lemma liesOver_map_ringOfIntegersEquiv (τ : L ≃ₐ[K] L) (A : F ≃ₐ[K] F)
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    {q : HeightOneSpectrum (𝓞 L)} {Q : HeightOneSpectrum (𝓞 F)}
    (h : q.asIdeal.LiesOver Q.asIdeal) :
    (Ideal.map (Place.ringOfIntegersEquiv τ) q.asIdeal).LiesOver
      (Ideal.map (Place.ringOfIntegersEquiv A) Q.asIdeal) := by
  refine Ideal.LiesOver.mk ?_
  ext x
  rw [Ideal.mem_comap, ← Ideal.comap_symm (Place.ringOfIntegersEquiv A),
      ← Ideal.comap_symm (Place.ringOfIntegersEquiv τ), Ideal.mem_comap, Ideal.mem_comap,
      ringOfIntegersEquiv_symm_algebraMap τ A hA x]
  exact Ideal.mem_of_liesOver q.asIdeal Q.asIdeal _

/-- **Infinite places.**  If `w` lies over `v` then `τ • w` lies over `A • v`. -/
lemma liesOver_smul_infinitePlace (τ : L ≃ₐ[K] L) (A : F ≃ₐ[K] F)
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    {w : InfinitePlace L} {v : InfinitePlace F} (h : w.LiesOver v) :
    (τ • w).LiesOver (A • v) := by
  have hwv : ∀ y : F, w (algebraMap F L y) = v y := fun y => by
    have h1 := congrArg (fun (u : InfinitePlace F) => u y)
      (NumberField.InfinitePlace.LiesOver.comap_eq w v)
    simpa using h1
  have hsymm : ∀ y : F, τ.symm (algebraMap F L y) = algebraMap F L (A.symm y) := fun y => by
    have h2 := congrArg τ.symm (hA (A.symm y)).symm
    simpa using h2.symm
  refine AbsoluteValue.LiesOver.mk ?_
  ext y
  show (τ • w) (algebraMap F L y) = (A • v) y
  rw [NumberField.InfinitePlace.smul_apply, hsymm y, hwv,
    NumberField.InfinitePlace.smul_apply]

theorem liesOver_smul_of_restrict {K F L : Type*} [Field K] [NumberField K] [Field F]
    [NumberField F] [Field L] [NumberField L] [Algebra K F] [Algebra F L] [Algebra K L]
    [IsScalarTower K F L]
    (τ : L ≃ₐ[K] L) (A : F ≃ₐ[K] F)
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    {w : NK.GlobalCFT.Place L} {v : NK.GlobalCFT.Place F}
    (h : NK.GlobalCFT.Place.LiesOver w v) :
    NK.GlobalCFT.Place.LiesOver (τ • w) (A • v) := by
  rw [Place.liesOver_iff] at h ⊢
  rcases h with ⟨w', v', rfl, rfl, hwv⟩ | ⟨q, Q, rfl, rfl, hqQ⟩
  · rw [Place.smul_ofInfinite, Place.smul_ofInfinite]
    exact Place.liesOver_ofInfinite (liesOver_smul_infinitePlace τ A hA hwv)
  · rw [Place.smul_ofFinite, Place.smul_ofFinite]
    exact Place.liesOver_ofFinite (liesOver_map_ringOfIntegersEquiv τ A hA hqQ)

end NK.HassePrinciple
