import Mathlib.NumberTheory.RamificationInertia.Galois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transitivity of the action of `Gal(L/K)` on the primes of `𝓞 L` over `p`

For `L/K` a finite Galois extension of number fields and `p` a nonzero prime of
`𝓞 K`, the Galois group `Gal(L/K)` acts transitively on the set of primes of
`𝓞 L` lying over `p`.  Concretely: for any two primes `q₁`, `q₂` of `𝓞 L` above
`p` there is `σ : L ≃ₐ[K] L` carrying `q₁` to `q₂` under the induced
automorphism `galRestrict 𝓞K K L 𝓞L σ` of `𝓞 L`.

This is the `map`-form of Mathlib's `Ideal.exists_comap_galRestrict_eq`
(transitivity in `comap` form); the two are equivalent because
`galRestrict 𝓞K K L 𝓞L σ` is bijective.
-/

namespace Commons.NumberTheory.RamificationInertia

theorem exists_map_galRestrict_eq {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q₁ q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [q₁.asIdeal.LiesOver p.asIdeal] [q₂.asIdeal.LiesOver p.asIdeal] :
    ∃ σ : L ≃ₐ[K] L,
      q₁.asIdeal.map (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) σ : NumberField.RingOfIntegers L →+*
        NumberField.RingOfIntegers L) = q₂.asIdeal := by
  -- Transitivity in `comap` form, with the roles of `q₁` and `q₂` exchanged:
  -- some `σ` satisfies `q₂.asIdeal.comap (galRestrict … σ) = q₁.asIdeal`.
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq
    (R := NumberField.RingOfIntegers K) (K := K) (L := L)
    (S := NumberField.RingOfIntegers L) (p := p.asIdeal)
    (P₁ := q₂.asIdeal) (P₂ := q₁.asIdeal)
    (show q₂.asIdeal ∈ p.asIdeal.primesOver _ from ⟨q₂.2, inferInstance⟩)
    (show q₁.asIdeal ∈ p.asIdeal.primesOver _ from ⟨q₁.2, inferInstance⟩)
  refine ⟨σ, ?_⟩
  -- `galRestrict` is bijective, so `map` is a left inverse of `comap`.
  rw [← hσ]
  exact Ideal.map_comap_of_surjective _ (galRestrict _ _ _ _ σ).surjective _

end Commons.NumberTheory.RamificationInertia