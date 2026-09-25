import Mathlib
import Submission.NK.UniverseUnify.ringOfIntegersULiftEquiv

/-!
# The height one spectrum is invariant under `ULift`

The ring of integers of a number field is invariant under `ULift` up to isomorphism
(`NK.UniverseUnify.ringOfIntegersULiftEquiv`), and the height one spectrum of a Dedekind domain
is invariant under ring isomorphisms (the nonzero prime ideals are transported by `Ideal.map`).
Combining the two gives the universe transport for the *places* of a number field:

`NK.UniverseUnify.heightOneSpectrumULift` : for every number field `K` the finite places of
`ULift K` and of `K` are in bijection.

Nothing here is specific to number fields: the general statement is that any ring equivalence
`R ≃+* S` between Dedekind domains induces a bijection
`HeightOneSpectrum R ≃ HeightOneSpectrum S` (`heightOneSpectrumCongr`), by mapping the ideal along
the equivalence.  The two maps are inverse to each other because `Ideal.map` is functorial
(`Ideal.map_map`, `Ideal.map_id`).
-/

namespace NK.UniverseUnify

universe u w

open IsDedekindDomain

/-- **Transport of a height one prime along a ring equivalence.**

For a ring equivalence `e : R ≃+* S` between Dedekind domains and a nonzero prime ideal `v` of `R`,
the image `v.asIdeal.map e` is again a nonzero prime ideal.  (`Ideal.map_isPrime_of_equiv` is the
instance recording primality, and `Ideal.map_eq_bot_iff_of_injective` that the zero ideal is not hit
because `e` is injective.) -/
noncomputable def heightOneSpectrumMapRingEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] (e : R ≃+* S)
    (v : HeightOneSpectrum R) : HeightOneSpectrum S where
  asIdeal := v.asIdeal.map (e : R →+* S)
  isPrime := Ideal.map_isPrime_of_equiv e
  ne_bot := fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h)

/-- The defining computation of `heightOneSpectrumMapRingEquiv` on `asIdeal`. -/
@[simp]
theorem heightOneSpectrumMapRingEquiv_asIdeal {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] (e : R ≃+* S)
    (v : HeightOneSpectrum R) :
    (heightOneSpectrumMapRingEquiv e v).asIdeal = v.asIdeal.map (e : R →+* S) := rfl

/-- **The height one spectrum is a functor on ring equivalences.**

A ring equivalence `e : R ≃+* S` between Dedekind domains induces a bijection of height one
spectra, `v ↦ v.asIdeal.map e`, whose inverse is `w ↦ w.asIdeal.map e.symm`.  The two round trips
are `Ideal.map_map` followed by `Ideal.map_id` (`e.symm ∘ e = id`, `e ∘ e.symm = id`). -/
noncomputable def heightOneSpectrumCongr {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] (e : R ≃+* S) :
    HeightOneSpectrum R ≃ HeightOneSpectrum S where
  toFun := heightOneSpectrumMapRingEquiv e
  invFun := heightOneSpectrumMapRingEquiv e.symm
  left_inv v := by
    apply HeightOneSpectrum.ext
    show (v.asIdeal.map (e : R →+* S)).map (e.symm : S →+* R) = v.asIdeal
    rw [Ideal.map_map]
    have hcomp : ((e.symm : S →+* R).comp (e : R →+* S)) = RingHom.id R := by
      ext x; exact e.symm_apply_apply x
    rw [hcomp, Ideal.map_id]
  right_inv v := by
    apply HeightOneSpectrum.ext
    show (v.asIdeal.map (e.symm : S →+* R)).map (e : R →+* S) = v.asIdeal
    rw [Ideal.map_map]
    have hcomp : ((e : R →+* S).comp (e.symm : S →+* R)) = RingHom.id S := by
      ext x; exact e.apply_symm_apply x
    rw [hcomp, Ideal.map_id]

/-- **The finite places of a number field are invariant under `ULift`.**

The ring of integers of `ULift K` is isomorphic to that of `K` as a ring
(`NK.UniverseUnify.ringOfIntegersULiftEquiv`), and a ring isomorphism of Dedekind domains induces
a bijection of height one spectra (`heightOneSpectrumCongr`). -/
theorem heightOneSpectrumULift (K : Type u) [Field K] [NumberField K] :
    Nonempty (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (ULift.{w} K)) ≃
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  obtain ⟨e⟩ := ringOfIntegersULiftEquiv (K := K)
  exact ⟨heightOneSpectrumCongr e⟩

end NK.UniverseUnify
