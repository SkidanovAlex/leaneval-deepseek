import Mathlib
import Submission.NK.Reconstruct.Transport
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one

namespace NK.ReconstructField

open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Two bookkeeping lemmas

The Galois action on the primes of a finite Galois level is defined through `galRestrict`
(`NK.Chebotarev.instSMulPrimeIdeal`, `Commons.…Completion.placeSmul`), whereas the transport of
primes along a ring isomorphism goes through `NK.Reconstruct.ringOfIntegersEquiv`.  For a
*Galois* automorphism the two agree, because both have the same underlying map on `𝓞 L`:

* `coe_ringOfIntegersEquiv_toRingEquiv_eq_galRestrict` compares the two ring homomorphisms;
* `map_ringOfIntegersEquiv_eq_map_galRestrict` is the resulting comparison of `Ideal.map`.
-/

/-- The ring homomorphism of rings of integers induced by a Galois automorphism, computed either
through `ringOfIntegersEquiv` or through `galRestrict`. -/
private lemma coe_ringOfIntegersEquiv_toRingEquiv_eq_galRestrict
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (σ : Gal(L/ℚ)) :
    ((NK.Reconstruct.ringOfIntegersEquiv σ.toRingEquiv : NumberField.RingOfIntegers L ≃+*
        NumberField.RingOfIntegers L) : NumberField.RingOfIntegers L →+*
        NumberField.RingOfIntegers L) =
      ((galRestrict (NumberField.RingOfIntegers ℚ) ℚ L (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L ≃ₐ[NumberField.RingOfIntegers ℚ]
          NumberField.RingOfIntegers L) : NumberField.RingOfIntegers L →+*
        NumberField.RingOfIntegers L) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  show ((NK.Reconstruct.ringOfIntegersEquiv σ.toRingEquiv x :
      NumberField.RingOfIntegers L) : L) =
    ((galRestrict (NumberField.RingOfIntegers ℚ) ℚ L (NumberField.RingOfIntegers L) σ x :
      NumberField.RingOfIntegers L) : L)
  rw [NK.Reconstruct.ringOfIntegersEquiv_apply]
  exact (algebraMap_galRestrict_apply (NumberField.RingOfIntegers ℚ) σ x).symm

/-- The induced map on ideals of a Galois automorphism, computed either through
`ringOfIntegersEquiv` or through `galRestrict`. -/
private lemma map_ringOfIntegersEquiv_eq_map_galRestrict
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (σ : Gal(L/ℚ))
    (I : Ideal (NumberField.RingOfIntegers L)) :
    Ideal.map (NK.Reconstruct.ringOfIntegersEquiv σ.toRingEquiv) I =
      Ideal.map (galRestrict (NumberField.RingOfIntegers ℚ) ℚ L
        (NumberField.RingOfIntegers L) σ : NumberField.RingOfIntegers L →+*
        NumberField.RingOfIntegers L) I := by
  rw [show Ideal.map (NK.Reconstruct.ringOfIntegersEquiv σ.toRingEquiv) I =
      Ideal.map ((NK.Reconstruct.ringOfIntegersEquiv σ.toRingEquiv :
        NumberField.RingOfIntegers L ≃+* NumberField.RingOfIntegers L) :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) I from rfl]
  rw [coe_ringOfIntegersEquiv_toRingEquiv_eq_galRestrict σ]

/-- An automorphism of a number field Galois over `ℚ` stabilising a prime over a completely split
rational prime is trivial: if `L` is a number field with `IsGalois ℚ L`, `P` is a finite prime of
`𝓞 L` whose ramification index and inertia degree over `ℤ` are both `1`, and `w` is a ring
automorphism of `L` with `w(P) = P` (i.e. `primeTransport w P = P`), then `w = 1`.
Route: every ring automorphism of `L` fixes `ℚ`, so `w` is an element of `Gal(L/ℚ)`
(`AlgEquiv.ofRingEquiv`, `map_ratCast`); the compatibility
`ringOfIntegersEquiv σ.toRingEquiv = galRestrict (𝓞 ℚ) ℚ L (𝓞 L) σ` converts `primeTransport w P = P`
into membership of `w` in the decomposition subgroup of `P` in `Gal(L/ℚ)`, whose cardinality is
`e · f = 1` (`Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup` with base `ℚ`,
hence it is trivial by `Subgroup.eq_bot_iff_card`). -/
theorem eq_one_of_primeTransport_eq_self_of_splitCompletely
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    (w : L ≃+* L) (P : NK.Chebotarev.PrimeIdeal L)
    (he : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1)
    (hf : P.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) = 1)
    (hw : NK.Reconstruct.primeTransport w P = P) :
    w = 1 := by
  -- Every ring automorphism of a field of characteristic zero fixes `ℚ`.
  have hfix : ∀ q : ℚ, w (algebraMap ℚ L q) = algebraMap ℚ L q := by
    intro q
    simpa using map_ratCast w q
  let σ : Gal(L/ℚ) := AlgEquiv.ofRingEquiv (f := w) hfix
  have hσw : σ.toRingEquiv = w := rfl
  have hwA : Ideal.map (NK.Reconstruct.ringOfIntegersEquiv w) P.asIdeal = P.asIdeal :=
    congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hw
  -- `w` stabilises `P`, i.e. lies in the decomposition subgroup of `P`.
  have hmem : σ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := ℚ) P := by
    rw [Commons.NumberTheory.NumberField.Completion.mem_decompositionSubgroup]
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal,
      ← map_ringOfIntegersEquiv_eq_map_galRestrict σ P.asIdeal, hσw, hwA]
  -- The decomposition subgroup has order `e · f = 1`, hence is trivial.
  let p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    ⟨P.asIdeal.under (NumberField.RingOfIntegers ℚ), inferInstance,
      Ideal.under_ne_bot (NumberField.RingOfIntegers ℚ) P.ne_bot⟩
  letI : MulSemiringAction Gal(L/ℚ) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers ℚ) ℚ L
      (NumberField.RingOfIntegers L)
  haveI : IsGaloisGroup Gal(L/ℚ) (NumberField.RingOfIntegers ℚ)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/ℚ)) (NumberField.RingOfIntegers ℚ)
      (NumberField.RingOfIntegers L) ℚ L
  have hcard : Nat.card (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup
      (K := ℚ) P) = 1 := by
    rw [Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup p P
        (inferInstance : P.asIdeal.LiesOver p.asIdeal),
      Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal P.asIdeal (Gal(L/ℚ)), he,
      Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal P.asIdeal (Gal(L/ℚ)), hf, mul_one]
  have hbot : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := ℚ) P = ⊥ :=
    (Subgroup.eq_bot_iff_card _).mpr hcard
  have hσ1 : σ = 1 := Subgroup.mem_bot.mp (hbot ▸ hmem)
  rw [← hσw, hσ1]
  rfl

end NK.ReconstructField
