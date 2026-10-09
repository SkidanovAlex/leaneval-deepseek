import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of places along an isomorphism of number fields

First ingredient of the universe bridge (§10 of `NOTE_session18_divisibility_route.md`): a
`ℚ`-algebra isomorphism `e : K ≃ₐ[ℚ] K₀` of number fields restricts to a ring isomorphism
`𝓞 K ≃+* 𝓞 K₀` of the rings of integers, along which places (height-one spectra) transport.
-/

universe u v

open IsDedekindDomain

namespace Commons.NumberTheory.NumberField

variable {K K₀ : Type*} [Field K] [NumberField K] [Field K₀] [NumberField K₀]

/-- An integral element stays integral under a `ℚ`-algebra isomorphism of number fields. -/
lemma isIntegral_map_algEquiv (e : K ≃ₐ[ℚ] K₀) {x : K} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (e x) :=
  IsIntegral.map (e.restrictScalars ℤ) hx

lemma isIntegral_map_algEquiv_symm (e : K ≃ₐ[ℚ] K₀) {y : K₀} (hy : IsIntegral ℤ y) :
    IsIntegral ℤ (e.symm y) :=
  IsIntegral.map (e.symm.restrictScalars ℤ) hy

/-- **Restriction of a `ℚ`-algebra isomorphism of number fields to the rings of integers.** -/
noncomputable def ringOfIntegersRingEquiv (e : K ≃ₐ[ℚ] K₀) :
    NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers K₀ where
  toFun x := ⟨e x, isIntegral_map_algEquiv e x.2⟩
  invFun y := ⟨e.symm y, isIntegral_map_algEquiv_symm e y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : K))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : K₀))
  map_mul' x y := Subtype.ext (map_mul e (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add e (x : K) (y : K))

@[simp]
lemma ringOfIntegersRingEquiv_apply_coe (e : K ≃ₐ[ℚ] K₀) (x : NumberField.RingOfIntegers K) :
    ((ringOfIntegersRingEquiv e x : NumberField.RingOfIntegers K₀) : K₀) = e x := rfl

/-- **Transport of a place along a `ℚ`-algebra isomorphism of number fields.** -/
noncomputable def heightOneSpectrumMap (e : K ≃ₐ[ℚ] K₀)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    HeightOneSpectrum (NumberField.RingOfIntegers K₀) where
  asIdeal := Q.asIdeal.comap (ringOfIntegersRingEquiv e).symm.toRingHom
  isPrime := Q.isPrime.comap _
  ne_bot := fun h => Q.ne_bot (by
    have hsurj : Function.Surjective (ringOfIntegersRingEquiv e).symm.toRingHom :=
      (ringOfIntegersRingEquiv e).symm.surjective
    have hle : Q.asIdeal ≤ ⊥ := by
      refine ((Ideal.comap_le_comap_iff_of_surjective _ hsurj) Q.asIdeal ⊥).mp ?_
      rw [h, Ideal.comap_bot_of_injective (f := (ringOfIntegersRingEquiv e).symm.toRingHom)
        (ringOfIntegersRingEquiv e).symm.injective]
    exact le_bot_iff.mp hle)

@[simp]
lemma heightOneSpectrumMap_asIdeal (e : K ≃ₐ[ℚ] K₀)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (heightOneSpectrumMap e Q).asIdeal =
      Q.asIdeal.comap (ringOfIntegersRingEquiv e).symm.toRingHom := rfl

/-- The transported place is carried back to `Q` by the ring isomorphism. -/
lemma heightOneSpectrumMap_asIdeal_liesOver (e : K ≃ₐ[ℚ] K₀)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (heightOneSpectrumMap e Q).asIdeal.comap (ringOfIntegersRingEquiv e).toRingHom =
      Q.asIdeal := by
  rw [heightOneSpectrumMap_asIdeal, Ideal.comap_comap]
  rw [show (ringOfIntegersRingEquiv e).symm.toRingHom.comp
      (ringOfIntegersRingEquiv e).toRingHom = RingHom.id _ from by ext; simp]
  exact Ideal.comap_id _



/-- The image of `Q` under the induced ring isomorphism of integers is the transported place. -/
lemma heightOneSpectrumMap_asIdeal_eq_map (e : K ≃ₐ[ℚ] K₀)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Q.asIdeal.map (ringOfIntegersRingEquiv e).toRingHom =
      (heightOneSpectrumMap e Q).asIdeal := by
  rw [heightOneSpectrumMap_asIdeal]
  ext x
  rw [Ideal.mem_map_iff_of_surjective (f := (ringOfIntegersRingEquiv e).toRingHom)
    (ringOfIntegersRingEquiv e).surjective, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨(ringOfIntegersRingEquiv e).symm x, hx, by simp⟩

/-- **The induced isomorphism of residue fields of a transported place.** -/
noncomputable def residueFieldQuotientRingEquiv (e : K ≃ₐ[ℚ] K₀)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (NumberField.RingOfIntegers K ⧸ Q.asIdeal) ≃+*
      (NumberField.RingOfIntegers K₀ ⧸ (heightOneSpectrumMap e Q).asIdeal) :=
  Ideal.quotientEquiv _ _ (ringOfIntegersRingEquiv e) (heightOneSpectrumMap_asIdeal_eq_map e Q).symm



/-- The multiplicative equivalence on ideals induced by a ring equivalence. -/
noncomputable def idealMapMulEquiv {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R ≃+* S) : Ideal R ≃* Ideal S where
  toFun I := I.map f.toRingHom
  invFun J := J.map f.symm.toRingHom
  left_inv I := by
    change Ideal.map f.symm.toRingHom (Ideal.map f.toRingHom I) = I
    rw [Ideal.map_map]
    rw [show f.symm.toRingHom.comp f.toRingHom = RingHom.id R from by ext; simp]
    exact Ideal.map_id I
  right_inv J := by
    change Ideal.map f.toRingHom (Ideal.map f.symm.toRingHom J) = J
    rw [Ideal.map_map]
    rw [show f.toRingHom.comp f.symm.toRingHom = RingHom.id S from by ext; simp]
    exact Ideal.map_id J
  map_mul' I J := Ideal.map_mul f.toRingHom I J

@[simp]
lemma idealMapMulEquiv_apply {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R ≃+* S)
    (I : Ideal R) : idealMapMulEquiv f I = I.map f.toRingHom := rfl

/-- **The `Associates.count` / `multiplicity` transport along `ringOfIntegersRingEquiv`.**

The `Q`-adic valuation of `r : 𝓞 K` is `exp (-multiplicity Q.asIdeal (span {r}))`
(`IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity`), and both arguments of
`multiplicity` transport along the induced multiplicative equivalence of ideals
(`multiplicity_map_eq`).  Hence the `Q`-adic valuation on the ring of integers is compatible with
`ringOfIntegersRingEquiv e` and the transported place `heightOneSpectrumMap e Q`. -/
theorem intValuation_ringOfIntegersRingEquiv (e : K ≃ₐ[ℚ] K₀)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : NumberField.RingOfIntegers K) :
    (heightOneSpectrumMap e Q).intValuation (ringOfIntegersRingEquiv e r) = Q.intValuation r := by
  rcases eq_or_ne r 0 with h | h
  · subst h
    simp [map_zero]
  · have hne : ringOfIntegersRingEquiv e r ≠ 0 := by
      intro hz
      apply h
      have := congrArg (ringOfIntegersRingEquiv e).symm hz
      simpa using this
    rw [Q.intValuation_eq_exp_neg_multiplicity h,
      (heightOneSpectrumMap e Q).intValuation_eq_exp_neg_multiplicity hne]
    congr 2
    -- `multiplicity` transport
    have hspan : Ideal.span {ringOfIntegersRingEquiv e r} =
        (Ideal.span {r}).map (ringOfIntegersRingEquiv e).toRingHom := by
      rw [Ideal.map_span]
      simp
    rw [hspan, ← heightOneSpectrumMap_asIdeal_eq_map,
      ← idealMapMulEquiv_apply, ← idealMapMulEquiv_apply,
      multiplicity_map_eq (idealMapMulEquiv (ringOfIntegersRingEquiv e))]



/-- **The `Q`-adic valuation on `K` is carried to the `Q₀`-adic valuation on `K₀` by `e`.**

This is the isometry behind the universe bridge (recipe (i) of §14 of the note).  It is proved by
writing `x = r / s` with `r s : 𝓞 K` (`IsLocalization.mk'_surjective`), using
`HeightOneSpectrum.valuation_of_mk'` on both sides, and feeding in
`intValuation_ringOfIntegersRingEquiv`. -/
theorem valuation_ringOfIntegersRingEquiv (e : K ≃ₐ[ℚ] K₀)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : K) :
    (heightOneSpectrumMap e Q).valuation K₀ (e x) = Q.valuation K x := by
  obtain ⟨⟨r, s⟩, hrs⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (NumberField.RingOfIntegers K)) x
  have hs : ringOfIntegersRingEquiv e (↑s) ≠ 0 :=
    fun h => nonZeroDivisors.ne_zero s.2 (by
      have := congrArg (ringOfIntegersRingEquiv e).symm h
      simpa using this)
  have hcoe : e (IsLocalization.mk' K r s) =
      IsLocalization.mk' K₀ (ringOfIntegersRingEquiv e r)
        ⟨ringOfIntegersRingEquiv e (↑s), mem_nonZeroDivisors_of_ne_zero hs⟩ := by
    simp only [IsFractionRing.mk'_eq_div, map_div₀, ringOfIntegersRingEquiv_apply_coe]
  rw [← hrs, hcoe, IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    intValuation_ringOfIntegersRingEquiv, intValuation_ringOfIntegersRingEquiv]

end Commons.NumberTheory.NumberField
