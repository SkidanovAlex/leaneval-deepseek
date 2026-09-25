import Mathlib

/-!
# Transport of the ideal class group along a ring isomorphism

If `e : R ≃+* S` is an isomorphism of Dedekind domains, then there is an isomorphism
of ideal class groups `ClassGroup R ≃* ClassGroup S` sending the class of a height one
prime `v` of `R` to the class of the prime `v.asIdeal.map e` of `S`.

The construction is Mathlib's `ClassGroup.mulEquiv`; the content here is the computation
of its value on the classes of integral ideals (`ClassGroup.mk0`), which is the statement
`mk0_mulEquiv` below, together with its fractional-ideal ingredient
`ringEquivOfRingEquiv_coeIdeal`.
-/

open scoped nonZeroDivisors

namespace Work.CFTLib.ClassGroupTransport

/-- The local instance needed to work with `IsFractionRing.semilinearEquivOfRingEquiv`
outside of its defining file (compare `FractionalIdeal/Operations.lean`). -/
local instance instRingHomInvPairRingEquivSymm {R S : Type} [CommRing R] [CommRing S]
    (f : R ≃+* S) : RingHomInvPair (f : R →+* S) f.symm :=
  RingHomInvPair.of_ringEquiv f

/-- `FractionalIdeal.ringEquivOfRingEquiv` sends the fractional ideal associated to an
integral ideal `I` to the fractional ideal associated to the image ideal `I.map f`. -/
lemma ringEquivOfRingEquiv_coeIdeal {R S K L : Type} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Field K] [Field L] [Algebra R K] [Algebra S L]
    [IsFractionRing R K] [IsFractionRing S L] (f : R ≃+* S) (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv K L f (I : FractionalIdeal R⁰ K) =
      ((I.map (f : R →+* S) : Ideal S) : FractionalIdeal S⁰ L) := by
  apply FractionalIdeal.ext
  intro x
  rw [← FractionalIdeal.mem_coe, ← FractionalIdeal.mem_coe]
  rw [show (↑(FractionalIdeal.ringEquivOfRingEquiv K L f (I : FractionalIdeal R⁰ K)) :
        Submodule S L)
      = Submodule.map (IsFractionRing.semilinearEquivOfRingEquiv K L f).toLinearMap
          (↑(I : FractionalIdeal R⁰ K)) from rfl]
  simp only [FractionalIdeal.coe_coeIdeal, IsLocalization.coeSubmodule, Submodule.mem_map,
    Algebra.linearMap_apply]
  constructor
  · rintro ⟨y, ⟨r, hr, rfl⟩, hyx⟩
    refine ⟨f r, ?_, ?_⟩
    · exact Ideal.subset_span ⟨r, hr, rfl⟩
    · exact (IsFractionRing.semilinearEquivOfRingEquiv_algebraMap K L f r).symm.trans hyx
  · rintro ⟨y, hy, hyx⟩
    rw [Ideal.mem_map_iff_of_surjective (f : R →+* S) f.surjective] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    refine ⟨algebraMap R K r, ⟨r, hr, rfl⟩, ?_⟩
    exact (IsFractionRing.semilinearEquivOfRingEquiv_algebraMap K L f r).trans hyx

/-- The unit of invertible fractional ideals associated to an integral ideal `I` is sent by
the induced equivalence to the unit associated to `I.map e`. -/
lemma unitsMapEquiv_mk0 {R S : Type} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] (e : R ≃+* S) (I : (Ideal R)⁰) :
    Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv (FractionRing R) (FractionRing S) e)
        (FractionalIdeal.mk0 (FractionRing R) I) =
      FractionalIdeal.mk0 (FractionRing S)
        ⟨I.1.map (e : R →+* S), mem_nonZeroDivisors_of_ne_zero
          ((Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
            (mem_nonZeroDivisors_iff_ne_zero.mp I.2))⟩ := by
  apply Units.ext
  simp only [Units.coe_mapEquiv, FractionalIdeal.coe_mk0]
  exact ringEquivOfRingEquiv_coeIdeal e I.1

set_option backward.isDefEq.respectTransparency.types false in
/-- `ClassGroup.mulEquiv e` sends the class of an integral ideal `I` (i.e. `ClassGroup.mk0 I`)
to the class of the image ideal `I.map e`. -/
theorem mk0_mulEquiv {R S : Type} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] (e : R ≃+* S) (I : (Ideal R)⁰) :
    ClassGroup.mulEquiv e (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨I.1.map (e : R →+* S), mem_nonZeroDivisors_of_ne_zero
        ((Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2))⟩ := by
  set J : (Ideal S)⁰ := ⟨I.1.map (e : R →+* S), mem_nonZeroDivisors_of_ne_zero
    ((Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2))⟩ with hJ
  show ClassGroup.mulEquiv e (ClassGroup.mk0 I) = ClassGroup.mk0 J
  have key : Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv (FractionRing R)
        (FractionRing S) e) (FractionalIdeal.mk0 (FractionRing R) I) =
      FractionalIdeal.mk0 (FractionRing S) J := unitsMapEquiv_mk0 e I
  rw [ClassGroup.mulEquiv_apply, ClassGroup.equiv_mk0]
  rw [QuotientGroup.congr_mk']
  rw [key]
  rw [← ClassGroup.equiv_mk0 (FractionRing S) J, MulEquiv.symm_apply_apply]

theorem exists_classGroup_mulEquiv {R S : Type} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] (e : R ≃+* S) :
    ∃ φ : ClassGroup R ≃* ClassGroup S, ∀ (v : IsDedekindDomain.HeightOneSpectrum R)
      (w : IsDedekindDomain.HeightOneSpectrum S), w.asIdeal = v.asIdeal.map (e : R →+* S) →
      φ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) =
      ClassGroup.mk0 ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩ := by
  refine ⟨ClassGroup.mulEquiv e, ?_⟩
  intro v w hw
  rw [mk0_mulEquiv]
  congr 1
  exact Subtype.ext hw.symm

end Work.CFTLib.ClassGroupTransport
