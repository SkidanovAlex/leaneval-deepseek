import Mathlib
import Submission.Work.DSG4b.Root
import Submission.Work.DSG4b.RootLift

namespace Work.DSG4b

universe u

/-- For a maximal ideal `m` of a commutative ring `A`, the residue field of the localisation
`A_m = Localization.AtPrime m` is canonically the quotient `A ⧸ m`: the canonical map
`A ⧸ m → κ(m)` is bijective because `A ⧸ m` is a field. -/
theorem residueField_localizationAtPrime_equiv (A : Type u) [CommRing A] (m : Ideal A)
    [m.IsMaximal] :
    Nonempty (IsLocalRing.ResidueField (Localization.AtPrime m) ≃+* (A ⧸ m)) :=
  ⟨(RingEquiv.ofBijective (algebraMap (A ⧸ m) m.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField m)).symm⟩

/-- The residue field of the "root local ring" `Work.DSG4b.rootLocal R` (the localisation of the
root presentation of the residue-field enlargement at its canonical `K`-valued point) is the
algebraic closure `K = AlgebraicClosure (ResidueField R)` of the residue field of `R`.

Concretely, the canonical evaluation `rootEv : rootRing R →+* K` is surjective with kernel
`rootKer R` (the ideal at which we localise), so it induces an isomorphism
`rootRing R ⧸ rootKer R ≃+* K`, and the residue field of the localisation is the fraction field of
that quotient.  (Stated as `Nonempty` because a ring equivalence is data, not a proposition.) -/
theorem rootLocal_residueField_equiv (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    Nonempty (IsLocalRing.ResidueField (Work.DSG4b.rootLocal R) ≃+* Work.DSG4b.AlgebrClosure R) :=
  by
  -- `rootKer R = ker (rootEv R)` is maximal, as the kernel of a surjection onto the field `K`.
  have hmax : (rootKer R).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (rootEv R) (rootEv_surjective R)
  -- The residue field of `Localization.AtPrime (rootKer R)` is `rootRing R ⧸ rootKer R`,
  -- by the helper lemma above applied to the (maximal) ideal `rootKer R`.
  obtain ⟨h1⟩ := residueField_localizationAtPrime_equiv (rootRing R) (rootKer R)
  -- The first isomorphism theorem turns the surjection `rootEv` into `rootRing R ⧸ rootKer R ≃+* K`.
  have h2 : (rootRing R ⧸ rootKer R) ≃+* AlgebrClosure R :=
    RingHom.quotientKerEquivOfSurjective (rootEv_surjective R)
  exact ⟨h1.trans h2⟩

end Work.DSG4b
