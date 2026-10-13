import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map

/-!
# DSEQ0 (area EQ0): equal characteristic zero — basic API

This module is the base layer of the area `EQ0` of the direct-summand proof map
(`sources/dsmap/direct_summand_proof_map.md`, §5, and the review
`sources/dsmap/direct_summand_proof_map_REVIEW.md`).

The vocabulary (`DSMap.phi`, `DSMap.GammaA`, `DSMap.RG`, `DSMap.rgUnit`, `DSMap.DSplit`,
`DSMap.cechZ`, `DSMap.coaug0`, ...) lives in the frozen file `Submission/Work/DSMap/Map.lean`
and is imported, never redefined.

Contents of this file:

* `Work.DSEQ0.isUnit_natCast_of_charZero_residueField`: in a local ring whose residue field has
  characteristic zero every nonzero natural number is a unit.  This is the arithmetic input of
  the trace argument: the generic degree `[K(X):K]` is invertible.
* elementary manipulations of `DSplit` (building a splitting from a retraction, and conversely),
  phrased so that they can be used with both `IsSplitMono` and `DSplit`.

-/

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQ0

universe u v w w₁ w₂

section CharZero

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- In a local ring whose residue field has characteristic zero, every nonzero natural number
is a unit.  (If `n ≠ 0` were not a unit then `n ∈ 𝔪` and `n` would die in the residue field,
contradicting `CharZero`.) -/
theorem isUnit_natCast_of_charZero_residueField [CharZero (IsLocalRing.ResidueField A)]
    {n : ℕ} (hn : n ≠ 0) : IsUnit (n : A) := by
  by_contra h
  have hmem : (n : A) ∈ IsLocalRing.maximalIdeal A := by
    by_contra hc
    exact h ((IsLocalRing.notMem_maximalIdeal).mp hc)
  have h0 : (IsLocalRing.residue A) (n : A) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [map_natCast] at h0
  exact (Nat.cast_ne_zero.mpr hn) h0

/-- A natural number which is nonzero and which lies in the image of `ℕ → A` dies in no
localization-compatible way: it is invertible.  This is the form in which the Euler
characteristic `χ = [K(X):K]` of the trace argument is used. -/
theorem isUnit_of_ne_zero_natCast [CharZero (IsLocalRing.ResidueField A)]
    (χ : ℕ) (hχ : χ ≠ 0) : IsUnit ((χ : A)) :=
  isUnit_natCast_of_charZero_residueField hχ

/-- The unit of `A` whose underlying element is a nonzero natural number, when the residue
field has characteristic zero.  This is the form in which the inverse of the Euler
characteristic `χ = [K(X):K]` is available. -/
noncomputable def unitOfNatCast [CharZero (IsLocalRing.ResidueField A)]
    (n : ℕ) (hn : n ≠ 0) : Aˣ :=
  (isUnit_natCast_of_charZero_residueField (A := A) hn).unit

@[simp]
theorem coe_unitOfNatCast [CharZero (IsLocalRing.ResidueField A)]
    (n : ℕ) (hn : n ≠ 0) : ((unitOfNatCast (A := A) n hn : Aˣ) : A) = (n : A) :=
  IsUnit.unit_spec _

end CharZero

section Splitting

open DSMap

variable (A : Type u) [CommRing A]

/-- A splitting of the challenge unit in the derived category is exactly the data of a
retraction. -/
theorem isSplitMono_rgUnit_iff [HasDerivedCategory (ModuleCat.{u} A)] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] :
    IsSplitMono (rgUnit A X f) ↔
      ∃ r : RG A X f ⟶ (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A A), rgUnit A X f ≫ r = 𝟙 _ := by
  constructor
  · intro h
    obtain ⟨⟨r, hr⟩⟩ := h.exists_splitMono
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    exact IsSplitMono.mk' ⟨r, hr⟩

/-- Version in the form `rgUnit ≫ r = 𝟙` producing `IsSplitMono`. -/
theorem isSplitMono_of_retraction [HasDerivedCategory (ModuleCat.{u} A)] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    (r : RG A X f ⟶ (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A A))
    (hr : rgUnit A X f ≫ r = 𝟙 _) : IsSplitMono (rgUnit A X f) :=
  IsSplitMono.mk' ⟨r, hr⟩

/-- `DSplit` follows from a splitting at one fixed choice of the derived-category
instances, provided the instances are given.  Stated in the exact shape needed to
feed `DSplit`: it removes the two universal quantifiers. -/
theorem dsplit_of_isSplitMono (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (h : ∀ (_ : HasDerivedCategory.{w₁} (ModuleCat.{u} A))
      (_ : HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)), IsSplitMono (rgUnit A X f)) :
    DSplit.{u, w₁, w₂} A X f := h

/-- If the challenge unit is an isomorphism then it is a split mono. -/
theorem isSplitMono_of_isIso_rgUnit [HasDerivedCategory (ModuleCat.{u} A)] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] [IsIso (rgUnit A X f)] :
    IsSplitMono (rgUnit A X f) :=
  IsSplitMono.of_iso _

end Splitting

end Work.DSEQ0
