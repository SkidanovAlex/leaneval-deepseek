/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The boundary of the chapter: `NK.ResidueFrob.LocalStructureData` at every place

This is the *usable* boundary of `NK.TameStructureDeep`: the hypotheses of the place-level
theorems of `Submission/Work/ResidueFrob/` — `NK.ResidueFrob.LocalStructureData` and
`NK.ResidueFrob.TameDataInputs` — are produced from the single residual
`NK.TameStructureDeep.TameRamificationCore` at each place together with the residue-character
detector `NK.LocalTame.Zl2ResidueChar` (which the sibling theorem
`NK.Mine.zl2ResidueChar_adicCompletion` discharges from local class field theory; see
`localStructureData_of_zl2ResidueChar` below).

Nothing else is assumed: the residue characteristic `p` is a parameter pinned by `CharP` of the
residue field (`NK.Mine.charP_ringChar_residueField_adicCompletion` fixes the *canonical*
choice `p = ringChar`), the residue cardinality is `NK.LocalStructure.residueCard K 𝔭` and is
*proved* to be a power of `p` (`NK.TameStructureDeep.q_eq_of_charP`), and every other field of
`NK.LocalStructure.TameCore`, `NK.TameData.TameAbelianisationInput`,
`NK.TameData.TameTorsionInput` and `NK.LocalStructure.TameFrobeniusCore` is a theorem.
-/
import Submission.NK.TameStructureDeep.Data
import Submission.NK.ResidueFrob.LocalStructureInputs
import Submission.NK.Mine.zl2ResidueChar_adicCompletion
import Submission.NK.Mine.ResidueCharAutomatic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructureDeep

universe u

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The local structure theorem at a place, from the residual.**

For a place `A` of `K'` over a finite prime `𝔭` of `K` and `p` a prime with
`CharP (ResidueField (𝒪_κ)) p` at the completion `κ = K_𝔭`, the residual
`NK.TameStructureDeep.TameRamificationCore p (residueCard K 𝔭) κ (localClosure A)` together with
Shimizu's residue-character detector `NK.LocalTame.Zl2ResidueChar p κ (localClosure A)` produce
`NK.ResidueFrob.LocalStructureData K K' A` — input (iii) of the Neukirch–Uchida endgame. -/
theorem localStructureData_of (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField
      ((NK.TameData.primeBelow A).adicCompletionIntegers K)) p)
    (h : TameRamificationCore p (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (hZ : NK.LocalTame.Zl2ResidueChar p (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A)) :
    NK.ResidueFrob.LocalStructureData K K' A :=
  ⟨p, tameCore_adicCompletion (NK.TameData.primeBelow A) hchar h,
    tameAbelianisationInput_adicCompletion (NK.TameData.primeBelow A) hchar h,
    tameFrobeniusCore_adicCompletion (NK.TameData.primeBelow A) h,
    hZ⟩

/-- The residue characteristic of the local field of a place, as a function of the place: the
canonical choice `p = ringChar (ResidueField (𝒪_κ))`, known to be prime by
`NK.Mine.prime_ringChar_residueField_adicCompletion`. -/
noncomputable def residueCharAt (A : NK.FrobeniusBridge.FinitePlaceOf K K') : ℕ :=
  ringChar (IsLocalRing.ResidueField ((NK.TameData.primeBelow A).adicCompletionIntegers K))

/-- The canonical `CharP` datum at the residue field of the local field of a place. -/
theorem charP_residueCharAt (A : NK.FrobeniusBridge.FinitePlaceOf K K') :
    CharP (IsLocalRing.ResidueField ((NK.TameData.primeBelow A).adicCompletionIntegers K))
      (residueCharAt A) :=
  NK.Mine.charP_ringChar_residueField_adicCompletion (NK.TameData.primeBelow A)

/-- The canonical residue characteristic of the local field of a place is prime. -/
theorem prime_residueCharAt (A : NK.FrobeniusBridge.FinitePlaceOf K K') :
    (residueCharAt A).Prime :=
  NK.Mine.prime_ringChar_residueField_adicCompletion (NK.TameData.primeBelow A)

/-- **The local structure theorem at every place**, from the residual at every place — the
hypothesis of `NK.ResidueFrob.frobeniusCorrespondencePlace_of_localStructureData`.  The residue
characteristic is the canonical `ringChar` of the residue field at each place, so `CharP` is
*not* a hypothesis (`charP_residueCharAt`). -/
theorem localStructureData_of_all
    (h : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K',
      TameRamificationCore (residueCharAt A)
        (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (hZ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K',
      NK.LocalTame.Zl2ResidueChar (residueCharAt A)
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A)) :
    ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K', NK.ResidueFrob.LocalStructureData K K' A :=
  fun A => localStructureData_of A (charP_residueCharAt A) (h A) (hZ A)

/-- **The weakest local structure inputs at a place** (`NK.ResidueFrob.TameDataInputs`) from the
residual, `TameDataInputs` being the `NK.TameData.TameDataInput`-form of the same data. -/
theorem tameDataInputs_of_core (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField
      ((NK.TameData.primeBelow A).adicCompletionIntegers K)) p)
    (h : TameRamificationCore p (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (hZ : NK.LocalTame.Zl2ResidueChar p (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A)) :
    NK.ResidueFrob.TameDataInputs K K' A :=
  ⟨p, tameDataInput_adicCompletion (NK.TameData.primeBelow A) hchar h, hZ⟩

section Endgame

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The endgame instantiation: leaf (iii) of the Neukirch–Uchida endgame from the residual.**

The hypotheses `hD₁`, `hD₂` *and* `hTame` of
`NK.FrobeniusBridge.frobeniusCorrespondencePlace_of_tameData_atPlaces` — i.e. the local–global
Frob̀enius dictionary at every place of the two fields — are discharged by the local structure
theory of this chapter: at each place, the residual `TameRamificationCore` together with the
residue-character detector `Zl2ResidueChar` produce `NK.ResidueFrob.LocalStructureData`, and
`NK.ResidueFrob.frobeniusCorrespondencePlace_of_localStructureData` (a sibling theorem of
`Submission/Work/ResidueFrob/`) converts those to the σ-free finite-level Frobenius
correspondence.  The only hypotheses left are per-place instances of the classical local
structure theorem.

The residue characteristic is pinned to `ringChar (ResidueField (𝔭.adicCompletionIntegers K))`,
whose `CharP` and primeness are *proved* (`charP_residueCharAt`, `prime_residueCharAt`), so it is
not a hypothesis here. -/
theorem frobeniusCorrespondencePlace_of_core
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
      TameRamificationCore (ringChar (IsLocalRing.ResidueField
          ((NK.TameData.primeBelow A).adicCompletionIntegers K₁)))
        (NK.LocalStructure.residueCard K₁ (NK.TameData.primeBelow A))
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A) ∧
      NK.LocalTame.Zl2ResidueChar (ringChar (IsLocalRing.ResidueField
          ((NK.TameData.primeBelow A).adicCompletionIntegers K₁)))
        (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
      TameRamificationCore (ringChar (IsLocalRing.ResidueField
          ((NK.TameData.primeBelow B).adicCompletionIntegers K₂)))
        (NK.LocalStructure.residueCard K₂ (NK.TameData.primeBelow B))
        (NK.FrobeniusBridge.localField B) (NK.FrobeniusBridge.localClosure B) ∧
      NK.LocalTame.Zl2ResidueChar (ringChar (IsLocalRing.ResidueField
          ((NK.TameData.primeBelow B).adicCompletionIntegers K₂)))
        (NK.FrobeniusBridge.localField B) (NK.FrobeniusBridge.localClosure B)) :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a :=
  NK.ResidueFrob.frobeniusCorrespondencePlace_of_localStructureData ϕ hϕ a
    (fun A => localStructureData_of A (charP_residueCharAt A) (h₁ A).1 (h₁ A).2)
    (fun B => localStructureData_of B (charP_residueCharAt B) (h₂ B).1 (h₂ B).2)

end Endgame

/-! ## Discharging the residue-character detector

`NK.LocalTame.Zl2ResidueChar p κ K'` (Shimizu, arXiv:2009.10431, Lemma 2.1) is *not* part of the
local ramification theory of this chapter: it is local class field theory.  The sibling theorem
`NK.Mine.zl2ResidueChar_adicCompletion` reduces it to an `ArtinReciprocity` datum for `κ`,
openness of the index-`ℓ` normal subgroups (Nikolov–Segal), and Shimizu's `ℤ_ℓ²`-detection for the
units.  We record the resulting version of the boundary theorem, so that a caller who has those
inputs never has to mention `Zl2ResidueChar`. -/

/-- **The local structure theorem at a place, with the residue-character detector discharged** by
`NK.Mine.zl2ResidueChar_adicCompletion` from an `ArtinReciprocity` datum, openness of index-`ℓ`
normal subgroups, and the `ℤ_ℓ²`-detection for the profinite completion of the unit group. -/
theorem localStructureData_of_zl2ResidueChar (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p : ℕ}
    (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField
      ((NK.TameData.primeBelow A).adicCompletionIntegers K)) p)
    (h : TameRamificationCore p (NK.LocalStructure.residueCard K (NK.TameData.primeBelow A))
      (NK.FrobeniusBridge.localField A) (NK.FrobeniusBridge.localClosure A))
    (D : NK.LocalCFT.ArtinReciprocity (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A))
    (hopen : ∀ (ℓ : ℕ), ℓ.Prime →
      ∀ H : Subgroup (Gal((NK.FrobeniusBridge.localClosure A) /
        (NK.FrobeniusBridge.localField A))), H.index = ℓ → H.Normal →
        IsOpen (H : Set (Gal((NK.FrobeniusBridge.localClosure A) /
          (NK.FrobeniusBridge.localField A)))))
    (hU : NK.LocalTame.HasZl2Quotient p
      (NK.LocalReciprocity.completionUnits (NK.FrobeniusBridge.localField A)))
    (hU' : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ¬ NK.LocalTame.HasZl2Quotient ℓ
      (NK.LocalReciprocity.completionUnits (NK.FrobeniusBridge.localField A))) :
    NK.ResidueFrob.LocalStructureData K K' A :=
  localStructureData_of A hchar h
    (NK.Mine.zl2ResidueChar_adicCompletion (NK.TameData.primeBelow A) hp hchar
      (NK.FrobeniusBridge.localClosure A) D hopen hU hU')

end

end NK.TameStructureDeep
