import Mathlib
import Submission.Work.DSMap.Map

/-!
# DSG4b — gonflement: vocabulary

The frozen interface `DSMap.area_G4b_gonflement` (EGA 0_III 10.3.1; André's *gonflement*;
Česnavičius, *Purity for the Brauer group*, Lemma 5.1) says:

> A regular (Noetherian) ring `A` and a maximal ideal `m ⊂ A` admit a flat ring map `ψ : A →+* A'`
> with `A'` a complete regular local ring, algebraically closed residue field, and the maximal
> ideal of `A'` lying over `m`.

This file fixes the vocabulary of the area; the construction is in
`Submission/Work/DSG4b/Main.lean`.
-/

namespace Work.DSG4b

open IsLocalRing

universe u v

/-- `ψ : A →+* A'` exhibits `A'` as a **gonflement** of `A` at `m` when `A'` is a complete regular
local ring with algebraically closed residue field, `ψ` is flat, and `maximalIdeal A'` lies over
`m`.  This is exactly the conclusion of `DSMap.area_G4b_gonflement`. -/
def IsGonflement {A : Type u} [CommRing A] (m : Ideal A) (A' : Type u) [CommRing A']
    [IsLocalRing A'] (ψ : A →+* A') : Prop :=
  IsRegularLocalRing A' ∧ IsAdicComplete (maximalIdeal A') A' ∧ IsAlgClosed (ResidueField A') ∧
    ψ.Flat ∧ (maximalIdeal A').comap ψ = m

variable {A : Type u} [CommRing A]

section Basic

variable {m : Ideal A} {A' : Type u} [CommRing A'] [IsLocalRing A'] {ψ : A →+* A'}

theorem IsGonflement.isRegularLocal (h : IsGonflement m A' ψ) : IsRegularLocalRing A' := h.1
theorem IsGonflement.isAdicComplete (h : IsGonflement m A' ψ) :
    IsAdicComplete (maximalIdeal A') A' := h.2.1
theorem IsGonflement.isAlgClosed (h : IsGonflement m A' ψ) : IsAlgClosed (ResidueField A') :=
  h.2.2.1
theorem IsGonflement.flat (h : IsGonflement m A' ψ) : ψ.Flat := h.2.2.2.1
theorem IsGonflement.comap_maximalIdeal (h : IsGonflement m A' ψ) :
    (maximalIdeal A').comap ψ = m := h.2.2.2.2

end Basic

end Work.DSG4b
