import Mathlib
import Submission.Work.SSGRoute.isOpen_map_fixingSubgroupEquiv
import Submission.Work.SSGRoute.hom_ext_of_eqOn_subgroup_of_index_lt
import Submission.Work.SSGRoute.isOpen_ker_comp_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of open-kernel homomorphisms descends along a restriction

`Work.SSGRoute.finite_homs_of_restriction`: for a Galois extension `Ω/κ`, a finite intermediate
field `L` of degree `< l` (`l` prime) and any group `M`, the open-kernel homomorphisms
`Gal(Ω/κ) →* Multiplicative (ZMod l)` are finite as soon as those on `Gal(Ω/↥L)` are.

The map `χ ↦ χ.comp (GalRestrict L)` is injective on homomorphisms: two homs agreeing on the image
of `Gal(Ω/↥L)` agree on `L.fixingSubgroup`, and the difference then has range a subgroup of a group
of order `l` whose index is `≤ [Gal(Ω/κ) : L.fixingSubgroup] = finrank κ L < l`, forcing it to be
trivial.  It also preserves openness of the kernel, so it restricts to an injection between the
subtypes, and the target subtype is finite by hypothesis.
-/

namespace Work.SSGRoute

open scoped Topology

/-- The restriction homomorphism `Gal(Ω/↥L) →* Gal(Ω/κ)`: an `↥L`-algebra automorphism of `Ω` is
in particular a `κ`-algebra automorphism.  Realised through
`IntermediateField.fixingSubgroupEquiv`. -/
abbrev GalRestrict {κ Ω : Type*} [Field κ] [Field Ω] [Algebra κ Ω]
    (L : IntermediateField κ Ω) : Gal(Ω/↥L) →* Gal(Ω/κ) :=
  (Subgroup.subtype L.fixingSubgroup).comp
    (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom

lemma GalRestrict_apply {κ Ω : Type*} [Field κ] [Field Ω] [Algebra κ Ω]
    (L : IntermediateField κ Ω) (σ : Gal(Ω/↥L)) :
    GalRestrict L σ = ((IntermediateField.fixingSubgroupEquiv L).symm σ : Gal(Ω/κ)) := rfl

/-- `GalRestrict L` sends the image of `τ ∈ L.fixingSubgroup` back to `τ`. -/
lemma GalRestrict_fixingSubgroupEquiv_apply {κ Ω : Type*} [Field κ] [Field Ω] [Algebra κ Ω]
    (L : IntermediateField κ Ω) (τ : ↥L.fixingSubgroup) :
    GalRestrict L (IntermediateField.fixingSubgroupEquiv L τ) = (τ : Gal(Ω/κ)) := by
  rw [GalRestrict_apply, MulEquiv.symm_apply_apply]

/-- `Multiplicative (ZMod l)` has `l` elements. -/
lemma natCard_multiplicative_zmod (l : ℕ) [NeZero l] :
    Nat.card (Multiplicative (ZMod l)) = l := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

/-- **Finiteness of open-kernel homomorphisms descends along a restriction with prime-to-`l`
degree.**  `Ω/κ` a Galois extension, `L/κ` finite of degree `< l` (`l` prime) inside `Ω`.  If the
open-kernel homomorphisms `Gal(Ω/↥L) →* Multiplicative (ZMod l)` are finite, then so are those on
`Gal(Ω/κ)`. -/
theorem finite_homs_of_restriction {κ Ω : Type*} [Field κ] [Field Ω] [Algebra κ Ω] [IsGalois κ Ω]
    (L : IntermediateField κ Ω) [FiniteDimensional κ L] (l : ℕ) (hl : l.Prime)
    (hdeg : Module.finrank κ L < l)
    (h : Finite {ψ : Gal(Ω/↥L) →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set Gal(Ω/↥L))}) :
    Finite {χ : Gal(Ω/κ) →* Multiplicative (ZMod l) // IsOpen (χ.ker : Set Gal(Ω/κ))} := by
  have hFinβ : Finite {ψ : Gal(Ω/↥L) →* Multiplicative (ZMod l) //
      IsOpen (ψ.ker : Set Gal(Ω/↥L))} := h
  have hne : NeZero l := ⟨hl.ne_zero⟩
  have hfin : L.fixingSubgroup.index = Module.finrank κ L :=
    (IntermediateField.finrank_eq_fixingSubgroup_index Ω L).symm
  have hidx : L.fixingSubgroup.index < l := by rw [hfin]; exact hdeg
  have hpos : L.fixingSubgroup.index ≠ 0 := by
    rw [hfin]; exact ne_of_gt (Module.finrank_pos : 0 < Module.finrank κ L)
  refine Finite.of_injective
    (fun χ : {χ : Gal(Ω/κ) →* Multiplicative (ZMod l) // IsOpen (χ.ker : Set Gal(Ω/κ))} =>
      (⟨χ.1.comp (GalRestrict L), isOpen_ker_comp_restrict L χ.1 χ.2⟩ :
        {ψ : Gal(Ω/↥L) →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set Gal(Ω/↥L))})) ?_
  rintro ⟨χ₁, hχ₁⟩ ⟨χ₂, hχ₂⟩ hab
  have hcomp : χ₁.comp (GalRestrict L) = χ₂.comp (GalRestrict L) := by
    simpa using congrArg Subtype.val hab
  apply Subtype.ext
  refine hom_ext_of_eqOn_subgroup_of_index_lt L.fixingSubgroup l hl
    (natCard_multiplicative_zmod l) hpos hidx ?_
  intro τ hτ
  have h1 : GalRestrict L (IntermediateField.fixingSubgroupEquiv L ⟨τ, hτ⟩) = τ :=
    GalRestrict_fixingSubgroupEquiv_apply L ⟨τ, hτ⟩
  have key : ∀ χ : Gal(Ω/κ) →* Multiplicative (ZMod l),
      χ τ = (χ.comp (GalRestrict L)) (IntermediateField.fixingSubgroupEquiv L ⟨τ, hτ⟩) := by
    intro χ
    rw [MonoidHom.comp_apply, h1]
  rw [key χ₁, key χ₂, hcomp]

end Work.SSGRoute
