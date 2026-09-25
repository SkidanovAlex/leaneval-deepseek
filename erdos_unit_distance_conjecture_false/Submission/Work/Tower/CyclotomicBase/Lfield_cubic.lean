import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicCubic

set_option linter.style.haveILetI false

namespace Work.Tower.CyclotomicBase

/-- The cubic subfield `Lᵢ ⊆ ℚ(ζ_D)` cut out by the `i`-th cubic character `χᵢ` has
degree `3` over `ℚ`, is Galois, and is totally real.

Indeed, `galCoord i : Gal(ℚ(ζ_D)/ℚ) → ℤ/3` is surjective (the `i`-th CRT component of a
unit can be prescribed independently), so its kernel has index `3`, and the Galois
correspondence for the abelian extension `ℚ(ζ_D)/ℚ` gives `[Lᵢ : ℚ] = 3` with `Lᵢ/ℚ` Galois.
A degree-`3` Galois extension of `ℚ` is totally real: complex conjugation at a non-real place
would give an element of order `2` in a Galois group of order `3`. -/
theorem Lfield_cubic {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1)
    [NeZero (D r)] (i : Fin ℓ) :
    Module.finrank ℚ ↥(Lfield r hr hr3 i) = 3 ∧ IsGalois ℚ ↥(Lfield r hr hr3 i) ∧
      NumberField.IsTotallyReal ↥(Lfield r hr hr3 i) := by
  haveI : IsCyclotomicExtension {D r} ℚ (Cyc r) := isCyclotomicExtension_cyc r
  haveI : IsGalois ℚ (Cyc r) := IsCyclotomicExtension.isGalois {D r} ℚ (Cyc r)
  -- The `i`-th coordinate character `galCoord i : Gal(ℚ(ζ_D)/ℚ) → ℤ/3` is surjective.
  have hsurj : Function.Surjective (galCoord r hr hr3 i) := by
    intro a
    obtain ⟨b, hb⟩ := coordChar_surjective r hr hr3 i a
    obtain ⟨σ, hσ⟩ := (galEquiv r).surjective b
    refine ⟨σ, ?_⟩
    have hgal : galCoord r hr hr3 i σ = coordChar r hr hr3 i ((galEquiv r) σ) := rfl
    rw [hgal, hσ]; exact hb
  -- Hence its kernel has index `3`.
  have hidx : (galCoord r hr hr3 i).ker.index = 3 := by
    rw [Subgroup.index_eq_card]
    have e := QuotientGroup.quotientKerEquivOfSurjective (galCoord r hr hr3 i) hsurj
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp
  -- The Galois correspondence: `[Lᵢ : ℚ]` equals the index of the kernel.
  have hfin : Module.finrank ℚ ↥(Lfield r hr hr3 i) = 3 := by
    show Module.finrank ℚ ↥(IntermediateField.fixedField (galCoord r hr hr3 i).ker) = 3
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (Cyc r) _,
      IntermediateField.fixingSubgroup_fixedField, hidx]
  haveI hg : IsGalois ℚ ↥(Lfield r hr hr3 i) :=
    IsGalois.of_fixedField_normal_subgroup (galCoord r hr hr3 i).ker
  exact ⟨hfin, hg, Work.Tower.isTotallyReal_of_isGalois_finrank_three _ hfin⟩

end Work.Tower.CyclotomicBase
