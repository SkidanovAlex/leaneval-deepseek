import Mathlib
import Submission.Commons.GroupTheory.SpecificGroups.Cyclic.subgroup_eq_of_card_eq
import Submission.NK.LocalCFT.NormGroup.normGroup_le_iff
import Submission.NK.LocalCFT.NormGroup.normGroup_eq_iff
import Submission.NK.LocalCFT.Reduction.Defs
import Submission.NK.LocalArtin.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A reciprocity map at a cyclic level kills norms

The classical statement (*"the Artin symbol kills norms"*, Serre, *Local Fields*, Ch. XI §2, XV §5.2;
Neukirch, *Algebraic Number Theory*, V.5.5) is, at a finite abelian level `E/F`:

> for a reciprocity map `Φ : Fˣ ↠ Gal(E/F)` with kernel `N_{E/F} Eˣ`, and every intermediate
  `L ≤ E`:  `Φ(N_{L/F} Lˣ) = Gal(E/L)`, i.e. every `x ∈ N_{L/F} Lˣ` has `Φ(x)|_L = 1`.

This file proves it **whenever `Gal(E/F)` is cyclic**, in a form that mentions no Lubin–Tate theory:
the only inputs are that `Φ` is a surjection with kernel `N_E` (the reciprocity isomorphism at the top
level) and the norm index theorem at every level.  The argument is by cardinality: `Φ(N_L)` and the
stabiliser of `L` are subgroups of `Gal(E/F)` of the same cardinality `[E : L]`, and a cyclic group has
at most one subgroup of a given order.

This is the form in which the theorem is used for the canonical Lubin–Tate symbols
(`NK.LocalReciprocityLubinTate.normInKernel_of_level_isCyclic` is the tower-level restatement, and
`NK.LocalReciprocityLubinTate.LubinTate.exists_ltSymbol_family` supplies the symbols with the required
kernel `⟨π⟩U^n = N_{F(Λ_n)/F}` by Honda's reciprocity law).

## Main result

* `NK.LocalReciprocityLubinTate.normGroup_map_eq_of_isCyclic`.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u v

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **A reciprocity map at a cyclic level kills norms.**

Let `E` be a finite abelian level of `F^{ab}`, `Φ : Fˣ →* Gal(E/F)` a surjection with kernel
`N_{E/F} Eˣ` (the reciprocity isomorphism at the top level), and assume the norm index theorem at every
intermediate level (`NK.LocalArtin.NormIndex`; a theorem of this chapter for `Q.adicCompletion K`).
If `Gal(E/F)` is **cyclic**, then for every finite abelian subfield `L ≤ E` and every
`x ∈ N_{L/F} Lˣ`, the automorphism `Φ x` fixes `L` pointwise. -/
theorem normGroup_map_eq_of_isCyclic
    (hidx : NK.LocalArtin.NormIndex F F')
    (E : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F E] [Normal F E]
    (Φ : Fˣ →* (↥E ≃ₐ[F] ↥E)) (hsurj : Function.Surjective Φ)
    (hker : MonoidHom.ker Φ = NK.LocalReciprocity.normGroup F ↥E)
    (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E))
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L] (hLE : L ≤ E) :
    ∀ x ∈ NK.LocalReciprocity.normGroup F ↥L,
      ∀ y : ↥L, (Φ x) ⟨y.1, hLE y.2⟩ = ⟨y.1, hLE y.2⟩ := by
  classical
  haveI hgalE : IsGalois F ↥E := NK.LocalCFT.NormGroup.instIsGaloisLevelOfMaxAbelian E
  letI : Algebra ↥L ↥E := RingHom.toAlgebra (Subsemiring.inclusion hLE)
  haveI hSTL : IsScalarTower F ↥L ↥E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  have hle : NK.LocalReciprocity.normGroup F ↥E ≤ NK.LocalReciprocity.normGroup F ↥L :=
    NK.LocalCFT.normGroup_le_of_le hLE
  -- ### the image of the norm group has the cardinality of `Gal(E/L)`
  have hcardA : Nat.card ↥(Subgroup.map Φ (NK.LocalReciprocity.normGroup F ↥L)) *
      Module.finrank F ↥L = Module.finrank F ↥E := by
    have h1 : Subgroup.map Φ (NK.LocalReciprocity.normGroup F ↥L) =
        (Φ.comp (NK.LocalReciprocity.normGroup F ↥L).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.subtype_range]
    have hkercomp : (Φ.comp (NK.LocalReciprocity.normGroup F ↥L).subtype).ker =
        (NK.LocalReciprocity.normGroup F ↥E).subgroupOf
          (NK.LocalReciprocity.normGroup F ↥L) := by
      ext z
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, ← hker,
        MonoidHom.mem_ker]
      rfl
    have h2 : Nat.card ↥(Subgroup.map Φ (NK.LocalReciprocity.normGroup F ↥L)) =
        (NK.LocalReciprocity.normGroup F ↥E).relIndex
          (NK.LocalReciprocity.normGroup F ↥L) := by
      rw [h1, ← Subgroup.index_ker, hkercomp]
      rfl
    rw [h2, ← hidx L, Subgroup.relIndex_mul_index hle, hidx E]
  -- ### the stabiliser of `L` has the same cardinality
  have hcardB : Nat.card ↥(Subgroup.comap
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥E) ↥L) ⊥) *
      Module.finrank F ↥L = Module.finrank F ↥E := by
    have hkerL : (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥E) ↥L).ker =
        Subgroup.comap (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥E) ↥L) ⊥ := by
      ext σ
      rfl
    have hsurjL : Function.Surjective ⇑(AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥E) ↥L) :=
      AlgEquiv.restrictNormalHom_surjective ↥E
    have h2 : (Subgroup.comap (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥E) ↥L) ⊥).index =
        Module.finrank F ↥L := by
      rw [← hkerL, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurjL, Subgroup.card_top,
        IsGalois.card_aut_eq_finrank F ↥L]
    have h3 := Subgroup.card_mul_index
      (Subgroup.comap (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥E) ↥L) ⊥)
    rw [h2, IsGalois.card_aut_eq_finrank F ↥E] at h3
    exact h3
  -- ### the two subgroups agree by cyclicity
  have hcards : Nat.card ↥(Subgroup.map Φ (NK.LocalReciprocity.normGroup F ↥L)) =
      Nat.card ↥(Subgroup.comap (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥E) ↥L) ⊥) :=
    Nat.mul_right_cancel (Module.finrank_pos (R := F)) (by rw [hcardA, hcardB])
  have hAB : Subgroup.map Φ (NK.LocalReciprocity.normGroup F ↥L) =
      Subgroup.comap (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥E) ↥L) ⊥ :=
    Commons.GroupTheory.SpecificGroups.Cyclic.subgroup_eq_of_card_eq _ _ hcards
  intro x hx y
  have hxmem : Φ x ∈ Subgroup.comap (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥E) ↥L) ⊥ := by
    rw [← hAB]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hrn : ((Φ x).restrictNormal ↥L) = 1 := hxmem
  have happ := AlgEquiv.restrictNormal_commutes (χ := Φ x) (E := ↥L) y
  rw [hrn] at happ
  simp only [AlgEquiv.one_apply] at happ
  have hmap : (algebraMap ↥L ↥E) y = ⟨y.1, hLE y.2⟩ := rfl
  rw [← hmap]
  exact happ.symm

end NK.LocalReciprocityLubinTate
