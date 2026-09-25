import Mathlib
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement

/-!
# The norm class subgroup of the maximal abelian subextension

Let `K ⊆ F` be a finite Galois extension of number fields with group `G = Gal(F/K)`.  The fixed
field `M = F^{[G,G]}` of the derived subgroup (written `⁅⊤,⊤⁆` in Lean) is the maximal abelian
subextension of `F/K`, and its norm class subgroup `N_{M/K} C_M ≤ C_K` is the same as the norm
class subgroup `N_{F/K} C_F` of the whole extension.

Both inclusions are elementary in one direction: `N_{F/K} C_F ≤ N_{M/K} C_M` is the tower
property (`NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower`), and the reverse inclusion follows
because the two subgroups have the same (finite) index.  The index of `N_{L/K} C_L` is the order
of the abelianisation `Gal(L/K)^{ab}` (`Norm index theorem`, derived here from the single
arithmetic input `NK.GlobalCFTdeep.FundamentalClassElement`, see
`NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement`), and
`Gal(M/K) ≅ G/⁅⊤,⊤⁆ = Gal(F/K)^{ab}` by the Galois correspondence for normal subgroups.

This is the norm limitation theorem (Milne, *Class Field Theory*, Theorem 4.8) in the special
case `E = F` (where `E.fixingSubgroup = ⊥`): `N_{F/K}C_F = N_{L/K}C_L` for the maximal abelian
subextension `L = F^{[G,G]}`.  The proof below needs no Frobenius normalisation of the Artin map,
and no transfer: it uses only the norm index theorem for the two Galois levels `F/K` and `L/K`,
which is available from `hFC` as
`NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement`.
-/

namespace NK.NUV2.TowerRank

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **Two subgroups of a group with a common finite index, one contained in the other, are
equal.** -/
private theorem subgroup_eq_of_le_of_index_eq {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B)
    (hidx : A.index = B.index) (hne : A.index ≠ 0) : A = B := by
  have hmul : A.relIndex B * B.index = A.index := Subgroup.relIndex_mul_index h
  have hB : B.index ≠ 0 := by rw [← hidx]; exact hne
  have h1 : A.relIndex B * B.index = 1 * B.index := by rw [one_mul, hmul, hidx]
  exact le_antisymm h (Subgroup.relIndex_eq_one.mp
    (Nat.mul_right_cancel (Nat.pos_of_ne_zero hB) h1))

/-- **The norm class subgroup of the maximal abelian subextension.**  For `K ⊆ F` finite Galois
with group `G`, the norm class subgroup of the fixed field of the derived subgroup `⁅⊤,⊤⁆ = [G,G]`
agrees with the norm class subgroup of `F`. -/
theorem normClassSubgroup_fixedField_commutator (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F] :
    NK.GlobalCFT.Idele.normClassSubgroup K ↥(IntermediateField.fixedField
        (⁅(⊤ : Subgroup (F ≃ₐ[K] F)), (⊤ : Subgroup (F ≃ₐ[K] F))⁆)) =
      NK.GlobalCFT.Idele.normClassSubgroup K F := by
  classical
  -- rewrite the derived subgroup as `commutator G` (a definitional unfolding)
  change NK.GlobalCFT.Idele.normClassSubgroup K ↥(IntermediateField.fixedField
      (commutator (F ≃ₐ[K] F))) = NK.GlobalCFT.Idele.normClassSubgroup K F
  -- the fixed field `M = F^{[G,G]}` is a number field, finite and Galois over `K`
  letI : NumberField ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))) := inferInstance
  letI : FiniteDimensional K ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))) :=
    inferInstance
  letI : IsGalois K ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))) := inferInstance
  -- the tower `K ⊆ M ⊆ F`
  letI : Algebra ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))) F := inferInstance
  letI :
      IsScalarTower K ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))) F := inferInstance
  letI :
      FiniteDimensional ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))) F := inferInstance
  -- the elementary inclusion `N_{F/K}C_F ≤ N_{M/K}C_M`
  have hle : NK.GlobalCFT.Idele.normClassSubgroup K F ≤
      NK.GlobalCFT.Idele.normClassSubgroup K
        ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))) :=
    NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower (K := K)
      (L := ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F)))) (M := F)
  -- the norm index of `F/K`
  have hidx1 : (NK.GlobalCFT.Idele.normClassSubgroup K F).index =
      Nat.card (Abelianization (F ≃ₐ[K] F)) :=
    NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement hFC
      (K := K) (L := F)
  -- the norm index of `M/K`
  have hidx2 : (NK.GlobalCFT.Idele.normClassSubgroup K
        ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F)))).index =
      Nat.card (Abelianization (↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))) ≃ₐ[K]
        ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))))) :=
    NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement hFC
      (K := K) (L := ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))))
  -- `Abelianization Gal(M/K) ≅ Abelianization (G ⧸ [G,G]) ≅ Abelianization G`
  have hcard : Nat.card (Abelianization
        (↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))) ≃ₐ[K]
          ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))))) =
      Nat.card (Abelianization (F ≃ₐ[K] F)) := by
    have e : (F ≃ₐ[K] F) ⧸ commutator (F ≃ₐ[K] F) ≃*
        (↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))) ≃ₐ[K]
          ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F)))) :=
      IsGalois.normalAutEquivQuotient (K := K) (L := F) (commutator (F ≃ₐ[K] F))
    have h1 : Nat.card (Abelianization ((F ≃ₐ[K] F) ⧸ commutator (F ≃ₐ[K] F))) =
        Nat.card (Abelianization
          (↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))) ≃ₐ[K]
            ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F))))) :=
      Nat.card_congr e.abelianizationCongr.toEquiv
    -- `G ⧸ [G,G]` is commutative, hence is its own abelianisation
    haveI : IsMulCommutative ((F ≃ₐ[K] F) ⧸ commutator (F ≃ₐ[K] F)) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
    have hbot : commutator ((F ≃ₐ[K] F) ⧸ commutator (F ≃ₐ[K] F)) = ⊥ := commutator_eq_bot _
    have h2 : Nat.card (Abelianization ((F ≃ₐ[K] F) ⧸ commutator (F ≃ₐ[K] F))) =
        Nat.card (Abelianization (F ≃ₐ[K] F)) := by
      have h3 : Nat.card (Abelianization ((F ≃ₐ[K] F) ⧸ commutator (F ≃ₐ[K] F))) =
          Nat.card (((F ≃ₐ[K] F) ⧸ commutator (F ≃ₐ[K] F)) ⧸ ⊥) :=
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hbot).toEquiv
      have h4 : Nat.card (((F ≃ₐ[K] F) ⧸ commutator (F ≃ₐ[K] F)) ⧸ ⊥) =
          Nat.card ((F ≃ₐ[K] F) ⧸ commutator (F ≃ₐ[K] F)) :=
        Nat.card_congr QuotientGroup.quotientBot.toEquiv
      -- `Abelianization G` *is* `G ⧸ commutator G`
      exact h3.trans (h4.trans rfl)
    exact h1.symm.trans h2
  -- both indices are finite (they are cardinals of the finite abelianisations)
  have hneA : (NK.GlobalCFT.Idele.normClassSubgroup K F).index ≠ 0 := by
    rw [hidx1]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  -- equal finite indices and the inclusion give the equality
  have hAB : (NK.GlobalCFT.Idele.normClassSubgroup K F).index =
      (NK.GlobalCFT.Idele.normClassSubgroup K
        ↥(IntermediateField.fixedField (commutator (F ≃ₐ[K] F)))).index :=
    hidx1.trans (hcard.symm.trans hidx2.symm)
  exact (subgroup_eq_of_le_of_index_eq hle hAB hneA).symm

end NK.NUV2.TowerRank
