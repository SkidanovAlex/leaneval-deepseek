import Mathlib
import Submission.Work.SSGRoute.NKExistenceImport
import Submission.NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The maximal abelian subextension has the same norm class subgroup (norm limitation)

For a finite Galois extension `L / K` of number fields, we produce an intermediate field
`A ≤ L` with `A / K` abelian (indeed `Gal(A/K)` is commutative) and
`N_{A/K} C_A ≤ V` for any subgroup `V ≤ C_K` containing `N_{L/K} C_L`.

The proof is the "index form" of the *norm limitation theorem*: taking `A = L^{[G,G]}`
(the fixed field of the commutator subgroup of `G = Gal(L/K)`), the two norm class subgroups
`N_{L/K} C_L ≤ N_{A/K} C_A` by the tower property, while
`[C_K : N_{A/K}C_A] = |Gal(A/K)^{ab}| = |Gal(A/K)| = [A : K] = |G^{ab}| = |Gal(L/K)^{ab}|
 = [C_K : N_{L/K}C_L]` by the norm index theorem
(`NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement`).  Equal finite
index plus inclusion forces equality.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped IsMulCommutative
open NK.GlobalCFT

namespace Work.SSGRoute.CFTSide

/-- A subgroup with the same index as a containing subgroup is equal to it. -/
private theorem eq_of_le_of_index_eq {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B)
    (hidx : A.index = B.index) (hne : A.index ≠ 0) : A = B := by
  have hrel : A.relIndex B = 1 := by
    have hmul := Subgroup.relIndex_mul_index h
    rw [hidx] at hmul
    have hBpos : 0 < B.index := by rw [← hidx]; exact Nat.pos_of_ne_zero hne
    exact Nat.eq_of_mul_eq_mul_right hBpos (by rw [hmul, one_mul])
  have htop : A.subgroupOf B = ⊤ := by
    rw [← Subgroup.index_eq_one, ← Subgroup.relIndex]
    exact hrel
  exact le_antisymm h (Subgroup.subgroupOf_eq_top.mp htop)

theorem exists_abelian_subextension_normClassSubgroup_le
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K))
    (hle : NK.GlobalCFT.Idele.normClassSubgroup K L ≤ V) :
    ∃ A : IntermediateField K L, IsGalois K ↥A ∧ IsMulCommutative (↥A ≃ₐ[K] ↥A) ∧
      NK.GlobalCFT.Idele.normClassSubgroup K ↥A ≤ V := by
  classical
  -- the commutator subgroup of `G = Gal(L/K)` and its fixed field
  haveI hCnorm : Subgroup.Normal ⁅(⊤ : Subgroup (L ≃ₐ[K] L)), ⊤⁆ :=
    Subgroup.commutator_normal ⊤ ⊤
  let A : IntermediateField K L := IntermediateField.fixedField ⁅(⊤ : Subgroup (L ≃ₐ[K] L)), ⊤⁆
  haveI hAgal : IsGalois K ↥A :=
    IsGalois.of_fixedField_normal_subgroup ⁅(⊤ : Subgroup (L ≃ₐ[K] L)), ⊤⁆
  haveI hQuot : IsMulCommutative ((L ≃ₐ[K] L) ⧸ ⁅(⊤ : Subgroup (L ≃ₐ[K] L)), ⊤⁆) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := ⁅(⊤ : Subgroup (L ≃ₐ[K] L)), ⊤⁆)).mpr le_rfl
  -- `Gal(A/K)` is a quotient of the commutative group `G ⧸ [G,G]`
  have hAcomm : IsMulCommutative (↥A ≃ₐ[K] ↥A) :=
    IsMulCommutative.of_comm (fun a b => by
      obtain ⟨x, rfl⟩ :=
        (IsGalois.normalAutEquivQuotient ⁅(⊤ : Subgroup (L ≃ₐ[K] L)), ⊤⁆).surjective a
      obtain ⟨y, rfl⟩ :=
        (IsGalois.normalAutEquivQuotient ⁅(⊤ : Subgroup (L ≃ₐ[K] L)), ⊤⁆).surjective b
      rw [← map_mul, ← map_mul, mul_comm'])
  haveI : IsMulCommutative (↥A ≃ₐ[K] ↥A) := hAcomm
  refine ⟨A, hAgal, hAcomm, ?_⟩
  -- the two norm indices agree
  have hcardA : Nat.card (Abelianization (↥A ≃ₐ[K] ↥A)) = Nat.card (Abelianization (L ≃ₐ[K] L)) := by
    have h1 : Nat.card (Abelianization (↥A ≃ₐ[K] ↥A)) = Nat.card (↥A ≃ₐ[K] ↥A) :=
      (Nat.card_congr (Abelianization.equivOfComm (H := (↥A ≃ₐ[K] ↥A))).toEquiv).symm
    have h2 : Nat.card (↥A ≃ₐ[K] ↥A) =
        Nat.card ((L ≃ₐ[K] L) ⧸ ⁅(⊤ : Subgroup (L ≃ₐ[K] L)), ⊤⁆) :=
      (Nat.card_congr (IsGalois.normalAutEquivQuotient
        ⁅(⊤ : Subgroup (L ≃ₐ[K] L)), ⊤⁆).toEquiv).symm
    rw [h1, h2]
    rfl
  have hidxeq : (NK.GlobalCFT.Idele.normClassSubgroup K ↥A).index =
      (NK.GlobalCFT.Idele.normClassSubgroup K L).index := by
    rw [NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement hFC
          (K := K) (L := ↥A),
        NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement hFC
          (K := K) (L := L)]
    exact hcardA
  have hle' : NK.GlobalCFT.Idele.normClassSubgroup K L ≤ NK.GlobalCFT.Idele.normClassSubgroup K ↥A :=
    NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower (K := K) (L := ↥A) (M := L)
  have hne : (NK.GlobalCFT.Idele.normClassSubgroup K L).index ≠ 0 :=
    NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := K) (L := L)
  have heq : NK.GlobalCFT.Idele.normClassSubgroup K L = NK.GlobalCFT.Idele.normClassSubgroup K ↥A :=
    eq_of_le_of_index_eq hle' hidxeq.symm hne
  rw [← heq]
  exact hle

end Work.SSGRoute.CFTSide
