import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Star.Basic
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.GroupTheory.Cyclic.isCyclic_of_cyclic_of_index_prime_quotient_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cyclicity of the norm class quotient in degree `p ^ a`, `a ≥ 3`

Let `L / K` be a finite cyclic extension of number fields of degree `p ^ a` with `p` prime and
`a ≥ 3`.  Suppose `M₁ ≤ M₂ ≤ L` is a chain of intermediate fields with

* `[C_K : N_{M₁/K} C_{M₁}] = p`,
* `[C_K : N_{M₂/K} C_{M₂}] = p ^ (a - 1)`,

and suppose the norm class quotients `C_{M₁} ⧸ N_{L/M₁} C_L` and `C_K ⧸ N_{M₂/K} C_{M₂}` are
cyclic.  Then `C_K ⧸ N_{L/K} C_L` is cyclic.

The proof is the group-theoretic argument of
`NK.GroupTheory.Cyclic.isCyclic_of_cyclic_of_index_prime_quotient_prime`, applied to the
abelian group `A = C_K ⧸ N_{L/K} C_L`: the image `H` of `N_{M₁/K} C_{M₁}` in `A` is cyclic of
order `p ^ (a - 1)`, the image `H'` of `N_{M₂/K} C_{M₂}` is a subgroup of `H` of order `p`
(here `M₁ ≤ M₂` is used), and `A ⧸ H' ≅ C_K ⧸ N_{M₂/K} C_{M₂}` is cyclic.

The two class-field-theoretic inputs are unconditional here:

* Hasse's index theorem `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic` gives
  `[C_K : N_{L/K} C_L] = [L : K] = p ^ a`;
* the transitivity/monotonicity of the norm class subgroups along a tower
  (`NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower`,
  `NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.CFTLib

open NK.GlobalCFT

/-- Lifting a homomorphism `f` which kills `N` to the quotient `G ⧸ N` does not change its
range. -/
private lemma range_lift_eq {G M : Type*} [Group G] [Group M] (N : Subgroup G) [N.Normal]
    (f : G →* M) (hf : N ≤ f.ker) :
    (QuotientGroup.lift N f hf).range = f.range := by
  ext y
  rw [MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    exact ⟨x, (QuotientGroup.lift_mk' N hf x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨QuotientGroup.mk' N x, QuotientGroup.lift_mk' N hf x⟩

/-- **Cyclicity of the image of a norm class subgroup.**  For `K ⊆ M ⊆ L` of number fields, the
norm map `N_{M/K} : C_M → C_K` descends to a surjection
`C_M ⧸ N_{L/M}C_L ↠ (N_{M/K}C_M) ⧸ N_{L/K}C_L`; hence the image of `N_{M/K}C_M` in
`C_K ⧸ N_{L/K}C_L` is cyclic whenever `C_M ⧸ N_{L/M}C_L` is. -/
private lemma isCyclic_map_normClassSubgroup
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M]
    [FiniteDimensional ↥M L] [IsGalois ↥M L]
    (h : IsCyclic (IdeleClassGroup ↥M ⧸ Idele.normClassSubgroup ↥M L)) :
    IsCyclic ↥((Idele.normClassSubgroup K ↥M).map
      (QuotientGroup.mk' (Idele.normClassSubgroup K L))) := by
  let NL : Subgroup (IdeleClassGroup K) := Idele.normClassSubgroup K L
  let NLM : Subgroup (IdeleClassGroup ↥M) := Idele.normClassSubgroup ↥M L
  have hle : NL ≤ Idele.normClassSubgroup K ↥M := Idele.normClassSubgroup_le_of_tower
  let f : IdeleClassGroup ↥M →* (IdeleClassGroup K ⧸ NL) :=
    (QuotientGroup.mk' NL).comp (IdeleClassGroup.normClassHom K ↥M)
  have hfker : NLM ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    obtain ⟨y, rfl⟩ := Idele.mem_normClassSubgroup.mp hx
    show QuotientGroup.mk' NL ((IdeleClassGroup.normClassHom K ↥M)
      ((IdeleClassGroup.normClassHom ↥M L) y)) = 1
    rw [NormGroup.globalCFT_normClassHom_trans y]
    exact (QuotientGroup.eq_one_iff _).mpr (Idele.mem_normClassSubgroup.mpr ⟨y, rfl⟩)
  let φ : (IdeleClassGroup ↥M ⧸ NLM) →* (IdeleClassGroup K ⧸ NL) :=
    QuotientGroup.lift NLM f hfker
  have hfrange : f.range = (Idele.normClassSubgroup K ↥M).map (QuotientGroup.mk' NL) := by
    rw [MonoidHom.range_comp, ← Idele.normClassSubgroup_eq_range]
  have hφrange : φ.range = (Idele.normClassSubgroup K ↥M).map (QuotientGroup.mk' NL) := by
    rw [range_lift_eq NLM f hfker, hfrange]
  rw [← hφrange]
  exact isCyclic_of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)

/-- **Cyclicity of the norm class quotient in degree `p ^ a` with `a ≥ 3`.**  See the module
docstring for the statement and the proof. -/
theorem isCyclic_normClassQuotient_of_three_le {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] {p a : ℕ} (hp : p.Prime) (ha : 3 ≤ a)
    (hcard : Nat.card (L ≃ₐ[K] L) = p ^ a)
    (M1 M2 : IntermediateField K L) [FiniteDimensional K M1] [NumberField ↥M1]
    [FiniteDimensional K M2] [NumberField ↥M2]
    (hM1 : M1 ≤ M2)
    (hidx1 : (NK.GlobalCFT.Idele.normClassSubgroup K ↥M1).index = p)
    (hidx2 : (NK.GlobalCFT.Idele.normClassSubgroup K ↥M2).index = p ^ (a - 1))
    (hcycl1 : IsCyclic (NK.GlobalCFT.IdeleClassGroup ↥M1 ⧸
      NK.GlobalCFT.Idele.normClassSubgroup ↥M1 L))
    (hcycl2 : IsCyclic (NK.GlobalCFT.IdeleClassGroup K ⧸
      NK.GlobalCFT.Idele.normClassSubgroup K ↥M2)) :
    IsCyclic (NK.GlobalCFT.IdeleClassGroup K ⧸
      NK.GlobalCFT.Idele.normClassSubgroup K L) := by
  -- `L / M₁` and `L / M₂` are finite Galois extensions
  haveI : FiniteDimensional ↥M1 L := inferInstance
  haveI : IsGalois ↥M1 L := inferInstance
  haveI : FiniteDimensional ↥M2 L := inferInstance
  haveI : IsGalois ↥M2 L := inferInstance
  -- the tower `M₁ ⊆ M₂`, so that `M₂` is an `M₁`-algebra
  letI : Algebra ↥M1 ↥M2 := (IntermediateField.inclusion hM1).toRingHom.toAlgebra
  haveI : IsScalarTower K ↥M1 ↥M2 := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FiniteDimensional ↥M1 ↥M2 := inferInstance
  -- monotonicity of the norm class subgroups
  have hle1 : Idele.normClassSubgroup K L ≤ Idele.normClassSubgroup K ↥M1 :=
    Idele.normClassSubgroup_le_of_tower (K := K) (L := ↥M1) (M := L)
  have hle2 : Idele.normClassSubgroup K L ≤ Idele.normClassSubgroup K ↥M2 :=
    Idele.normClassSubgroup_le_of_tower (K := K) (L := ↥M2) (M := L)
  have hle21 : Idele.normClassSubgroup K ↥M2 ≤ Idele.normClassSubgroup K ↥M1 :=
    Idele.normClassSubgroup_le_of_tower (K := K) (L := ↥M1) (M := ↥M2)
  -- the order of `A = C_K ⧸ N_{L/K} C_L` is `p ^ a`
  have hKL : Module.finrank K L = p ^ a := (IsGalois.card_aut_eq_finrank K L).symm.trans hcard
  have hNLidx : (Idele.normClassSubgroup K L).index = p ^ a := by
    rw [NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic, hKL]
  have hAcard : Nat.card (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) = p ^ a :=
    (Subgroup.index_eq_card (Idele.normClassSubgroup K L)).symm.trans hNLidx
  -- the two subgroups `S₁ = N_{M₁} ⧸ N_L` and `S₂ = N_{M₂} ⧸ N_L` of `A`
  let S1 : Subgroup (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) :=
    (Idele.normClassSubgroup K ↥M1).map (QuotientGroup.mk' (Idele.normClassSubgroup K L))
  let S2 : Subgroup (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) :=
    (Idele.normClassSubgroup K ↥M2).map (QuotientGroup.mk' (Idele.normClassSubgroup K L))
  -- `S₁` is cyclic: it is the image of `C_{M₁} ⧸ N_{L/M₁} C_L`
  have hS1cyc : IsCyclic ↥S1 := isCyclic_map_normClassSubgroup (K := K) (L := L) M1 hcycl1
  -- `S₂ ≤ S₁` because `M₁ ≤ M₂`
  have hS2le : S2 ≤ S1 := Subgroup.map_mono hle21
  -- the residuals `A ⧸ Sᵢ` are the norm class quotients of `Mᵢ`
  have hiso1 : (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) ⧸ S1 ≃*
      (IdeleClassGroup K ⧸ Idele.normClassSubgroup K ↥M1) :=
    QuotientGroup.quotientQuotientEquivQuotient (Idele.normClassSubgroup K L)
      (Idele.normClassSubgroup K ↥M1) hle1
  have hiso2 : (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) ⧸ S2 ≃*
      (IdeleClassGroup K ⧸ Idele.normClassSubgroup K ↥M2) :=
    QuotientGroup.quotientQuotientEquivQuotient (Idele.normClassSubgroup K L)
      (Idele.normClassSubgroup K ↥M2) hle2
  -- the indices of `S₁` and `S₂` in `A`
  have hS1index : S1.index = p :=
    (Subgroup.index_eq_card S1).trans ((Nat.card_congr hiso1.toEquiv).trans
      ((Subgroup.index_eq_card (Idele.normClassSubgroup K ↥M1)).symm.trans hidx1))
  have hS2index : S2.index = p ^ (a - 1) :=
    (Subgroup.index_eq_card S2).trans ((Nat.card_congr hiso2.toEquiv).trans
      ((Subgroup.index_eq_card (Idele.normClassSubgroup K ↥M2)).symm.trans hidx2))
  -- their orders
  have hS1card : Nat.card ↥S1 = p ^ (a - 1) := by
    have h1 := Subgroup.card_mul_index S1
    have hpa : p ^ a = p ^ (a - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a)]
    rw [hS1index, hAcard, hpa] at h1
    exact Nat.mul_right_cancel hp.pos h1
  have hS2card : Nat.card ↥S2 = p := by
    have h1 := Subgroup.card_mul_index S2
    have hpa : p ^ a = p * p ^ (a - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ a)]
    rw [hS2index, hAcard, hpa] at h1
    exact Nat.mul_right_cancel (pow_pos hp.pos _) h1
  -- `A ⧸ S₂` is cyclic
  have hS2cyc : IsCyclic ((IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) ⧸ S2) :=
    hiso2.isCyclic.mpr hcycl2
  -- `A` is finite, of order `p ^ a`
  haveI : Finite (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) :=
    Subgroup.index_ne_zero_iff_finite.mp (by rw [hNLidx]; exact pow_ne_zero _ hp.ne_zero)
  exact NK.GroupTheory.Cyclic.isCyclic_of_cyclic_of_index_prime_quotient_prime
    hp ha S1 hS1cyc hS1card hAcard S2 hS2le hS2card hS2cyc

end NK.CFTLib
