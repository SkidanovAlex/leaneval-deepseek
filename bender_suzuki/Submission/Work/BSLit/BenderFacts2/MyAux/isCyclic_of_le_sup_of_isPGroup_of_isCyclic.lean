import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2.MyAux

theorem isCyclic_of_le_sup_of_isPGroup_of_isCyclic
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {U T A : Subgroup G} (hU : IsPGroup p U) (hT : IsCyclic T)
    (hN : T ≤ Subgroup.normalizer (U : Set G)) (hUT : U ⊓ T = ⊥) (hA : A ≤ U ⊔ T)
    (hcop : ¬ p ∣ Nat.card ↥A) : IsCyclic ↥A := by
  -- `A` is a `p'`-subgroup and `U` is a `p`-group, so `A ⊓ U = ⊥`.
  have hAU : A ⊓ U = ⊥ := by
    have hd : Disjoint U A :=
      IsPGroup.disjoint_of_coprime hU (IsPGroup.card (G := ↥A))
        (hp.coprime_iff_not_dvd.mpr hcop)
    rw [inf_comm]
    exact disjoint_iff.mp hd
  -- `T` normalises `U`, so `U` is normal in `T ⊔ U`.
  have hNrmT : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hNrmTU : (U.subgroupOf (T ⊔ U)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hN
  -- A quotient of the cyclic group `T` is cyclic.
  haveI : IsCyclic ↥T := hT
  have hcT : IsCyclic (T ⧸ U.subgroupOf T) :=
    isCyclic_of_surjective (QuotientGroup.mk' (U.subgroupOf T))
      (QuotientGroup.mk'_surjective (U.subgroupOf T))
  -- Noether's second isomorphism theorem: `(T ⊔ U)/U ≅ T/(T ⊓ U)` is cyclic.
  haveI hcTU : IsCyclic (↥(T ⊔ U) ⧸ U.subgroupOf (T ⊔ U)) :=
    (MulEquiv.isCyclic (QuotientGroup.quotientInfEquivProdNormalizerQuotient T U hN)).mp hcT
  -- `A` embeds in `(T ⊔ U)/U`.
  have hA' : A ≤ T ⊔ U := by rwa [sup_comm]
  let φ : A →* (↥(T ⊔ U) ⧸ U.subgroupOf (T ⊔ U)) :=
    (QuotientGroup.mk' (U.subgroupOf (T ⊔ U))).comp (Subgroup.inclusion hA')
  have hφ1 : ∀ a : A, φ a = 1 ↔ (a : G) ∈ U := by
    intro a
    show QuotientGroup.mk (Subgroup.inclusion hA' a) = 1 ↔ (a : G) ∈ U
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    rw [hφ1 a] at ha
    have hmem : (a : G) ∈ A ⊓ U := ⟨a.2, ha⟩
    rw [hAU] at hmem
    exact Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem)
  exact isCyclic_of_injective φ hφinj

end Work.BSLit.BenderFacts2.MyAux
