import Mathlib

namespace Work.CORE4

set_option linter.style.haveILetI false in
theorem isCyclic_of_le_sup_of_inf_eq_bot {G : Type*} [Group G] (A K F : Subgroup G)
    (hA : A ≤ K ⊔ F) (hnorm : K ≤ Subgroup.normalizer (F : Set G))
    (hinf : A ⊓ F = ⊥) (hK : IsCyclic ↥K) : IsCyclic ↥A := by
  -- `K` normalizes `F`, so `F` is normal in `K` and in `K ⊔ F`.
  haveI : IsCyclic ↥K := hK
  haveI h1 : (F.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  haveI h2 : (F.subgroupOf (K ⊔ F)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
  -- A quotient of the cyclic group `K` is cyclic.
  have hquotK : IsCyclic (↥K ⧸ F.subgroupOf K) :=
    isCyclic_of_surjective (QuotientGroup.mk' (F.subgroupOf K)) (QuotientGroup.mk'_surjective _)
  -- Noether's second isomorphism theorem identifies `(K ⊔ F)/F` with `K/(K ∩ F)`.
  haveI hquotSup : IsCyclic (↥(K ⊔ F) ⧸ F.subgroupOf (K ⊔ F)) :=
    (MulEquiv.isCyclic (QuotientGroup.quotientInfEquivProdNormalizerQuotient K F hnorm)).mp hquotK
  -- `A` embeds into the cyclic group `(K ⊔ F)/F`, since `A ⊓ F = ⊥`.
  let φ : ↥A →* ↥(K ⊔ F) ⧸ F.subgroupOf (K ⊔ F) :=
    (QuotientGroup.mk' (F.subgroupOf (K ⊔ F))).comp (Subgroup.inclusion hA)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hxmem : ((Subgroup.inclusion hA x : ↥(K ⊔ F)) : G) ∈ F := by
        have hx1 : ((Subgroup.inclusion hA x : ↥(K ⊔ F)) :
            ↥(K ⊔ F) ⧸ F.subgroupOf (K ⊔ F)) = 1 := by
          simpa only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply] using hx
        have hm2 : (Subgroup.inclusion hA x : ↥(K ⊔ F)) ∈ F.subgroupOf (K ⊔ F) :=
          (QuotientGroup.eq_one_iff (N := F.subgroupOf (K ⊔ F)) _).mp hx1
        exact Subgroup.mem_subgroupOf.mp hm2
      have hmem : (x : G) ∈ A ⊓ F := ⟨x.2, hxmem⟩
      rw [hinf] at hmem
      exact Subtype.ext (by simpa using (Subgroup.mem_bot.mp hmem))
    · intro hx
      subst hx
      simp
  exact isCyclic_of_injective φ hφinj

end Work.CORE4
