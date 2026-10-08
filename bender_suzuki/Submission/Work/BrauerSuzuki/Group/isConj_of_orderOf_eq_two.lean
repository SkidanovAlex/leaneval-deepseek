import Mathlib
import Submission.Work.BrauerSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.BrauerSuzuki.Group

/-- Every element of order `2` of a finite group lies in some Sylow `2`-subgroup. -/
theorem exists_sylow_mem_of_orderOf_eq_two {G : Type*} [Group G] {u : G} (hu : orderOf u = 2) :
    ∃ S : Sylow 2 G, u ∈ S := by
  have hP : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [pow_one, Nat.card_zpowers, hu])
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  exact ⟨S, hS (Subgroup.mem_zpowers u)⟩

/-- Conjugation preserves the order of an element. -/
theorem orderOf_conj_eq {G : Type*} [Group G] (c x : G) :
    orderOf (c * x * c⁻¹) = orderOf x := by
  have h : SemiconjBy c x (c * x * c⁻¹) := by rw [SemiconjBy]; group
  exact (SemiconjBy.orderOf_eq c h).symm

theorem isConj_of_orderOf_eq_two {G : Type*} [Group G] [Finite G]
    (h : ∀ S : Sylow 2 G, Work.BrauerSuzuki.HasUniqueInvolution ↥S)
    {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) : IsConj u v := by
  obtain ⟨Su, huS⟩ := exists_sylow_mem_of_orderOf_eq_two hu
  obtain ⟨Sv, hvS⟩ := exists_sylow_mem_of_orderOf_eq_two hv
  obtain ⟨zu, hzu2, hzu_uniq⟩ := h Su
  obtain ⟨zv, hzv2, hzv_uniq⟩ := h Sv
  -- `u` and `v` are the unique involutions of `Su` and `Sv`.
  have hu_eq : u = (zu : G) := by
    have hmem : (⟨u, huS⟩ : ↥Su) = zu :=
      hzu_uniq ⟨u, huS⟩ (by rw [Subgroup.orderOf_mk]; exact hu)
    exact congrArg Subtype.val hmem
  have hv_eq : v = (zv : G) := by
    have hmem : (⟨v, hvS⟩ : ↥Sv) = zv :=
      hzv_uniq ⟨v, hvS⟩ (by rw [Subgroup.orderOf_mk]; exact hv)
    exact congrArg Subtype.val hmem
  -- Sylow conjugacy: `Su = c • Sv`.
  obtain ⟨c, hc⟩ := (Sylow.isPretransitive_of_finite (p := 2) (G := G)).exists_smul_eq Sv Su
  -- `c z_v c⁻¹` is an involution of `Su`, hence equals `z_u`.
  have hmem : c * (zv : G) * c⁻¹ ∈ Su := by
    have hsub : (MulAut.conj c • (Sv : Subgroup G)) = (Su : Subgroup G) := by
      rw [← Sylow.pointwise_smul_def (g := MulAut.conj c) (P := Sv), ← Sylow.smul_def, hc]
    have h0 : (MulAut.conj c) • (zv : G) ∈ Su := by
      change (MulAut.conj c) • (zv : G) ∈ (Su : Subgroup G)
      rw [← hsub]
      exact Subgroup.smul_mem_pointwise_smul (zv : G) (MulAut.conj c) (Sv : Subgroup G) zv.2
    simpa [MulAut.smul_def, MulAut.conj_apply] using h0
  have hord : orderOf (c * (zv : G) * c⁻¹) = 2 := by
    rw [orderOf_conj_eq, Subgroup.orderOf_coe zv, hzv2]
  have hzu_eq : c * (zv : G) * c⁻¹ = (zu : G) := by
    have hmem' : (⟨c * (zv : G) * c⁻¹, hmem⟩ : ↥Su) = zu :=
      hzu_uniq ⟨c * (zv : G) * c⁻¹, hmem⟩ (by rw [Subgroup.orderOf_mk]; exact hord)
    exact congrArg Subtype.val hmem'
  rw [isConj_iff]
  refine ⟨c⁻¹, ?_⟩
  rw [hu_eq, hv_eq, ← hzu_eq]
  group

end Work.BrauerSuzuki.Group
