import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.P3NeBot.app3_1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.ThreePoints.ThmC

open LeanEval.GroupTheory.Defs

/-- **Peterfalvi I Appendix III (1) (p. 206)**, applied to the orbit of the base point in the
`Ω = G ⧸ H` setting.  Let `F ≤ G` be such that `F ⊓ H` is a maximal strongly embedded subgroup of
`F`, let `¬ HasFourGroup F`, and let `s ∈ Inv(F ∖ H)` whose (unique) fixed point `ω` of `Ω = G ⧸ H`
lies in the `F`-orbit of the base point.  Then `F ⊓ H ⊓ H^s ≤ Stab_G(ω)`. -/
theorem app3_consequence {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {F : Subgroup G}
    (hstrongF : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((F ⊓ H).subgroupOf F))
    (hmax : IsCoatom ((F ⊓ H).subgroupOf F))
    (hrank : ¬ Submission.Blueprint.HasFourGroup F)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    {s : G} (hs : orderOf s = 2) (hsF : s ∈ F) (hsH : s ∉ H)
    {ω : G ⧸ H} (hω : s • ω = ω)
    (huniq : ∀ c : G ⧸ H, s • c = c → c = ω)
    (horb : ω ∈ MulAction.orbit F (((1 : G) : G ⧸ H))) :
    F ⊓ H ⊓ Submission.Blueprint.conj s H ≤ MulAction.stabilizer G ω := by
  classical
  haveI : Finite ↥F := Subtype.finite
  -- the involution `t = s` in the abstract group `↥F`, outside the point stabiliser
  -- `K = (F ⊓ H).subgroupOf F`
  have ht' : orderOf (⟨s, hsF⟩ : ↥F) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hs
  have htH' : (⟨s, hsF⟩ : ↥F) ∉ (F ⊓ H).subgroupOf F := by
    intro hmem
    exact hsH (Subgroup.mem_subgroupOf.mp hmem).2
  -- `K` is maximal in `↥F`, in the `∀`-form required by `appIII_one_core`
  have hmax' : ∀ M : Subgroup ↥F,
      (F ⊓ H).subgroupOf F ≤ M → M = (F ⊓ H).subgroupOf F ∨ M = ⊤ := by
    intro M hM
    rcases eq_or_ne M ((F ⊓ H).subgroupOf F) with hMK | hMK
    · exact Or.inl hMK
    · obtain ⟨g, hgM, hgK⟩ :=
        SetLike.exists_of_lt (lt_of_le_of_ne hM (Ne.symm hMK))
      exact Or.inr ((SetLike.isCoatom_iff.mp hmax).2 M g hM hgK hgM)
  -- the unique fixed point of `t` in the coset space `↥F ⧸ K`
  obtain ⟨b, hb_eq⟩ := Set.ncard_eq_one.mp (Work.ThreePoints.ncard_fixedPts_zpowers hstrongF ht')
  have hb : (⟨s, hsF⟩ : ↥F) • b = b := by
    have h : b ∈ Submission.Blueprint.fixedPts ((F ⊓ H).subgroupOf F)
        (Subgroup.zpowers (⟨s, hsF⟩ : ↥F)) := by rw [hb_eq]; exact rfl
    exact (Work.ThreePoints.mem_fixedPts.mp h) _ (Subgroup.mem_zpowers _)
  have hbuniq : ∀ c : ↥F ⧸ (F ⊓ H).subgroupOf F, (⟨s, hsF⟩ : ↥F) • c = c → c = b := by
    intro c hc
    have h : c ∈ Submission.Blueprint.fixedPts ((F ⊓ H).subgroupOf F)
        (Subgroup.zpowers (⟨s, hsF⟩ : ↥F)) := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      exact Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hc)
    rw [hb_eq] at h
    exact h
  -- Peterfalvi I Appendix III (1), in the abstract group `↥F`
  have hcore := Work.ThreePoints.P3NeBot.appIII_one_core (F := ↥F) ((F ⊓ H).subgroupOf F)
    hstrongF hmax' hrank hBrSz hFT ht' htH' hb hbuniq
  -- transfer the conclusion to `G`
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  have hgF : g ∈ F := hg.1.1
  have hgtp : g ∈ Submission.Blueprint.twoPoint H s := ⟨hg.1.2, hg.2⟩
  have hg1 : (⟨g, hgF⟩ : ↥F) ∈ (F ⊓ H).subgroupOf F := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hgF, hg.1.2⟩
  have hg2 : (⟨g, hgF⟩ : ↥F) ∈ Submission.Blueprint.conj (⟨s, hsF⟩ : ↥F)
      ((F ⊓ H).subgroupOf F) := by
    rw [Work.ThreePoints.mem_conj_iff, Subgroup.mem_subgroupOf]
    refine ⟨?_, ?_⟩
    · have hcoe : (((⟨s, hsF⟩ : ↥F)⁻¹ * ⟨g, hgF⟩ * ⟨s, hsF⟩ : ↥F) : G) = s⁻¹ * g * s := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      rw [hcoe]
      exact F.mul_mem (F.mul_mem (F.inv_mem hsF) hgF) hsF
    · have hcoe : (((⟨s, hsF⟩ : ↥F)⁻¹ * ⟨g, hgF⟩ * ⟨s, hsF⟩ : ↥F) : G) = s⁻¹ * g * s := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      rw [hcoe]
      exact Work.ThreePoints.mem_twoPoint.mp hgtp |>.2
  have hgmem : (⟨g, hgF⟩ : ↥F) ∈ (F ⊓ H).subgroupOf F ⊓ Submission.Blueprint.conj
      (⟨s, hsF⟩ : ↥F) ((F ⊓ H).subgroupOf F) := ⟨hg1, hg2⟩
  have hgb : (⟨g, hgF⟩ : ↥F) • b = b := MulAction.mem_stabilizer_iff.mp (hcore hgmem)
  -- `b` is the coset `x H`; then `x⁻¹ g x ∈ H` and `x⁻¹ s x ∈ H`
  obtain ⟨x, hxb⟩ := QuotientGroup.mk_surjective b
  have hmem1 : ((⟨g, hgF⟩ : ↥F) * x)⁻¹ * x ∈ (F ⊓ H).subgroupOf F := by
    rw [← hxb, MulAction.Quotient.smul_mk, QuotientGroup.eq] at hgb
    exact hgb
  have hmem2 : ((⟨s, hsF⟩ : ↥F) * x)⁻¹ * x ∈ (F ⊓ H).subgroupOf F := by
    have h := hb
    rw [← hxb, MulAction.Quotient.smul_mk, QuotientGroup.eq] at h
    exact h
  have hcoe1 : ((((⟨g, hgF⟩ : ↥F) * x)⁻¹ * x : ↥F) : G) = (x : G)⁻¹ * g⁻¹ * (x : G) := by
    have h1 : ((⟨g, hgF⟩ : ↥F) * x)⁻¹ * x = x⁻¹ * (⟨g, hgF⟩ : ↥F)⁻¹ * x := by group
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  have hcoe2 : ((((⟨s, hsF⟩ : ↥F) * x)⁻¹ * x : ↥F) : G) = (x : G)⁻¹ * s * (x : G) := by
    have h1 : ((⟨s, hsF⟩ : ↥F) * x)⁻¹ * x = x⁻¹ * (⟨s, hsF⟩ : ↥F)⁻¹ * x := by group
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
    rw [inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two hs)]
  have hH1 : (x : G)⁻¹ * g * (x : G) ∈ H := by
    have h := (Subgroup.mem_subgroupOf.mp hmem1).2
    rw [hcoe1] at h
    rw [show (x : G)⁻¹ * g * (x : G) = ((x : G)⁻¹ * g⁻¹ * (x : G))⁻¹ from by group]
    exact H.inv_mem h
  have hH2 : (x : G)⁻¹ * s * (x : G) ∈ H := by
    have h := (Subgroup.mem_subgroupOf.mp hmem2).2
    rwa [hcoe2] at h
  -- `x H` is a fixed point of `s`; by the uniqueness of the fixed point it equals `ω`
  have hfix : s • (((x : G)) : G ⧸ H) = (((x : G)) : G ⧸ H) := by
    rw [Work.ThreePoints.smul_mk, QuotientGroup.eq]
    rw [show (s * (x : G))⁻¹ * (x : G) = (x : G)⁻¹ * s * (x : G) from by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two hs)]]
    exact hH2
  have hω' : ω = (((x : G)) : G ⧸ H) := by
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp (Work.ThreePoints.ncard_fixedPts_zpowers hH hs)
    have h1 : (((x : G)) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers s) := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      exact Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hfix)
    have h2 : ω ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers s) := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      exact Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hω)
    rw [hy, Set.mem_singleton_iff] at h1 h2
    exact h2.trans h1.symm
  rw [hω', Work.ThreePoints.smul_mk, QuotientGroup.eq]
  rw [show (g * (x : G))⁻¹ * (x : G) = ((x : G)⁻¹ * g * (x : G))⁻¹ from by group]
  exact H.inv_mem hH1

end Work.ThreePoints.ThmC
