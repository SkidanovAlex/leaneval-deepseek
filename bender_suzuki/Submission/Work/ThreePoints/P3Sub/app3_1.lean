import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.ThreePoints.P3NeBot.app3_1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.P3Sub

/-- **Peterfalvi I, Appendix III (1) (p. 206)**, in the `Ω = G ⧸ H` setting used by
Ch. II §4 Prop. 3 (c).

`H` is strongly embedded in `G`, `F ≤ N_G(X)` is `2`-transitive on `Ω_X`, `F ⊓ H` is a maximal
strongly embedded subgroup of `F`, `F` has `2`-rank `1`, and `t ∈ F ∖ H` is an involution
fixing `ω ∈ Ω`.  Then the two-point stabiliser `F ⊓ H ⊓ H^t` fixes `ω` as well.

The proof passes to the abstract group `↥F`, where the verified core `appIII_one_core`
(Appendix III (1): in a group of `2`-rank `1` with a maximal strongly embedded subgroup, the
two-point stabiliser of an involution fixes its unique fixed point) applies; the conclusion is
then transported back to `G` along a coset representative `x` of the fixed point of `t` in
`↥F ⧸ (F ⊓ H).subgroupOf F`. -/
theorem app3_1 {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    {X F : Subgroup G} (hFN : F ≤ Subgroup.normalizer (X : Set G))
    (h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub F (Submission.Blueprint.fixedPts H X))
    (hFSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((F ⊓ H).subgroupOf F))
    (hmax : ∀ M : Subgroup G, F ⊓ H ≤ M → M ≤ F → M = F ⊓ H ∨ M = F)
    (h2rank1 : ¬ Submission.Blueprint.HasFourGroup F)
    {t : G} (ht : orderOf t = 2) (htF : t ∈ F) (htH : t ∉ H)
    {ω : G ⧸ H} (hω : t • ω = ω) :
    F ⊓ Submission.Blueprint.twoPoint H t ≤ MulAction.stabilizer G ω := by
  classical
  haveI : Finite ↥F := Subtype.finite
  -- the involution `t` inside the abstract group `↥F`, outside the point stabiliser
  -- `(F ⊓ H).subgroupOf F`
  have ht' : orderOf (⟨t, htF⟩ : ↥F) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact ht
  have htH' : (⟨t, htF⟩ : ↥F) ∉ (F ⊓ H).subgroupOf F := by
    intro hmem
    exact htH (Subgroup.mem_subgroupOf.mp hmem).2
  -- `F ⊓ H` is a maximal subgroup of `↥F`, in the `∀`-form required by `appIII_one_core`
  have hmax' : ∀ M : Subgroup ↥F,
      (F ⊓ H).subgroupOf F ≤ M → M = (F ⊓ H).subgroupOf F ∨ M = ⊤ := by
    intro M hM
    have hle : F ⊓ H ≤ M.map (Subgroup.subtype F) := by
      intro y hy
      exact Subgroup.mem_map.mpr ⟨⟨y, hy.1⟩, hM (by rw [Subgroup.mem_subgroupOf]; exact hy), rfl⟩
    rcases hmax (M.map (Subgroup.subtype F)) hle (Subgroup.map_subtype_le M) with hcase | hcase
    · left
      refine le_antisymm ?_ hM
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      have h1 : (y : G) ∈ M.map (Subgroup.subtype F) := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      rwa [hcase] at h1
    · right
      refine le_antisymm le_top fun y _ => ?_
      have h1 : (y : G) ∈ M.map (Subgroup.subtype F) := by rw [hcase]; exact y.2
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp h1
      rwa [Subtype.ext hzy] at hz
  -- the (unique) fixed point of `t` in the coset space `↥F ⧸ (F ⊓ H).subgroupOf F`
  obtain ⟨b, hb_eq⟩ := Set.ncard_eq_one.mp
    (Work.ThreePoints.ncard_fixedPts_zpowers hFSE ht')
  have hb : (⟨t, htF⟩ : ↥F) • b = b := by
    have h : b ∈ Submission.Blueprint.fixedPts ((F ⊓ H).subgroupOf F)
        (Subgroup.zpowers (⟨t, htF⟩ : ↥F)) := by rw [hb_eq]; exact rfl
    exact (Work.ThreePoints.mem_fixedPts.mp h) _ (Subgroup.mem_zpowers _)
  have hbuniq : ∀ c : ↥F ⧸ (F ⊓ H).subgroupOf F, (⟨t, htF⟩ : ↥F) • c = c → c = b := by
    intro c hc
    have h : c ∈ Submission.Blueprint.fixedPts ((F ⊓ H).subgroupOf F)
        (Subgroup.zpowers (⟨t, htF⟩ : ↥F)) := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      exact Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hc)
    rw [hb_eq] at h
    exact h
  -- Peterfalvi I Appendix III (1), in the abstract group `↥F`
  have hcore := Work.ThreePoints.P3NeBot.appIII_one_core (F := ↥F) ((F ⊓ H).subgroupOf F)
    hFSE hmax' h2rank1 hBrSz hFT ht' htH' hb hbuniq
  -- transfer the conclusion to `G`
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  have hgF : g ∈ F := hg.1
  have hgtp : g ∈ Submission.Blueprint.twoPoint H t := hg.2
  have hg1 : (⟨g, hgF⟩ : ↥F) ∈ (F ⊓ H).subgroupOf F := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hgF, (Work.ThreePoints.mem_twoPoint.mp hgtp).1⟩
  have hg2 : (⟨g, hgF⟩ : ↥F) ∈ Submission.Blueprint.conj (⟨t, htF⟩ : ↥F)
      ((F ⊓ H).subgroupOf F) := by
    rw [Work.ThreePoints.mem_conj_iff, Subgroup.mem_subgroupOf]
    refine ⟨?_, ?_⟩
    · have hcoe : (((⟨t, htF⟩ : ↥F)⁻¹ * ⟨g, hgF⟩ * ⟨t, htF⟩ : ↥F) : G) = t⁻¹ * g * t := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      rw [hcoe]
      exact F.mul_mem (F.mul_mem (F.inv_mem htF) hgF) htF
    · have hcoe : (((⟨t, htF⟩ : ↥F)⁻¹ * ⟨g, hgF⟩ * ⟨t, htF⟩ : ↥F) : G) = t⁻¹ * g * t := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
      rw [hcoe]
      exact (Work.ThreePoints.mem_twoPoint.mp hgtp).2
  have hgmem : (⟨g, hgF⟩ : ↥F) ∈ (F ⊓ H).subgroupOf F ⊓ Submission.Blueprint.conj
      (⟨t, htF⟩ : ↥F) ((F ⊓ H).subgroupOf F) := ⟨hg1, hg2⟩
  have hgb : (⟨g, hgF⟩ : ↥F) • b = b := MulAction.mem_stabilizer_iff.mp (hcore hgmem)
  -- `b` is the coset `x H`; then `x⁻¹ g x ∈ H` and `x⁻¹ t x ∈ H`
  obtain ⟨x, hxb⟩ := QuotientGroup.mk_surjective b
  have hmem1 : ((⟨g, hgF⟩ : ↥F) * x)⁻¹ * x ∈ (F ⊓ H).subgroupOf F := by
    rw [← hxb, MulAction.Quotient.smul_mk, QuotientGroup.eq] at hgb
    exact hgb
  have hmem2 : ((⟨t, htF⟩ : ↥F) * x)⁻¹ * x ∈ (F ⊓ H).subgroupOf F := by
    have h := hb
    rw [← hxb, MulAction.Quotient.smul_mk, QuotientGroup.eq] at h
    exact h
  have hcoe1 : ((((⟨g, hgF⟩ : ↥F) * x)⁻¹ * x : ↥F) : G) = (x : G)⁻¹ * g⁻¹ * (x : G) := by
    have h1 : ((⟨g, hgF⟩ : ↥F) * x)⁻¹ * x = x⁻¹ * (⟨g, hgF⟩ : ↥F)⁻¹ * x := by group
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  have hcoe2 : ((((⟨t, htF⟩ : ↥F) * x)⁻¹ * x : ↥F) : G) = (x : G)⁻¹ * t * (x : G) := by
    have h1 : ((⟨t, htF⟩ : ↥F) * x)⁻¹ * x = x⁻¹ * (⟨t, htF⟩ : ↥F)⁻¹ * x := by group
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
    rw [inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two ht)]
  have hH1 : (x : G)⁻¹ * g * (x : G) ∈ H := by
    have h := (Subgroup.mem_subgroupOf.mp hmem1).2
    rw [hcoe1] at h
    rw [show (x : G)⁻¹ * g * (x : G) = ((x : G)⁻¹ * g⁻¹ * (x : G))⁻¹ from by group]
    exact H.inv_mem h
  have hH2 : (x : G)⁻¹ * t * (x : G) ∈ H := by
    have h := (Subgroup.mem_subgroupOf.mp hmem2).2
    rwa [hcoe2] at h
  -- `x H` is a fixed point of `t`; by uniqueness of the fixed point it is `ω`
  have hfix : t • (((x : G)) : G ⧸ H) = (((x : G)) : G ⧸ H) := by
    rw [Work.ThreePoints.smul_mk, QuotientGroup.eq]
    rw [show (t * (x : G))⁻¹ * (x : G) = (x : G)⁻¹ * t * (x : G) from by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two ht)]]
    exact hH2
  have hω' : ω = (((x : G)) : G ⧸ H) := by
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp (Work.ThreePoints.ncard_fixedPts_zpowers hH ht)
    have h1 : (((x : G)) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers t) := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      exact Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hfix)
    have h2 : ω ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers t) := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer]
      exact Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hω)
    rw [hy, Set.mem_singleton_iff] at h1 h2
    exact h2.trans h1.symm
  rw [hω', Work.ThreePoints.smul_mk, QuotientGroup.eq]
  rw [show (g * (x : G))⁻¹ * (x : G) = ((x : G)⁻¹ * g * (x : G))⁻¹ from by group]
  exact H.inv_mem hH1

end Work.ThreePoints.P3Sub
