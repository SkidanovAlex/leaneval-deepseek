import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.P3NeBot.prop1a_brsz
import Submission.Work.ThreePoints.P3NeBot.prop1b_brsz
import Submission.Work.ThreePoints.P3NeBot.p3_lemma1
import Submission.Work.ThreePoints.P3NeBot.p3_appI_one
import Submission.Work.ThreePoints.P3NeBot.p3_twoTransitive
import Submission.Work.ThreePoints.P3NeBot.p3_b

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

open LeanEval.GroupTheory.Defs

/-- Peterfalvi I Ch. II §4 Prop. 3 (a), (b) in the source's case `X ≠ 1`: with `X ≠ ⊥`,
`X ≤ V = C_D(t)` and `N_K(X) ≠ 1` (the existence of `k ∈ K ∖ {1}` normalising `X`), setting
`F = O^{2'}(C_G(X))`: `N_G(X) = F·N_V(X)`, and `N_H(X) = S ⋊ N_D(X)` with `S` a Sylow 2-subgroup
of `F ⊓ H`.  (`X ≠ ⊥` is what makes `C_G(X) < G`, hence `|F| < |G|` and `(B1)` applicable to `F`;
see `Work.ThreePoints.NOTES_LEAD_bs_p3_induction.md`.) -/
theorem sec4_prop3_ab_ne_bot {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (X : Subgroup G) (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    let C := Subgroup.centralizer (X : Set G)
    let F := (Submission.Blueprint.oddResidual C).map C.subtype
    Subgroup.normalizer (X : Set G) =
        F ⊔ (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G)) ∧
    (∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ F ⊓ H ∧ ¬ 2 ∣ (S.subgroupOf (F ⊓ H)).index ∧
      H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
      S ⊓ Submission.Blueprint.twoPoint H t = ⊥ ∧
      S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
        H ⊓ Subgroup.normalizer (X : Set G)) := by
  show Subgroup.normalizer (X : Set G) =
        p3F X ⊔ (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G)) ∧
      (∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ p3F X ⊓ H ∧
        ¬ 2 ∣ (S.subgroupOf (p3F X ⊓ H)).index ∧
        H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
        S ⊓ Submission.Blueprint.twoPoint H t = ⊥ ∧
        S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
          H ⊓ Subgroup.normalizer (X : Set G))
  constructor
  · -- ## (a)
    refine le_antisymm ?_ (sup_le ?_ inf_le_right)
    · -- `N_G(X) ≤ F ⊔ (V ⊓ N_G(X))`
      intro g hg
      -- the points `1` and `t` of `Ω = G ⧸ H` are fixed by `X`
      have hXH : X ≤ H := hX.trans (inf_le_left.trans inf_le_left)
      have hXtH : X ≤ Submission.Blueprint.conj t H :=
        hX.trans (inf_le_left.trans inf_le_right)
      have hcS : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H X := by
        rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, conj_one]
        exact hXH
      have hdS : ((t : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H X := by
        rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
        exact hXtH
      have hcd : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
        intro hcon
        exact htH (by
          have := QuotientGroup.eq.mp hcon
          simpa using this)
      -- `N_G(X)` preserves `fixedPts H X`
      have hpres : ∀ h ∈ Subgroup.normalizer (X : Set G),
          ∀ ω ∈ Submission.Blueprint.fixedPts H X,
            h • ω ∈ Submission.Blueprint.fixedPts H X := by
        intro h hh ω hω
        rw [mem_fixedPts] at hω ⊢
        intro x hx
        have hxh : h⁻¹ * x * h ∈ X := by
          simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) x).mp hx
        calc x • (h • ω) = (x * h) • ω := by rw [mul_smul]
          _ = (h * (h⁻¹ * x * h)) • ω := by rw [show x * h = h * (h⁻¹ * x * h) from by group]
          _ = h • ((h⁻¹ * x * h) • ω) := by rw [mul_smul]
          _ = h • ω := by rw [hω _ hxh]
      -- 2-transitivity of `F₁` on `Ω_X`
      have h2t := P3NeBot.p3_twoTransitive hFT hC hA hBrSz hS hH ht htH hX0 hX hNX
      have hg'inv : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ hg
      have hcd' : g⁻¹ • ((1 : G) : G ⧸ H) ≠ g⁻¹ • ((t : G) : G ⧸ H) := fun hcon => hcd (by
        have := congrArg (fun p : G ⧸ H => g • p) hcon
        simpa only [← mul_smul, mul_inv_cancel, one_smul] using this)
      obtain ⟨y, hyF1, hyc, hyd⟩ :=
        h2t ((1 : G) : G ⧸ H) hcS ((t : G) : G ⧸ H) hdS hcd
          (g⁻¹ • ((1 : G) : G ⧸ H)) (hpres g⁻¹ hg'inv _ hcS)
          (g⁻¹ • ((t : G) : G ⧸ H)) (hpres g⁻¹ hg'inv _ hdS) hcd'
      -- `g * y` fixes `1` and `t`, hence lies in `D = H ⊓ H^t`
      have hgyc : (g * y) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
        rw [mul_smul, hyc, ← mul_smul, mul_inv_cancel, one_smul]
      have hgyd : (g * y) • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by
        rw [mul_smul, hyd, ← mul_smul, mul_inv_cancel, one_smul]
      have hgyD : g * y ∈ Submission.Blueprint.twoPoint H t := by
        rw [twoPoint_eq, Subgroup.mem_inf]
        constructor
        · have h1 : g * y ∈ MulAction.stabilizer G ((1 : G) : G ⧸ H) := by
            rw [MulAction.mem_stabilizer_iff]; exact hgyc
          rwa [stabilizer_mk, conj_one] at h1
        · have h1 : g * y ∈ MulAction.stabilizer G ((t : G) : G ⧸ H) := by
            rw [MulAction.mem_stabilizer_iff]; exact hgyd
          rwa [stabilizer_mk] at h1
      have hyN : y ∈ Subgroup.normalizer (X : Set G) := p3F1_le_normalizer X hyF1
      have hgyN : g * y ∈ Subgroup.normalizer (X : Set G) := Subgroup.mul_mem _ hg hyN
      have hgyV : g * y ∈ p3F X ⊔
          (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G)) :=
        (sup_le_sup (p3F1_le_p3F X) le_rfl)
          (P3NeBot.p3_appI_one hFT hC hA hBrSz hS hH ht htH hX ⟨hgyD, hgyN⟩)
      have hyinv : y⁻¹ ∈ p3F X := Subgroup.inv_mem _ (p3F1_le_p3F X hyF1)
      have hg_eq : g = (g * y) * y⁻¹ := by group
      rw [hg_eq]
      exact Subgroup.mul_mem _ hgyV (Subgroup.mem_sup_left hyinv)
    · -- `F ≤ N_G(X)`
      exact (p3F_le_centralizer X).trans (Subgroup.centralizer_le_normalizer (X : Set G))
  · -- ## (b)
    exact P3NeBot.p3_b hFT hC hA hZJ hBrSz hMod hS hH ht htH hX0 hX hNX

end Work.ThreePoints
