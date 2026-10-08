import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3Sub.prop3b_support
import Submission.Work.ThreePoints.P3NeBot.app3_1
import Submission.Work.ThreePoints.P3NeBot.maximal_of_twoTransitive
import Submission.Work.ThreePoints.sec4_prop3_cd_ne_bot
import Submission.Work.NormalComplement.p2a_invol_unique
import Submission.Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical

/-- For a subgroup of a finite group, the cardinality of the underlying set is the group order. -/
lemma p2a_appIII_ncard_sub_eq_natCard {G : Type} [Group G] [Finite G] (S : Subgroup G) :
    (S : Set G).ncard = Nat.card ↥S := by
  rw [Set.ncard_def]; rfl

/-- The `ncard`-form of "`S` has exactly one involution" implies
`Work.BrauerSuzuki.HasUniqueInvolution ↥S`. -/
lemma p2a_appIII_hasUniqueInvolution_of_ncard_eq_one {G : Type} [Group G] {S : Subgroup G}
    (h : (Submission.Blueprint.involutions (S : Set G)).ncard = 1) :
    Work.BrauerSuzuki.HasUniqueInvolution ↥S := by
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp h
  have hzmem : z ∈ Submission.Blueprint.involutions (S : Set G) := by
    rw [hz]; exact Set.mem_singleton z
  rw [Submission.Blueprint.involutions, Set.mem_ofPred_eq] at hzmem
  refine ⟨⟨z, hzmem.1⟩, ?_, ?_⟩
  · exact (Subgroup.orderOf_coe (⟨z, hzmem.1⟩ : ↥S)).symm.trans hzmem.2
  · intro w hw
    apply Subtype.ext
    have hwin : (w : G) ∈ Submission.Blueprint.involutions (S : Set G) := by
      rw [Submission.Blueprint.involutions, Set.mem_ofPred_eq]
      exact ⟨w.2, by rw [Subgroup.orderOf_coe]; exact hw⟩
    rw [hz] at hwin
    exact Set.mem_singleton_iff.mp hwin

/-- A finite cyclic `2`-group with `x ^ 4 = 1` for all `x` has order at most `4`. -/
lemma p2a_appIII_cyclic_card_le_four {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hcyc : IsCyclic ↥S) (hexp : ∀ x ∈ S, x ^ 4 = 1) : Nat.card ↥S ≤ 4 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥S)
  have hzp : Subgroup.zpowers g = ⊤ := le_antisymm le_top (fun x _ => hg x)
  have hcard : Nat.card ↥S = orderOf g := by
    rw [← Nat.card_zpowers g, hzp, Subgroup.card_top]
  have hg4 : g ^ 4 = 1 := by
    have h := hexp (g : G) g.2
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using h
  have hdv : orderOf g ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hg4
  rw [hcard]
  exact Nat.le_of_dvd (by norm_num) hdv

/-- A finite generalized quaternion group whose elements all satisfy `x ^ 4 = 1` has order `8`
(so the only possibility is `Q₈`). -/
lemma p2a_appIII_genQuaternion_card_eq_eight {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hgen : Work.BrauerSuzuki.IsGenQuaternion ↥S) (hexp : ∀ x ∈ S, x ^ 4 = 1) :
    Nat.card ↥S = 8 := by
  obtain ⟨d⟩ := hgen
  obtain ⟨hcardP, -, -, -, -⟩ := Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d
  have htau4 : d.tau ^ 4 = 1 := by
    have h := hexp (d.tau : G) d.tau.2
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using h
  have hdv : orderOf d.tau ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr htau4
  rw [d.tau_order] at hdv
  have hn : d.n = 2 := by
    have hle : 2 ^ d.n ≤ 4 := Nat.le_of_dvd (by norm_num) hdv
    rcases lt_or_ge d.n 3 with h3 | h3
    · have h2 : 2 ≤ d.n := d.hn
      omega
    · exfalso
      have h8 : 8 ≤ 2 ^ d.n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ d.n := Nat.pow_le_pow_right (by norm_num) h3
      omega
  rw [hcardP, hn]
  norm_num

theorem p2a_appIII_cyclic (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hIII : Work.NormalComplement.AppIIIProp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ}
    {P A : Subgroup G} {r : ℕ} (h : Work.NormalComplement.Design.Setup5 G H t W p P A r)
    {S : Subgroup G} (hSpg : IsPGroup 2 S)
    (hSle : S ≤ Work.ThreePoints.p3F (Submission.Blueprint.centD H t) ⊓ H)
    (hSnorm : H ⊓ Subgroup.normalizer (Submission.Blueprint.centD H t : Set G) ≤
      Subgroup.normalizer (S : Set G))
    (hSD : S ⊓ Submission.Blueprint.twoPoint H t = ⊥)
    (hSsup : S ⊔ (Submission.Blueprint.twoPoint H t ⊓
      Subgroup.normalizer (Submission.Blueprint.centD H t : Set G)) =
      H ⊓ Subgroup.normalizer (Submission.Blueprint.centD H t : Set G))
    (hSidx : ¬ 2 ∣ (S.subgroupOf (Work.ThreePoints.p3F (Submission.Blueprint.centD H t) ⊓ H)).index)
    (huniqS : (Submission.Blueprint.involutions (S : Set G)).ncard = 1)
    (hcardS : (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard =
      (S : Set G).ncard + 1)
    (hexp : ∀ x ∈ S, x ^ 4 = 1) :
    ∀ (f m : ℕ), f.Prime →
      (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard = f ^ m →
      m = 1 → (S : Set G).ncard ≤ 4 := by
  intro f m hfprime hcardf hm
  have huniq : Work.BrauerSuzuki.HasUniqueInvolution ↥S :=
    p2a_appIII_hasUniqueInvolution_of_ncard_eq_one huniqS
  rcases Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution hSpg huniq with
    hcyc | hgen
  · -- cyclic case: `|S| ≤ 4` directly
    rw [p2a_appIII_ncard_sub_eq_natCard S]
    exact p2a_appIII_cyclic_card_le_four hcyc hexp
  · -- generalized quaternion case: `|S| = 8`, so the fixed point count is `9 = f ^ 1`, not prime
    have hcard8 : (S : Set G).ncard = 8 := by
      rw [p2a_appIII_ncard_sub_eq_natCard S]
      exact p2a_appIII_genQuaternion_card_eq_eight hgen hexp
    have h1 : f ^ m = (S : Set G).ncard + 1 := hcardf.symm.trans hcardS
    have hfm : f ^ m = 9 := by rw [h1, hcard8]
    have hf9 : f = 9 := by rw [hm] at hfm; simpa using hfm
    rw [hf9] at hfprime
    exact absurd hfprime (by norm_num)

end Work.NormalComplement
