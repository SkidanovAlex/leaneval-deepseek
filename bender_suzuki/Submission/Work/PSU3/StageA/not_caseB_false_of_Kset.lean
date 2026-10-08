import Mathlib
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.PSU3.StageA.G0Basic
import Submission.Work.PSU3.StageA.G0set_subgroup
import Submission.Work.PSU3.StageA.centD_eq_bot_of_le_Ksub

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

open scoped Pointwise
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

theorem not_caseB_false_of_Kset {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h5 : orderOf (s * t) = 5) (hW : Work.ThmF.W H t = ⊥)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 2)
    (hK : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (hcanon : ∀ x ∈ Q, x ≠ 1 → ∃ g ∈ Q, ∃ k ∈ Work.ThmF.Kset H t, ∃ y ∈ Q,
      t * x * t = g * k * t * y) :
    False := by
  classical
  have hsplit : IsSplitRankOne H Q t := hS.split
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  have hti : t⁻¹ = t := Work.RankOneUniqueness.inv_eq_self hsplit
  haveI : IsSimpleGroup G := hS.simple
  set K : Subgroup G := Work.ThmF.Ksub H t with hKdef
  have hKleD : K ≤ twoPoint H t := by rw [hKdef]; exact Work.ThmF.Ksub_le_twoPoint t
  have hKleH : K ≤ H := hKleD.trans inf_le_left
  have hKinv : ∀ k ∈ K, t * k * t = k⁻¹ := by
    intro k hk
    have hk' : k ∈ Work.ThmF.Kset H t := by
      have h2 : k ∈ (K : Set G) := hk
      have h2' : k ∈ (Work.ThmF.Ksub H t : Set G) := h2
      rw [hK] at h2'
      exact h2'
    have h := (Work.ThmF.mem_Kset_iff.mp hk').2
    rwa [hti] at h
  have hQtG0 : ∀ x ∈ Q, t * x * t ∈ G0set Q K t := by
    intro x hx
    by_cases hx1 : x = 1
    · subst hx1
      have h1 : t * 1 * t = (1 : G) := by rw [mul_one, ht2]
      rw [h1]
      exact mem_G0set.mpr (Or.inl (Subgroup.mem_sup_left (Q.one_mem)))
    · obtain ⟨g, hg, k, hkKset, y, hy, hgky⟩ := hcanon x hx hx1
      have hkK : k ∈ K := by
        have h3 : k ∈ (Work.ThmF.Kset H t : Set G) := hkKset
        have h3' : k ∈ (Work.ThmF.Ksub H t : Set G) := by
          rw [hK]; exact h3
        exact h3'
      refine mem_G0set.mpr (Or.inr ⟨g * k, ?_, y, hy, ?_⟩)
      · exact (Q ⊔ K).mul_mem (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right hkK)
      · exact hgky
  obtain ⟨S, hSset⟩ :=
    G0set_subgroup (H := H) (Q := Q) (K := K) ht2 hKleH hsplit.normal hKinv hQtG0
  have hQleS : Q ≤ S := by
    intro x hx
    show x ∈ (S : Set G)
    rw [hSset]
    exact mem_G0set.mpr (Or.inl (Subgroup.mem_sup_left hx))
  have htS : t ∈ S := by
    show t ∈ (S : Set G)
    rw [hSset]
    exact mem_G0set.mpr (Or.inr ⟨1, (Q ⊔ K).one_mem, 1, Q.one_mem, by group⟩)
  have hStop : S = ⊤ := by
    have hle : Subgroup.closure ((Q : Set G) ∪ {t}) ≤ S := by
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      rcases hx with hx | hx
      · exact hQleS hx
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]; exact htS
    rw [Work.RankOneUniqueness.closure_Q_t_eq_top hsplit] at hle
    exact top_le_iff.mp hle
  have hHleS : H ≤ S := by rw [hStop]; exact le_top
  have hPleH : Q ⊔ K ≤ H := sup_le hsplit.le hKleH
  have hHleP : H ≤ Q ⊔ K := by
    intro hh hhh
    have hhS0 : hh ∈ (S : Set G) := hHleS hhh
    have hhS : hh ∈ G0set Q K t := by rwa [hSset] at hhS0
    rw [mem_G0set] at hhS
    rcases hhS with hhS | ⟨p, hp, q, hq, hpq⟩
    · exact hhS
    · exfalso
      have htH : t ∈ H := by
        have h2 : t = p⁻¹ * hh * q⁻¹ := by rw [hpq]; group
        rw [h2]
        exact H.mul_mem (H.mul_mem (H.inv_mem (hPleH hp)) hhh) (H.inv_mem (hsplit.le hq))
      exact hsplit.not_mem htH
  have hDleK : twoPoint H t ≤ K := by
    intro d hd
    have hdP : d ∈ Q ⊔ K := hHleP (Subgroup.mem_inf.mp hd).1
    have hdQK : d ∈ ((Q : Set G) * (K : Set G)) := by
      have h' : ((Q ⊔ K : Subgroup G) : Set G) = (Q : Set G) * (K : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left Q K (hKleH.trans hsplit.normal)
      rw [← h']
      exact hdP
    obtain ⟨q, hq, k, hk, hqk⟩ := Set.mem_mul.mp hdQK
    have hq1 : q = 1 := by
      have hqD : q ∈ twoPoint H t := by
        have hq_eq : q = d * k⁻¹ := by rw [← hqk]; group
        rw [hq_eq]
        exact (twoPoint H t).mul_mem hd ((twoPoint H t).inv_mem (hKleD hk))
      have hmem : q ∈ Q ⊓ twoPoint H t := ⟨hq, hqD⟩
      rw [hsplit.inf_eq] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [hq1, one_mul] at hqk
    rw [← hqk]
    exact hk
  have hVbot : centD H t = ⊥ := centD_eq_bot_of_le_Ksub hsplit hK hDleK
  exact absurd hVbot (Work.PSU3.StageA.centD_ne_bot hS)

end Work.PSU3.StageA
