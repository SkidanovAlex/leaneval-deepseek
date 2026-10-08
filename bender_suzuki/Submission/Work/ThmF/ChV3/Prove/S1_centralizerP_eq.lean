import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV3.step6aux_count
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.ThmF.ChV3.Prove.S1_CG_card_orbit
import Submission.Work.ThmF.ChV3.Prove.S1_R_inf_CH_eq_P
import Submission.Work.ThmF.ChV3.Prove.S1_P_inf_CQ_sup_Sig
import Submission.Work.ThmF.ChV3.Prove.S1_CH_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open Pointwise

variable {G : Type} [Group G] [Finite G]

/-- **Cardinality of a product of subgroups with trivial intersection.**  If `B` normalises `A`,
then `A ⊔ B = A · B` (product of subgroups) and the multiplication map `A × B → A ⊔ B` is
bijective (it is surjective by `A ⊔ B = ↑A * ↑B`, and injective because `A ⊓ B = ⊥`); hence
`|A ⊔ B| = |A| |B|`. -/
private lemma card_sup_of_inf_eq_bot {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) (hbot : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hcoe : (↑(A ⊔ B) : Set G) = (↑A : Set G) * (↑B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B h
  have hbij : Function.Bijective
      (fun p : ↥A × ↥B =>
        (⟨(p.1 : G) * (p.2 : G),
          show (p.1 : G) * (p.2 : G) ∈ (↑(A ⊔ B) : Set G) from by
            rw [hcoe]; exact Set.mul_mem_mul p.1.2 p.2.2⟩ : ↥(A ⊔ B))) := by
    constructor
    · intro p q hpq
      have hval : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := by
        simpa using congrArg (fun z : ↥(A ⊔ B) => (z : G)) hpq
      have h1 : (p.1 : G)⁻¹ * (q.1 : G) = (p.2 : G) * (q.2 : G)⁻¹ := by
        have h2 : (p.2 : G) * (q.2 : G)⁻¹ = (p.1 : G)⁻¹ * (q.1 : G) := by
          calc (p.2 : G) * (q.2 : G)⁻¹
              = (p.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (q.2 : G)⁻¹ := by group
            _ = (p.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (q.2 : G)⁻¹ := by rw [hval]
            _ = (p.1 : G)⁻¹ * (q.1 : G) := by group
        exact h2.symm
      have hmem : (p.1 : G)⁻¹ * (q.1 : G) ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem p.1.2) q.1.2,
          by rw [h1]; exact B.mul_mem p.2.2 (B.inv_mem q.2.2)⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have hpq1 : (q.1 : G) = (p.1 : G) := by
        have := congrArg (fun z => (p.1 : G) * z) hmem
        simpa using this
      have hpq2 : (q.2 : G) = (p.2 : G) := by
        have h2 : (p.2 : G) * (q.2 : G)⁻¹ = 1 := by rw [← h1, hmem]
        have h3 : (p.2 : G) = (q.2 : G) := by
          have := congrArg (fun z => z * (q.2 : G)) h2
          simpa [mul_assoc] using this
        exact h3.symm
      exact Prod.ext (Subtype.ext hpq1.symm) (Subtype.ext hpq2.symm)
    · intro z
      have hz : (z : G) ∈ (↑A : Set G) * (↑B : Set G) := by rw [← hcoe]; exact z.2
      rw [Set.mem_mul] at hz
      obtain ⟨a, ha, b, hb, hab⟩ := hz
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

/-- `C_Q(P) ⊓ Σ = ⊥`: `C_Q(P) ≤ Q` while `Σ ≤ W ≤ C_D(t) ≤ D = H ⊓ H^t`, and `Q ⊓ D = ⊥` in a
split rank-one datum. -/
private lemma CQ_inf_Sig {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Work.ThmF.ChV3.CQ Q P ⊓ Work.ThmF.ChV3.Sig H t P = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxCQ, hxSig⟩ := Subgroup.mem_inf.mp hx
  have hxQ : x ∈ Q := (Subgroup.mem_inf.mp hxCQ).1
  have hxW : x ∈ Work.ThmF.W H t := (Subgroup.mem_inf.mp hxSig).1
  have hxD : x ∈ twoPoint H t :=
    Work.ThmF.centD_le_twoPoint t (Work.ThmF.W_le_centD H t hxW)
  have hmem : x ∈ Q ⊓ twoPoint H t := ⟨hxQ, hxD⟩
  rw [Work.ThmF.split_inf_eq c.split] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem S1_centralizerP_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t)) :
    h15.R ⊓ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) = ⊥ ∧
      h15.R ⊔ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) = Work.ThmF.ChV3.CG P ∧
      Nat.card ↥(Work.ThmF.ChV3.CG P) = Nat.card h15.R * Nat.card ↥(Work.ThmF.ChV3.CQ Q P) *
        Nat.card ↥(Work.ThmF.ChV3.Sig H t P) := by
  classical
  -- ## Structural containments
  have hSigH : Work.ThmF.ChV3.Sig H t P ≤ H :=
    (inf_le_left :
      Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t).trans
      ((Work.ThmF.W_le_centD H t).trans
        ((Work.ThmF.centD_le_twoPoint t).trans inf_le_left))
  have hCQsigH : Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P ≤
      H ⊓ Work.ThmF.ChV3.CG P := by
    refine sup_le (le_inf ?_ inf_le_right) (le_inf hSigH inf_le_right)
    exact inf_le_left.trans c.split.le
  have hCQsigN : Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P ≤
      Subgroup.normalizer (h15.R : Set G) :=
    (hCQsigH.trans inf_le_right).trans h15.hRn
  -- ## Cardinality of `R`
  have hcardR : Nat.card h15.R = Nat.card P * orderOf (s * t) ^ h15.m := by
    rw [h15.hcardR, h7]
  -- ## `|Ω_P| = f^m`
  have hfix : (Submission.Blueprint.fixedPts H P).ncard = orderOf (s * t) ^ h15.m := by
    have h := Work.ThmF.ChV3.step6aux_count hC4 c
    rw [h15.hcq] at h
    exact h.symm
  -- ## The trivial intersections
  have hCQSig : Work.ThmF.ChV3.CQ Q P ⊓ Work.ThmF.ChV3.Sig H t P = ⊥ := CQ_inf_Sig c
  have hconj1 : h15.R ⊓ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) = ⊥ := by
    have hle : h15.R ⊓ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) ≤
        P ⊓ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) := by
      refine le_inf ?_ inf_le_right
      calc h15.R ⊓ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P)
          ≤ h15.R ⊓ (H ⊓ Work.ThmF.ChV3.CG P) :=
            le_inf inf_le_left (inf_le_right.trans hCQsigH)
        _ = P := S1_R_inf_CH_eq_P c h15 h7 hpf
    rw [S1_P_inf_CQ_sup_Sig c h15] at hle
    exact le_bot_iff.mp hle
  -- ## Cardinality of `C_G(P)`
  have hconj3 : Nat.card ↥(Work.ThmF.ChV3.CG P) =
      Nat.card h15.R * Nat.card ↥(Work.ThmF.ChV3.CQ Q P) *
        Nat.card ↥(Work.ThmF.ChV3.Sig H t P) := by
    rw [S1_CG_card_orbit c, hfix, S1_CH_card c h15, hcardR]
    ring
  -- ## The join
  have hSig_norm : Work.ThmF.ChV3.Sig H t P ≤
      Subgroup.normalizer (Work.ThmF.ChV3.CQ Q P : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro σ hσ cc hcc
    have hσC : σ ∈ Work.ThmF.ChV3.CG P := (Subgroup.mem_inf.mp hσ).2
    have hccC : cc ∈ Work.ThmF.ChV3.CG P := (Subgroup.mem_inf.mp hcc).2
    have hccQ : cc ∈ Q := (Subgroup.mem_inf.mp hcc).1
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.le_normalizer_iff.mp c.split.normal) σ (hSigH hσ) cc hccQ
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hσC hccC) (Subgroup.inv_mem _ hσC)
  have hcard_sup : Nat.card ↥(Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) =
      Nat.card ↥(Work.ThmF.ChV3.CQ Q P) * Nat.card ↥(Work.ThmF.ChV3.Sig H t P) :=
    card_sup_of_inf_eq_bot hSig_norm hCQSig
  have hconj2 : h15.R ⊔ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) =
      Work.ThmF.ChV3.CG P := by
    refine le_antisymm (sup_le h15.hRc (sup_le inf_le_right inf_le_right)) ?_
    have hle : h15.R ⊔ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) ≤
        Work.ThmF.ChV3.CG P := sup_le h15.hRc (sup_le inf_le_right inf_le_right)
    have hcard : Nat.card ↥(h15.R ⊔ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P)) =
        Nat.card ↥(Work.ThmF.ChV3.CG P) := by
      rw [card_sup_of_inf_eq_bot hCQsigN hconj1, hcard_sup, hconj3]
      ring
    have hset : (↑(h15.R ⊔ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P)) : Set G) =
        ↑(Work.ThmF.ChV3.CG P) := by
      apply Set.eq_of_subset_of_ncard_le hle
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact le_of_eq hcard.symm
    exact le_of_eq (SetLike.coe_injective hset).symm
  exact ⟨hconj1, hconj2, hconj3⟩

end Work.ThmF.ChV3.Prove
