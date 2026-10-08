import Mathlib
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.Prove.xDvdOmega
import Submission.Work.ThmF.ChV3.Prove.S1_centralizerP_eq
import Submission.Work.ThmF.ChV3.Prove.S2_commS_mem_R
import Submission.Work.ThmF.ChV3.Prove.S3_T_facts
import Submission.Work.ThmF.ChV3.Prove.S4_centD_not_stronglyReal
import Submission.Work.ThmF.ChV3.Prove.S5_cst_inf_cs
import Submission.Work.ThmF.ChV3.Prove.A_le_cst
import Submission.Work.ThmF.ChV3.Prove.m_eq_one_101
import Submission.Work.ThmF.ChV3.Prove.sig_eq_bot_of_m_one
import Submission.Work.ThmF.ChV3.Prove.normal_sylow_of_card
import Submission.Work.ThmF.ChV3.Prove.centralizer_le_H_of_mem_Q
import Submission.Work.ThmF.ChV3.Prove.pPart_H_101
import Submission.Work.ThmF.ChV3.Prove.R_weaklyClosed_101
import Submission.Work.ThmF.ChV3.Prove.NR_hasNormalIndexP_101
import Submission.Work.ThmF.ChV3.Prove.hD_of_chain15

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Step16Step12` — §3 step (12): case (10-1) is impossible

The lead's pass-16 design (`ThmF/_design16/ThmF16.lean`, `step12`) proved from the leaves.  Here the
leaves are the modules under `Submission/Work/ThmF/ChV3/Prove/` (one file per leaf).

`HallWielandtProp` is applied to `A := R` (abelian by step (11), weakly closed in the Sylow
`p`-subgroup `R₁` of `N_G(R)` by leaf `R_weaklyClosed_101`), and `N_G(R)` has a normal subgroup of
index `p` by leaf `NR_hasNormalIndexP_101`; `G` simple gives the contradiction.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3

open Work.ThmF

variable {G : Type} [Group G] [Finite G]

/-- `|G|` is even (`H` has even order). -/
theorem even_card_G {H Q : Subgroup G} {t s r : G} {P : Subgroup G} (c : CtxF H Q t s r P) :
    Even (Nat.card G) := by
  obtain ⟨k, hk⟩ := split_even_card_H c.split
  obtain ⟨n, hn⟩ := Subgroup.card_subgroup_dvd_card H
  exact ⟨k * n, by rw [hn, hk]; ring⟩

/-- Commutativity of two elements of a commutative subgroup. -/
theorem comm_of_isMulCommutative {R : Subgroup G} (h : IsMulCommutative ↥R) :
    ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
  intro x hx y hy
  have := h.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

/-- **§3 step (12)**: case (10-1) is impossible ("we are in case (10-2)"). -/
theorem step12 (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (hHW : HallWielandtProp)
    {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : CtxF H Q t s r P) (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P)
    (hpf : Nat.card P = orderOf (s * t)) {T : Subgroup G} (h11 : Step11Out H Q t P h15.R T)
    (h6 : oddPart Q = ⊥ → IsMulCommutative ↥(CQ Q P) → Sig H t P = ⊥)
    (h8 : oddPart Q ≠ ⊥ → Work.ThmF.Prove.Step8Out H Q t P)
    (hH : Nat.card ↥H = Nat.card Q * Nat.card ↥(twoPoint H t))
    (hD : Nat.card ↥(twoPoint H t) = (2 ^ Nat.card P - 1) * Nat.card ↥(W H t) * Nat.card P)
    (hQ : ¬ Nat.card P ∣ Nat.card Q)
    (hSigW : ¬ Nat.card P ∣ Nat.card ↥(Sig H t P) → ¬ Nat.card P ∣ Nat.card ↥(W H t))
    (h101 : Case101 H t P h15.m) : False := by
  classical
  have hp : (Nat.card P).Prime := c.P_prime
  have : Fact (Nat.card P).Prime := ⟨hp⟩
  obtain ⟨hm1, hNR⟩ :=
    Work.ThmF.ChV3.Prove.m_eq_one_101 hFT hC4 c hpf h15.hm h15.hRc h15.hRn h7 h15.hcardR
      h15.hcq h15.hNG h11 h101
  have hsig : Sig H t P = ⊥ :=
    Work.ThmF.ChV3.Prove.sig_eq_bot_of_m_one c h15 hpf h6 h8 hm1
  have hGp : pPart (Nat.card P) (Nat.card G) = Nat.card P ^ 3 := by
    have := h101.2; rw [hm1] at this; exact this
  -- `|N_G(R)| = p³ (p − 1)`
  have hNRcard : Nat.card ↥(NG h15.R) = Nat.card P ^ 3 * (Nat.card P - 1) := by
    obtain ⟨-, -, hCG⟩ := Work.ThmF.ChV3.Prove.S1_centralizerP_eq hFT hC4 c h15 h7 hpf
    have hR : Nat.card h15.R = Nat.card P * Nat.card P := by
      have := h15.hcardR; rw [h7, ← hpf, hm1, pow_one] at this; exact this
    have hcq : Nat.card ↥(CQ Q P) = Nat.card P - 1 := by
      have := h15.hcq; rw [← hpf, hm1, pow_one] at this; omega
    have hS : Nat.card ↥(Sig H t P) = 1 := by rw [hsig]; exact Subgroup.card_bot
    rw [hNR, hCG, hR, hcq, hS]; ring
  -- the normal Sylow `R₁` of `N_G(R)`
  have hRp : IsPGroup (Nat.card P) h15.R := by
    apply IsPGroup.of_card
    have := h15.hcardR; rw [h7, ← hpf] at this
    rw [this, ← pow_succ']
  obtain ⟨R1, hRR1, hR1N, hR1c, hR1n⟩ :=
    Work.ThmF.ChV3.Prove.normal_sylow_of_card hp (NG h15.R) h15.R
      (Subgroup.le_normalizer) le_rfl hRp hNRcard
  -- small centralisers
  have hcb : ∀ x ∈ CQ Q P, x ≠ 1 → ∀ X : Subgroup G, IsPGroup (Nat.card P) X →
      X ≤ Subgroup.centralizer ({x} : Set G) → Nat.card X ≤ Nat.card P := by
    intro x hx hx1 X hXp hXc
    have hXH : X ≤ H :=
      hXc.trans (Work.ThmF.ChV3.Prove.centralizer_le_H_of_mem_Q c.split x hx.1 hx1)
    have hHp := Work.ThmF.ChV3.Prove.pPart_H_101 c hH hD hQ (hSigW h101.1)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hXp)
    have hdvd : Nat.card X ∣ Nat.card ↥H := Subgroup.card_dvd_of_le hXH
    have hH0 : Nat.card ↥H ≠ 0 := Nat.card_pos.ne'
    have hk' : k ≤ (Nat.card ↥H).factorization (Nat.card P) :=
      (hp.pow_dvd_iff_le_factorization hH0).mp (hk ▸ hdvd)
    have hpk : Nat.card P ^ k ∣ Nat.card P := by
      have h1 : Nat.card P ^ k ∣ pPart (Nat.card P) (Nat.card ↥H) := pow_dvd_pow (Nat.card P) hk'
      rwa [hHp] at h1
    rw [hk]
    exact Nat.le_of_dvd hp.pos hpk
  have hwc := Work.ThmF.ChV3.Prove.R_weaklyClosed_101 hFT hC4 c h15 h7 hpf h11 hm1 hsig hGp
    hcb hNRcard hRR1 hR1N hR1c hR1n
  have hNI := Work.ThmF.ChV3.Prove.NR_hasNormalIndexP_101 hFT hC4 c h15 h7 hpf h11 hm1 hsig
    hGp hcb hNRcard hRR1 hR1N hR1c hR1n
  -- Hall–Wielandt for `A = R` in the Sylow `R₁`
  have hR1syl : Nat.card R1 = Nat.card P ^ (Nat.card G).factorization (Nat.card P) := by
    rw [hR1c]; unfold pPart at hGp; rw [hGp]
  let S : Sylow (Nat.card P) G := Sylow.ofCard R1 hR1syl
  have hSR1 : (S : Subgroup G) = R1 := Sylow.coe_ofCard R1 hR1syl
  have hiff := hHW G (Nat.card P) hp S h15.R (by rw [hSR1]; exact hRR1)
    (by intro g hg; rw [hSR1] at hg; exact hwc g hg) (comm_of_isMulCommutative h11.comm)
  have hG : HasNormalIndexP (Nat.card P) G := hiff.mpr hNI
  have hp2 : Nat.card P ≠ 2 := by
    intro h2
    have hodd := split_odd_card_twoPoint c.split
    have hdvd : Nat.card P ∣ Nat.card ↥(twoPoint H t) :=
      Subgroup.card_dvd_of_le (c.P_le.trans inf_le_left)
    rw [h2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  exact Work.ThmF.Prove.simple_not_hasNormalIndexP hp hp2 c.simple (even_card_G c) hG

end Work.ThmF.ChV3
