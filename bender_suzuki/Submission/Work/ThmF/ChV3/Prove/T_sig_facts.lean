import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV3.Prove.S4_centD_not_stronglyReal
import Submission.Work.ThmF.ChV3.Prove.S3_T_facts
import Submission.Work.ThmF.ChV3.Prove.S2_commS_mem_R
import Submission.Work.ThmF.ChV3.Prove.S1_centralizerP_eq
import Submission.Work.ThmF.ChV3.Prove.S1_CH_aux
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV3.Prove.commutator_mem_centralizer_of_card_nine

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.T_sig_facts` — leaf **14a** of the Ch. V §3 second half

Peterfalvi II Ch. V §3 step (14a): in case (10-2) (`p = f = 3`, `m = 2`, `|C_Q(P)| = 8`,
`|Σ| = 3`), the subgroup `Σ = C_W(P)` acts faithfully on `T`, has `[T, Σ] ≤ Z₁ = ⟨st⟩` and
`C_T(Σ) = Z₁`.

* `|T| = 9`: `|T| = |P|^m` (`S3_T_facts`) and `|P|^m = |C_Q(P)| + 1 = 9` (`h15.hcq`, `d.cq8`).
* **Faithful.**  If `σ ∈ Σ` centralised `T`, then for `y ∈ C_Q(P)` the element `σ y σ⁻¹ ∈ C_Q(P)`
  (as `Σ ≤ N_G(C_Q(P))`) would act on `T` exactly as `y`; the action of `C_Q(P)` on `T^#` is free
  (`h15.hfpf` with `Ker = P`), so `σ y σ⁻¹ = y` for all `y`, i.e. `σ ∈ C_G(C_Q(P))`; with
  `σ ∈ D ∩ C_G(P)` this puts `σ ∈ Ker = P`, while `σ ∈ Σ ≤ W` and `W ⊓ P = ⊥`.
* **`C_T(Σ) = Z₁`.**  For `σ ∈ Σ^#` the fixed subgroup `C_T(σ)` is a proper subgroup of `T`
  (faithfulness) containing `Z₁ = ⟨st⟩` (as `Σ ≤ V ≤ C_G(s) ⊓ C_G(t)`), hence has order `3 = |Z₁|`.
* **`[T, Σ] ≤ Z₁`.**  For `b ∈ Σ^#`, `x ↦ [x, b]` is a homomorphism `T → T` (`T` abelian) with
  kernel `C_T(b) = Z₁`; its image `[T, b]` is a `b`-invariant subgroup of order `9/3 = 3`, hence —
  by `conj_eq_self_of_card_three` — is contained in `C_T(b) = Z₁`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

theorem T_sig_facts {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    (∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ≠ 1 → ∃ x ∈ T, σ * x * σ⁻¹ ≠ x) ∧
      (∀ a ∈ T, ∀ b ∈ Work.ThmF.ChV3.Sig H t P,
        a * b * a⁻¹ * b⁻¹ ∈ Work.ThmF.ChV3.Z1 s t) ∧
      T ⊓ Work.ThmF.ChV3.CG (Work.ThmF.ChV3.Sig H t P) = Work.ThmF.ChV3.Z1 s t := by
  classical
  -- ## 0. Structural facts
  have hTR : T ≤ h15.R := by rw [← h11.TPR]; exact le_sup_left
  have hTcomm : ∀ x y : G, x ∈ T → y ∈ T → x * y = y * x :=
    fun x y hx hy => mul_comm_of_mem h11.comm (hTR hx) (hTR hy)
  haveI hTcommI : IsMulCommutative ↥T :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hTcomm a b a.2 b.2))
  obtain ⟨hRinf, hRsup, hRcard⟩ := S1_centralizerP_eq hFT hC4 c h15 h7 hpf
  have h2 := S2_commS_mem_R hFT hC4 c hpf hRsup h15.hRn
  obtain ⟨hsTinv, hstT, hTexp, hTcard⟩ :=
    S3_T_facts hFT hC4 c hpf h15.m h15.hm h11 h7 h15.hcardR h15.hcq h2
  -- numeric facts
  have hP3 : Nat.card P = 3 := d.p3
  have hCQ8 : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 := d.cq8
  have hSig3 : Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 3 := d.sig3
  have hstord : orderOf (s * t) = 3 := by rw [← hpf, hP3]
  have hm9 : 3 ^ h15.m = 9 := by
    have h := h15.hcq
    rw [hCQ8, hstord] at h
    norm_num at h
    exact h.symm
  have hT9 : Nat.card ↥T = 9 := by rw [hTcard, hP3, hm9]
  have hTexp3 : ∀ x ∈ T, x ^ 3 = 1 := fun x hx => by
    have h := hTexp x hx
    rwa [hP3] at h
  have hZ1card : Nat.card ↥(Work.ThmF.ChV3.Z1 s t) = 3 := by
    rw [Work.ThmF.ChV3.Z1, Nat.card_zpowers, hstord]
  have hTne : T ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hT9; omega
  have hSne : Work.ThmF.ChV3.Sig H t P ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hSig3; omega
  obtain ⟨x₀, hx₀T, hx₀ne⟩ : ∃ x ∈ T, x ≠ 1 := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
    exact ⟨(a : G), a.2, fun h => ha (Subtype.ext h)⟩
  obtain ⟨σ₀, hσ₀, hσ₀ne⟩ : ∃ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ≠ 1 := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
    exact ⟨(a : G), a.2, fun h => ha (Subtype.ext h)⟩
  -- ## 1. `C_Q(P)` acts freely on `T^#` (`h15.hfpf` with `Ker = P`)
  have hfree : ∀ y ∈ Work.ThmF.ChV3.CQ Q P, ∀ x ∈ T, x ≠ 1 → y * x * y⁻¹ = x → y = 1 := by
    intro y hy x hxT hxne hfix
    have hxR : x ∈ h15.R := hTR hxT
    have hxnot : x ∉ Work.ThmF.ChV3.Ker H Q P t := by
      rw [h7]
      intro hxP
      exact hxne (by
        have hmem : x ∈ T ⊓ P := ⟨hxT, hxP⟩
        rwa [h11.TP, Subgroup.mem_bot] at hmem)
    refine h15.hfpf x hxR hxnot y hy ?_
    rw [hfix, mul_inv_cancel]
    exact (Work.ThmF.ChV3.Ker H Q P t).one_mem
  -- ## 2. the `C_Q(P)`-action on `T` is faithful
  have hCQfaith : ∀ y ∈ Work.ThmF.ChV3.CQ Q P, ∀ y' ∈ Work.ThmF.ChV3.CQ Q P,
      (∀ x ∈ T, y * x * y⁻¹ = y' * x * y'⁻¹) → y = y' := by
    intro y hy y' hy' hag
    have hz : y'⁻¹ * y ∈ Work.ThmF.ChV3.CQ Q P :=
      (Work.ThmF.ChV3.CQ Q P).mul_mem ((Work.ThmF.ChV3.CQ Q P).inv_mem hy') hy
    have hfixz : ∀ x ∈ T, (y'⁻¹ * y) * x * (y'⁻¹ * y)⁻¹ = x := by
      intro x hx
      have h := hag x hx
      rw [show (y'⁻¹ * y) * x * (y'⁻¹ * y)⁻¹ = y'⁻¹ * (y * x * y⁻¹) * y' by group, h]
      group
    have hz1 : y'⁻¹ * y = 1 := hfree (y'⁻¹ * y) hz x₀ hx₀T hx₀ne (hfixz x₀ hx₀T)
    calc y = y' * (y'⁻¹ * y) := by group
      _ = y' := by rw [hz1, mul_one]
  -- ## 3. `Σ ≤ …`
  have hSigW : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t := inf_le_left
  have hSigC : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  have hSigD : Work.ThmF.ChV3.Sig H t P ≤ twoPoint H t :=
    hSigW.trans ((Work.ThmF.W_le_centD H t).trans (Work.ThmF.centD_le_twoPoint t))
  have hSigNT : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.normalizer (T : Set G) :=
    le_trans le_sup_right h11.Tn
  have hSigNCQ : Work.ThmF.ChV3.Sig H t P ≤
      Subgroup.normalizer (Work.ThmF.ChV3.CQ Q P : Set G) :=
    le_trans le_sup_left (S1_CH_aux c h15).1
  have hSigP : Work.ThmF.ChV3.Sig H t P ⊓ P = ⊥ := (S1_CH_aux c h15).2.2
  have hSigCs : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.centralizer ({s} : Set G) :=
    hSigW.trans ((Work.ThmF.W_le_centD H t).trans
      (Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid))
  have hSigCt : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.centralizer ({t} : Set G) :=
    hSigW.trans ((Work.ThmF.W_le_centD H t).trans inf_le_right)
  -- `st` commutes with every element of `Σ`
  have hstcomm : ∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ * (s * t) = (s * t) * σ := by
    intro σ hσ
    have hσs : σ * s = s * σ := Subgroup.mem_centralizer_singleton_iff.mp (hSigCs hσ)
    have hσt : σ * t = t * σ := Subgroup.mem_centralizer_singleton_iff.mp (hSigCt hσ)
    calc σ * (s * t) = (σ * s) * t := by group
      _ = (s * σ) * t := by rw [hσs]
      _ = s * (σ * t) := by group
      _ = s * (t * σ) := by rw [hσt]
      _ = (s * t) * σ := by group
  -- ## 4. faithfulness (conjunct 1)
  have hfaith : ∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ≠ 1 → ∃ x ∈ T, σ * x * σ⁻¹ ≠ x := by
    intro σ hσ hσ1
    by_contra hcon
    push_neg at hcon
    have hσNT := hSigNT hσ
    have hσNQ := hSigNCQ hσ
    have hcen : ∀ y ∈ Work.ThmF.ChV3.CQ Q P, σ * y * σ⁻¹ = y := by
      intro y hy
      have hyN : y ∈ Subgroup.normalizer (T : Set G) := le_trans le_sup_left h11.Tn hy
      have hy' : σ * y * σ⁻¹ ∈ Work.ThmF.ChV3.CQ Q P :=
        (Subgroup.mem_normalizer_iff.mp hσNQ y).mp hy
      refine hCQfaith (σ * y * σ⁻¹) hy' y hy ?_
      intro x hx
      have hσx : σ⁻¹ * x * σ = x := by
        calc σ⁻¹ * x * σ = σ⁻¹ * (σ * x * σ⁻¹) * σ := by rw [hcon x hx]
          _ = x := by group
      have hyxT : y * x * y⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hyN x).mp hx
      calc (σ * y * σ⁻¹) * x * (σ * y * σ⁻¹)⁻¹
          = σ * (y * (σ⁻¹ * x * σ) * y⁻¹) * σ⁻¹ := by group
        _ = σ * (y * x * y⁻¹) * σ⁻¹ := by rw [hσx]
        _ = y * x * y⁻¹ := hcon (y * x * y⁻¹) hyxT
    have hσKer : σ ∈ Work.ThmF.ChV3.Ker H Q P t := by
      refine ⟨⟨hSigD hσ, ?_⟩, hSigC hσ⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
        have h := congrArg (fun z => z * σ) (hcen y hy)
        rw [show (σ * y * σ⁻¹) * σ = σ * y by group] at h
        exact h.symm)
    have hσP : σ ∈ P := by rw [← h7]; exact hσKer
    have hmem : σ ∈ Work.ThmF.ChV3.Sig H t P ⊓ P := ⟨hσ, hσP⟩
    rw [hSigP, Subgroup.mem_bot] at hmem
    exact hσ1 hmem
  -- ## 5. `C_T(σ) = Z₁` for `σ ∈ Σ^#`
  have hCTeq : ∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ≠ 1 →
      T ⊓ Subgroup.centralizer ({σ} : Set G) = Work.ThmF.ChV3.Z1 s t := by
    intro σ hσ hσ1
    have hZ1le : Work.ThmF.ChV3.Z1 s t ≤ T ⊓ Subgroup.centralizer ({σ} : Set G) := by
      refine Subgroup.zpowers_le.mpr ⟨hstT, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hstcomm σ hσ).symm
    have hcard3 : Nat.card ↥(T ⊓ Subgroup.centralizer ({σ} : Set G)) = 3 := by
      have hdvd9 : Nat.card ↥(T ⊓ Subgroup.centralizer ({σ} : Set G)) ∣ 3 ^ 2 := by
        have h9 : (3:ℕ) ^ 2 = Nat.card ↥T := by rw [hT9]; norm_num
        rw [h9]; exact Subgroup.card_dvd_of_le inf_le_left
      have hdvd3 : 3 ∣ Nat.card ↥(T ⊓ Subgroup.centralizer ({σ} : Set G)) := by
        rw [← hZ1card]; exact Subgroup.card_dvd_of_le hZ1le
      have hne9 : Nat.card ↥(T ⊓ Subgroup.centralizer ({σ} : Set G)) ≠ 9 := by
        intro h9
        have hST : T ⊓ Subgroup.centralizer ({σ} : Set G) = T :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, hT9])
        have hle : T ≤ Subgroup.centralizer ({σ} : Set G) := hST ▸ inf_le_right
        have hcenT : ∀ x ∈ T, σ * x * σ⁻¹ = x := by
          intro x hx
          have h1 : σ * x = x * σ :=
            (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
          rw [h1]; group
        obtain ⟨y, hyT, hyne⟩ := hfaith σ hσ hσ1
        exact hyne (hcenT y hyT)
      rcases (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp hdvd9 with ⟨j, hjle, hj⟩
      interval_cases j
      · rw [hj] at hdvd3; norm_num at hdvd3
      · simpa using hj
      · exact absurd (by simpa using hj) hne9
    exact (Subgroup.eq_of_le_of_card_ge hZ1le (by rw [hcard3, hZ1card])).symm
  refine ⟨hfaith, ?_, ?_⟩
  · -- ## 6. `[T, Σ] ≤ Z₁`
    intro a ha b hb
    rcases eq_or_ne b 1 with rfl | hb1
    · simp
    · -- `b ≠ 1`: `b` has order `3`, `C_T(b) = Z₁`, and the commutator map kills `Z₁`
      have hb3 : b ^ 3 = 1 := by
        have hdvd := Subgroup.orderOf_dvd_natCard (Work.ThmF.ChV3.Sig H t P) hb
        rw [hSig3] at hdvd
        rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf b) hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hb1
        · rw [← h]; exact pow_orderOf_eq_one b
      have hfix : Nat.card ↥(T ⊓ Subgroup.centralizer ({b} : Set G)) = 3 := by
        rw [hCTeq b hb hb1, hZ1card]
      have hmem :=
        commutator_mem_centralizer_of_card_nine hT9 hTcommI (hSigNT hb) hb3 hfix a ha
      rwa [hCTeq b hb hb1] at hmem
  · -- ## 7. `C_T(Σ) = Z₁`
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
      have hxcomm : σ₀ * x = x * σ₀ := Subgroup.mem_centralizer_iff.mp hxC σ₀ hσ₀
      have hin : x ∈ T ⊓ Subgroup.centralizer ({σ₀} : Set G) :=
        ⟨hxT, Subgroup.mem_centralizer_singleton_iff.mpr hxcomm.symm⟩
      rwa [hCTeq σ₀ hσ₀ hσ₀ne] at hin
    · intro x hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.zpowers_le.mpr hstT) hx
      · exact (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_iff.mpr (fun σ hσ => hstcomm σ hσ))) hx

end Work.ThmF.ChV3.Prove
