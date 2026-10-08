import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.coarseFrame_defs
import Submission.Work.ThmF.ChV12.prop1a
import Submission.Work.Higman.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- A free action of a finite group on a finite type has group order dividing the cardinality. -/
theorem card_dvd_card_of_free {Γ X : Type*} [Group Γ] [MulAction Γ X] [Fintype Γ] [Fintype X]
    (hfree : ∀ g : Γ, g ≠ 1 → ∀ x : X, g • x ≠ x) : Nat.card Γ ∣ Nat.card X := by
  classical
  haveI hF : ∀ g : Γ, Fintype ↑(MulAction.fixedBy X g) := fun g => Fintype.ofFinite _
  haveI hQ : Fintype (Quotient (MulAction.orbitRel Γ X)) := Fintype.ofFinite _
  have hburnside := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group Γ X
  have h1card : Fintype.card ↑(MulAction.fixedBy X (1 : Γ)) = Fintype.card X := by simp
  have hsum : (∑ g : Γ, Fintype.card ↑(MulAction.fixedBy X g)) = Fintype.card X := by
    rw [← h1card]
    refine Fintype.sum_eq_single 1 ?_
    intro g hg
    haveI : IsEmpty ↑(MulAction.fixedBy X g) :=
      ⟨fun y => hfree g hg y (MulAction.mem_fixedBy.mp y.2)⟩
    rw [Fintype.card_eq_zero]
  rw [hsum] at hburnside
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact ⟨Fintype.card (Quotient (MulAction.orbitRel Γ X)), by rw [mul_comm]; exact hburnside⟩

theorem caseC_zeta_action {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1)
    (hW : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w →
      x ∈ Work.ThmF.Q0sub H)
    {ζ : G} (hζ : ζ ∈ Work.ThmF.W H t) (hζ1 : ζ ≠ 1) :
    orderOf ζ ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1 ∧
    (∀ x : ↥Q, ζ⁻¹ * (x : G) * ζ * (x : G)⁻¹ ∈ Work.ThmF.Q0sub H →
      (x : G) ∈ Work.ThmF.Q0sub H) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- ## 0. Basic structural facts
  have hWne : Work.ThmF.W H t ≠ ⊥ := caseC_W_ne_bot (Q := Q) hζ hζ1
  have hKset : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    (caseC_Ksub_cyc hS hC4 hWne).1
  have hZ0leQ : Work.ThmF.Q0sub H ≤ Q := Q0sub_le_Q hS.split
  have hZ0central : ∀ z ∈ Work.ThmF.Q0sub H, ∀ x ∈ Q, z * x = x * z :=
    caseC_Q0sub_central hS hC4
  have hZ0sq : ∀ z ∈ Work.ThmF.Q0sub H, z * z = 1 := caseC_mem_Q0sub_iff hS hC4
  have hrowZ0 : Nat.card ↥(Work.ThmF.Q0sub H)
      = (involutions (H : Set G)).ncard + 1 := caseC_card_Q0sub_eq hS hC4
  have hcardK : Nat.card ↥(Work.ThmF.Ksub H t) = (involutions (H : Set G)).ncard :=
    caseC_card_Ksub hS hC4 hWne
  have hKcardsub : Nat.card ↥(Work.ThmF.Ksub H t) = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
    rw [hcardK, hrowZ0]; omega
  -- `ζ ∈ D = twoPoint H t`
  have hζD : ζ ∈ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.centD_le_twoPoint t (Work.ThmF.W_le_centD H t hζ)
  have hζH : ζ ∈ H := (Subgroup.mem_inf.mp hζD).1
  have hZpD : Subgroup.zpowers ζ ≤ Submission.Blueprint.twoPoint H t := by
    intro p hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    exact (Submission.Blueprint.twoPoint H t).zpow_mem hζD j
  have hZpH : ∀ p ∈ Subgroup.zpowers ζ, p ∈ H := fun p hp => (Subgroup.mem_inf.mp (hZpD hp)).1
  have hζodd : Odd (orderOf ζ) := by
    have hodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
      Work.ThmF.split_odd_card_twoPoint hS.split
    have hdvd : orderOf ζ ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
      rw [Subgroup.orderOf_coe (⟨ζ, hζD⟩ : ↥(Submission.Blueprint.twoPoint H t))]
      exact orderOf_dvd_natCard _
    exact hodd.of_dvd_nat hdvd
  -- `ζ` centralises `Q₀`
  have hζC0 : ∀ z ∈ Work.ThmF.Q0sub H, ζ * z = z * ζ := by
    have hP4 := (hC4 G hS.situation H hS.split.stronglyEmbedded t hS.split.invol
      hS.split.not_mem).2.2.2.2.1
    have hmem : ζ ∈ Submission.Blueprint.twoPoint H t ⊓
        Subgroup.centralizer (involutions (H : Set G)) := by
      rw [← hP4]
      exact ⟨Work.ThmF.W_le_centD H t hζ, (Subgroup.mem_inf.mp hζ).2⟩
    have hcent : ∀ u ∈ involutions (H : Set G), u * ζ = ζ * u :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hmem).2
    intro z hz
    have hz' : z ∈ Work.ThmF.Q0 H := by
      rw [← caseC_Q0sub_eq_Q0 hS hC4]; exact hz
    rcases hz' with h | rfl
    · exact (hcent z h).symm
    · simp
  have hζZ0c : ζ ∈ Subgroup.centralizer (Work.ThmF.Q0sub H : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun z hz => (hζC0 z hz).symm)
  -- `ζ` commutes with `K`
  have hζK : ∀ k ∈ Work.ThmF.Ksub H t, ζ * k = k * ζ := by
    intro k hk
    have hk' : k ∈ (Work.ThmF.Kset H t : Set G) := by rw [← hKset]; exact hk
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hζ).2 k hk').symm
  -- `Q₀` is `H`-invariant
  have hZ0inv : ∀ d ∈ H, ∀ z ∈ Work.ThmF.Q0sub H, d * z * d⁻¹ ∈ Work.ThmF.Q0sub H := by
    intro d hd z hz
    have hz' : z ∈ Work.ThmF.Q0 H := by rw [← caseC_Q0sub_eq_Q0 hS hC4]; exact hz
    rcases hz' with ⟨hzH, hzo⟩ | rfl
    · exact Work.ThmF.Q0_le_Q0sub H (Or.inl ⟨H.mul_mem (H.mul_mem hd hzH) (H.inv_mem hd),
        by rw [Work.ThmF.Bender.orderOf_conj_eq]; exact hzo⟩)
    · simp
  -- every square of an element of `Q` lies in `Q₀`
  have hsq0 : ∀ x : ↥Q, (x : G) * (x : G) ∈ Work.ThmF.Q0sub H := by
    have hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
      Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr
        ⟨caseC_isSuzuki2Grp hS hC4 hnab hZ hWne⟩
    have hZc : ∀ z : ↥Q, z ∈ Subgroup.center ↥Q ↔ z ^ 2 = 1 := (hHig ↥Q hSuz).1
    intro x
    have hmem : x ^ 2 ∈ Subgroup.center ↥Q := (hHig ↥Q hSuz).2.1 x
    have hsq : x ^ 2 * x ^ 2 = 1 := by
      simpa [pow_two] using (hZc (x ^ 2)).mp hmem
    have hx2 : ((x ^ 2 : ↥Q) : G) ∈ Work.ThmF.Q0sub H := (hZ (x ^ 2)).mpr hsq
    simpa [pow_two, Subgroup.coe_mul] using hx2
  -- powers of `ζ` centralise `Q₀` and commute with `K`
  have hzpZ0 : ∀ z ∈ Subgroup.zpowers ζ, ∀ y ∈ Work.ThmF.Q0sub H, z * y = y * z := by
    intro z hz y hy
    have hle : Subgroup.zpowers ζ ≤ Subgroup.centralizer (Work.ThmF.Q0sub H : Set G) :=
      Subgroup.zpowers_le.mpr hζZ0c
    exact (Subgroup.mem_centralizer_iff.mp (hle hz) y hy).symm
  have hzpK : ∀ z ∈ Subgroup.zpowers ζ, ∀ k ∈ Work.ThmF.Ksub H t, z * k = k * z := by
    intro z hz k hk
    have hle : Subgroup.zpowers ζ ≤ Subgroup.centralizer (Work.ThmF.Ksub H t : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr (fun k hk => (hζK k hk).symm))
    exact (Subgroup.mem_centralizer_iff.mp (hle hz) k hk).symm
  -- ## 1. The second assertion: `ζ` acts fixed-point-freely modulo `Q₀`
  have hpart2 : ∀ x : ↥Q, ζ⁻¹ * (x : G) * ζ * (x : G)⁻¹ ∈ Work.ThmF.Q0sub H →
      (x : G) ∈ Work.ThmF.Q0sub H := by
    intro x hx
    by_contra hx0
    have hPodd : Odd (Nat.card ↥(Subgroup.zpowers ζ)) := by
      rw [Nat.card_zpowers]; exact hζodd
    have hxcomm : Commute (x : G) (ζ⁻¹ * (x : G) * ζ * (x : G)⁻¹) :=
      (hZ0central _ hx (x : G) x.2).symm
    have hstep : ∃ c ∈ Work.ThmF.Q0sub H, ζ * (x : G) * ζ⁻¹ = (x : G) * c := by
      obtain ⟨c, hc, hce⟩ : ∃ c, c ∈ Work.ThmF.Q0sub H ∧
          ζ⁻¹ * (x : G) * ζ = (x : G) * c :=
        ⟨ζ⁻¹ * (x : G) * ζ * (x : G)⁻¹, hx, by
          rw [hxcomm.eq]; group⟩
      have hcz : ζ * c * ζ⁻¹ ∈ Work.ThmF.Q0sub H := hZ0inv ζ hζH c hc
      refine ⟨(ζ * c * ζ⁻¹)⁻¹, (Work.ThmF.Q0sub H).inv_mem hcz, ?_⟩
      have hcomm0 : Commute (ζ * c * ζ⁻¹) (x : G) := (hZ0central _ hcz (x : G) x.2)
      have hcomm : Commute ((ζ * c * ζ⁻¹)⁻¹) (x : G) := hcomm0.inv_left
      have h2 : ζ * (x : G) * ζ⁻¹ = (ζ * c * ζ⁻¹)⁻¹ * (x : G) := by
        have h1 : (x : G) = (ζ * c * ζ⁻¹) * (ζ * (x : G) * ζ⁻¹) := by
          calc (x : G) = ζ * (ζ⁻¹ * (x : G) * ζ) * ζ⁻¹ := by group
            _ = ζ * ((x : G) * c) * ζ⁻¹ := by rw [hce]
            _ = ζ * (c * (x : G)) * ζ⁻¹ := by rw [hZ0central c hc (x : G) x.2]
            _ = (ζ * c * ζ⁻¹) * (ζ * (x : G) * ζ⁻¹) := by group
        have h2 : ζ * (x : G) * ζ⁻¹ = (ζ * c * ζ⁻¹)⁻¹ * (x : G) := by
          have h := congrArg (fun y => (ζ * c * ζ⁻¹)⁻¹ * y) h1
          simpa [mul_assoc] using h.symm
        exact h2
      rw [h2, hcomm.eq]
    -- the natural-number iteration
    have hiter : ∀ j : ℕ, ∃ c ∈ Work.ThmF.Q0sub H,
        ζ ^ j * (x : G) * (ζ ^ j)⁻¹ = (x : G) * c := by
      intro j
      induction j with
      | zero => exact ⟨1, (Work.ThmF.Q0sub H).one_mem, by simp⟩
      | succ j ih =>
        obtain ⟨c, hc, hce⟩ := ih
        obtain ⟨c₁, hc₁, hc₁e⟩ := hstep
        refine ⟨c * (ζ ^ j * c₁ * (ζ ^ j)⁻¹),
          (Work.ThmF.Q0sub H).mul_mem hc (by simpa using hZ0inv _ (H.pow_mem hζH j) c₁ hc₁), ?_⟩
        have h1 : ζ ^ j * (ζ * (x : G) * ζ⁻¹) * (ζ ^ j)⁻¹ =
            (x : G) * (c * (ζ ^ j * c₁ * (ζ ^ j)⁻¹)) := by
          rw [hc₁e]
          rw [show ζ ^ j * ((x : G) * c₁) * (ζ ^ j)⁻¹ =
              (ζ ^ j * (x : G) * (ζ ^ j)⁻¹) * (ζ ^ j * c₁ * (ζ ^ j)⁻¹) from by group]
          rw [hce]
          group
        calc ζ ^ (j + 1) * (x : G) * (ζ ^ (j + 1))⁻¹
            = ζ ^ j * (ζ * (x : G) * ζ⁻¹) * (ζ ^ j)⁻¹ := by rw [pow_succ]; group
          _ = (x : G) * (c * (ζ ^ j * c₁ * (ζ ^ j)⁻¹)) := h1
    -- conjugation by any element of `⟨ζ⟩`
    have hconj : ∀ p ∈ Subgroup.zpowers ζ, ∃ c ∈ Work.ThmF.Q0sub H,
        p * (x : G) * p⁻¹ = (x : G) * c := by
      intro p hp
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      by_cases hj : (0 : ℤ) ≤ j
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = (k : ℤ) :=
          ⟨j.toNat, (Int.toNat_of_nonneg hj).symm⟩
        simpa using hiter k
      · have hj' : j < 0 := by omega
        obtain ⟨k, hk⟩ : ∃ k : ℕ, j = -((k : ℤ)) := ⟨(-j).toNat, by omega⟩
        rw [hk, zpow_neg, zpow_natCast]
        obtain ⟨c, hc, hce⟩ := hiter k
        have hc' : (ζ ^ k)⁻¹ * c * ζ ^ k ∈ Work.ThmF.Q0sub H := by
          simpa using hZ0inv _ (H.inv_mem (H.pow_mem hζH k)) c hc
        refine ⟨((ζ ^ k)⁻¹ * c * ζ ^ k)⁻¹, (Work.ThmF.Q0sub H).inv_mem hc', ?_⟩
        have h1 : (x : G) =
            ((ζ ^ k)⁻¹ * (x : G) * ζ ^ k) * ((ζ ^ k)⁻¹ * c * ζ ^ k) := by
          calc (x : G) = (ζ ^ k)⁻¹ * ((x : G) * c) * ζ ^ k := by rw [← hce]; group
            _ = ((ζ ^ k)⁻¹ * (x : G) * ζ ^ k) * ((ζ ^ k)⁻¹ * c * ζ ^ k) := by group
        have h2 : (ζ ^ k)⁻¹ * (x : G) * ((ζ ^ k)⁻¹)⁻¹ =
            (x : G) * ((ζ ^ k)⁻¹ * c * ζ ^ k)⁻¹ := by
          rw [inv_inv]
          exact eq_mul_inv_of_mul_eq h1.symm
        exact h2
    have hfix : ∀ p ∈ Subgroup.zpowers ζ, p⁻¹ * (x : G) * p * (x : G)⁻¹ ∈
        Work.ThmF.Q0sub H := by
      intro p hp
      obtain ⟨c, hc, hce⟩ := hconj p hp
      have hpH : p ∈ H := hZpH p hp
      have hc' : p⁻¹ * c * p ∈ Work.ThmF.Q0sub H := by
        simpa using hZ0inv p⁻¹ (H.inv_mem hpH) c hc
      have hcomm0 : Commute (p⁻¹ * c * p) (x : G) := (hZ0central _ hc' (x : G) x.2)
      have hcomm : Commute ((p⁻¹ * c * p)⁻¹) (x : G) := hcomm0.inv_left
      have h1 : p⁻¹ * (x : G) * p = (x : G) * (p⁻¹ * c * p)⁻¹ := by
        have h2 : (x : G) = (p⁻¹ * (x : G) * p) * (p⁻¹ * c * p) := by
          calc (x : G) = p⁻¹ * ((x : G) * c) * p := by rw [← hce]; group
            _ = (p⁻¹ * (x : G) * p) * (p⁻¹ * c * p) := by group
        exact eq_mul_inv_of_mul_eq h2.symm
      have hgoal : (x : G) * (p⁻¹ * c * p)⁻¹ * (x : G)⁻¹ = (p⁻¹ * c * p)⁻¹ := by
        rw [← hcomm.eq]; group
      rw [h1, hgoal]
      exact (Work.ThmF.Q0sub H).inv_mem hc'
    obtain ⟨y, hyQ, hy0, hyfix⟩ :=
      caseC_exists_fixed_of_fixed_mod_Q0 hS hC4 hZpD hPodd x.2 hx0 hfix
    have hycomm : ζ * y = y * ζ := by
      have h1 : ζ⁻¹ * y * ζ = y := hyfix ζ (Subgroup.mem_zpowers ζ)
      calc ζ * y = ζ * (ζ⁻¹ * y * ζ) := by rw [h1]
        _ = y * ζ := by group
    exact hy0 (hW ζ hζ hζ1 y hyQ hycomm)
  refine ⟨?_, hpart2⟩
  -- ## 2. The first assertion.
  have hKsubNQ : ∀ k ∈ Work.ThmF.Ksub H t, k ∈ Subgroup.normalizer (Q : Set G) := by
    intro k hk
    exact hS.split.normal (Subgroup.mem_inf.mp (Work.ThmF.Ksub_le_twoPoint (H := H) t hk)).1
  have hZpNQ : ∀ z ∈ Subgroup.zpowers ζ, z ∈ Subgroup.normalizer (Q : Set G) := by
    intro z hz
    exact hS.split.normal (hZpH z hz)
  have hZpW : Subgroup.zpowers ζ ≤ Work.ThmF.W H t := Subgroup.zpowers_le.mpr hζ
  let act : (↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ)) →
      {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H} →
      {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H} :=
    fun p x => ⟨⟨(p.1 : G) * (p.2 : G) * (x.1 : G) * (p.2 : G)⁻¹ * (p.1 : G)⁻¹, by
        have hmem : (p.1 : G) * (p.2 : G) ∈ Subgroup.normalizer (Q : Set G) :=
          Subgroup.mul_mem _ (hKsubNQ (p.1 : G) p.1.2) (hZpNQ (p.2 : G) p.2.2)
        have hx : (p.1 : G) * (p.2 : G) * (x.1 : G) * ((p.1 : G) * (p.2 : G))⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hmem (x.1 : G)).mp x.1.2
        rw [mul_inv_rev] at hx
        simpa only [mul_assoc] using hx⟩, by
      intro hcon
      have hdH : (p.1 : G) * (p.2 : G) ∈ H :=
        H.mul_mem (Subgroup.mem_inf.mp (Work.ThmF.Ksub_le_twoPoint (H := H) t p.1.2)).1
          (hZpH (p.2 : G) p.2.2)
      have hz : (p.1 : G) * (p.2 : G) * (x.1 : G) * (p.2 : G)⁻¹ * (p.1 : G)⁻¹ ∈
          Work.ThmF.Q0sub H := hcon
      have hconj : ((p.1 : G) * (p.2 : G))⁻¹ *
          ((p.1 : G) * (p.2 : G) * (x.1 : G) * (p.2 : G)⁻¹ * (p.1 : G)⁻¹) *
          ((p.1 : G) * (p.2 : G)) ∈ Work.ThmF.Q0sub H := by
        simpa using hZ0inv ((p.1 : G) * (p.2 : G))⁻¹ (H.inv_mem hdH) _ hz
      have heq : ((p.1 : G) * (p.2 : G))⁻¹ *
          ((p.1 : G) * (p.2 : G) * (x.1 : G) * (p.2 : G)⁻¹ * (p.1 : G)⁻¹) *
          ((p.1 : G) * (p.2 : G)) = (x.1 : G) := by group
      exact x.2 (by rw [← heq]; exact hconj)⟩
  have hact : ∀ (g : ↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ))
      (y : {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H}),
      (((act g y).1 : ↥Q) : G) =
        (g.1 : G) * (g.2 : G) * (y.1 : G) * (g.2 : G)⁻¹ * (g.1 : G)⁻¹ := fun g y => rfl
  letI : MulAction (↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ))
      {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H} :=
    { smul := act
      one_smul := fun x => Subtype.ext (Subtype.ext (by
        change (((act 1 x).1 : ↥Q) : G) = (((x.1 : ↥Q) : G))
        rw [hact]
        simp only [Prod.fst_one, Prod.snd_one, Subgroup.coe_one, one_mul, inv_one]
        group))
      mul_smul := fun p q x => Subtype.ext (Subtype.ext (by
        have hc : (p.2 : G) * (q.1 : G) = (q.1 : G) * (p.2 : G) := hzpK p.2 p.2.2 q.1 q.1.2
        have hc' : (p.2 : G)⁻¹ * (q.1 : G)⁻¹ = (q.1 : G)⁻¹ * (p.2 : G)⁻¹ := by
          rw [← mul_inv_rev (q.1 : G) (p.2 : G), ← mul_inv_rev (p.2 : G) (q.1 : G), hc]
        have hca : ∀ Z : G, (q.1 : G) * ((p.2 : G) * Z) = (p.2 : G) * ((q.1 : G) * Z) := by
          intro Z; rw [← mul_assoc, ← hc, mul_assoc]
        have hcb : ∀ Z : G, (p.2 : G)⁻¹ * ((q.1 : G)⁻¹ * Z) = (q.1 : G)⁻¹ * ((p.2 : G)⁻¹ * Z) := by
          intro Z; rw [← mul_assoc, hc', mul_assoc]
        change (((act (p * q) x).1 : ↥Q) : G) = (((act p (act q x)).1 : ↥Q) : G)
        rw [hact (p * q) x, hact p (act q x), hact q x]
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev]
        simp only [mul_assoc]
        rw [hca, hcb]
        try rfl)) }
  have hfreeT : ∀ g : ↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ), g ≠ 1 →
      ∀ x : {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H}, g • x ≠ x := by
    intro g hg x hx
    have hxG : (g.1 : G) * (g.2 : G) * (x.1 : G) * (g.2 : G)⁻¹ * (g.1 : G)⁻¹ = (x.1 : G) := by
      have h := congrArg (fun y : {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H} =>
        ((y.1 : ↥Q) : G)) hx
      change (((act g x).1 : ↥Q) : G) = (((x.1 : ↥Q) : G)) at h
      rw [hact] at h
      exact h
    have hz1 : (g.2 : G) * (x.1 : G) * (g.2 : G)⁻¹ = (g.1 : G)⁻¹ * (x.1 : G) * (g.1 : G) := by
      have h := congrArg (fun y => (g.1 : G)⁻¹ * y * (g.1 : G)) hxG
      rw [← h]; group
    have hsq : (g.2 : G) * ((x.1 : G) * (x.1 : G)) * (g.2 : G)⁻¹ =
        (g.1 : G)⁻¹ * ((x.1 : G) * (x.1 : G)) * (g.1 : G) := by
      have h := congrArg (fun y : G => y * y) hz1
      rw [show (g.2 : G) * ((x.1 : G) * (x.1 : G)) * (g.2 : G)⁻¹ =
          ((g.2 : G) * (x.1 : G) * (g.2 : G)⁻¹) * ((g.2 : G) * (x.1 : G) * (g.2 : G)⁻¹)
          from by group,
        show (g.1 : G)⁻¹ * ((x.1 : G) * (x.1 : G)) * (g.1 : G) =
          ((g.1 : G)⁻¹ * (x.1 : G) * (g.1 : G)) * ((g.1 : G)⁻¹ * (x.1 : G) * (g.1 : G))
          from by group]
      exact h
    have hzsq : (g.2 : G) * ((x.1 : G) * (x.1 : G)) * (g.2 : G)⁻¹ = (x.1 : G) * (x.1 : G) := by
      have h2 : (g.2 : G) * ((x.1 : G) * (x.1 : G)) = ((x.1 : G) * (x.1 : G)) * (g.2 : G) :=
        hzpZ0 _ g.2.2 _ (hsq0 x.1)
      rw [h2]; group
    rw [hzsq] at hsq
    by_cases hgk : (g.1 : G) = 1
    · have hz1' : (g.2 : G) * (x.1 : G) * (g.2 : G)⁻¹ = (x.1 : G) := by
        rw [hgk] at hz1; simpa using hz1
      by_cases hgz : (g.2 : G) = 1
      · exact hg (Prod.ext (Subtype.ext hgk) (Subtype.ext hgz))
      · have hcomm : (g.2 : G) * (x.1 : G) = (x.1 : G) * (g.2 : G) := by
          have h2 := congrArg (fun y => y * (g.2 : G)) hz1'
          simpa [mul_assoc] using h2
        exact x.2 (hW (g.2 : G) (hZpW g.2.2) hgz (x.1 : G) x.1.2 hcomm)
    · have hkK : (g.1 : G) ∈ Work.ThmF.Kset H t := by rw [← hKset]; exact g.1.2
      have hcomm : ((x.1 : G) * (x.1 : G)) * (g.1 : G) = (g.1 : G) * ((x.1 : G) * (x.1 : G)) := by
        have h2 := congrArg (fun y => (g.1 : G) * y) hsq
        simpa [mul_assoc] using h2.symm
      have hone : (x.1 : G) * (x.1 : G) = 1 :=
        Work.ThmF.ChV12.prop1a hS.situation hC4 H Q t hS.split (g.1 : G) hkK hgk
          ((x.1 : G) * (x.1 : G)) (Q.mul_mem x.1.2 x.1.2) hcomm
      exact x.2 ((hZ x.1).mpr (show x.1 * x.1 = 1 from Subtype.ext hone))
  have hdvd := card_dvd_card_of_free
    (Γ := ↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ))
    (X := {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H}) hfreeT
  -- cardinalities
  have hXcard : Nat.card {x : ↥Q // (x : G) ∉ Work.ThmF.Q0sub H}
      = Nat.card ↥Q - Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun x : ↥Q => (x : G) ∈ Work.ThmF.Q0sub H)]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    congr 1
    exact Fintype.card_congr (Subgroup.subgroupOfEquivOfLe hZ0leQ).toEquiv
  have hGcard : Nat.card (↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ))
      = Nat.card ↥(Work.ThmF.Ksub H t) * Nat.card ↥(Subgroup.zpowers ζ) := Nat.card_prod _ _
  rw [hGcard, hKcardsub, Nat.card_zpowers] at hdvd
  rw [hXcard, hcard] at hdvd
  -- now: `(|Q₀| - 1) * orderOf ζ ∣ |Q₀|^3 - |Q₀|`
  obtain ⟨n, hn2, hnq⟩ := caseC_Q0sub_card hS hC4 hWne
  have hq4 : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [hnq]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hid : Nat.card ↥(Work.ThmF.Q0sub H) ^ 3 - Nat.card ↥(Work.ThmF.Q0sub H) =
      Nat.card ↥(Work.ThmF.Q0sub H) * (Nat.card ↥(Work.ThmF.Q0sub H) - 1) *
        (Nat.card ↥(Work.ThmF.Q0sub H) + 1) := by
    have h1 : 1 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by omega
    have hle : Nat.card ↥(Work.ThmF.Q0sub H) ≤ Nat.card ↥(Work.ThmF.Q0sub H) ^ 3 := by
      calc Nat.card ↥(Work.ThmF.Q0sub H)
          = Nat.card ↥(Work.ThmF.Q0sub H) * 1 := by rw [mul_one]
        _ ≤ Nat.card ↥(Work.ThmF.Q0sub H) *
            (Nat.card ↥(Work.ThmF.Q0sub H) * Nat.card ↥(Work.ThmF.Q0sub H)) := by
            exact Nat.mul_le_mul_left _ (by simpa using Nat.mul_le_mul h1 h1)
        _ = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3 := by ring
    have hcast : ((Nat.card ↥(Work.ThmF.Q0sub H) ^ 3 -
          Nat.card ↥(Work.ThmF.Q0sub H) : ℕ) : ℤ) =
        ((Nat.card ↥(Work.ThmF.Q0sub H) *
          (Nat.card ↥(Work.ThmF.Q0sub H) - 1) *
          (Nat.card ↥(Work.ThmF.Q0sub H) + 1) : ℕ) : ℤ) := by
      rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_add,
        Nat.cast_one, Nat.cast_pow]
      ring
    exact_mod_cast hcast
  have hmul : orderOf ζ ∣ Nat.card ↥(Work.ThmF.Q0sub H) *
      (Nat.card ↥(Work.ThmF.Q0sub H) + 1) := by
    have h3 : (Nat.card ↥(Work.ThmF.Q0sub H) - 1) * orderOf ζ ∣
        Nat.card ↥(Work.ThmF.Q0sub H) * (Nat.card ↥(Work.ThmF.Q0sub H) - 1) *
          (Nat.card ↥(Work.ThmF.Q0sub H) + 1) := by rwa [← hid]
    have h4 : (Nat.card ↥(Work.ThmF.Q0sub H) - 1) * orderOf ζ ∣
        (Nat.card ↥(Work.ThmF.Q0sub H) - 1) *
          (Nat.card ↥(Work.ThmF.Q0sub H) * (Nat.card ↥(Work.ThmF.Q0sub H) + 1)) := by
      rwa [show Nat.card ↥(Work.ThmF.Q0sub H) * (Nat.card ↥(Work.ThmF.Q0sub H) - 1) *
            (Nat.card ↥(Work.ThmF.Q0sub H) + 1) =
          (Nat.card ↥(Work.ThmF.Q0sub H) - 1) *
            (Nat.card ↥(Work.ThmF.Q0sub H) * (Nat.card ↥(Work.ThmF.Q0sub H) + 1))
          from by ring] at h3
    exact Nat.dvd_of_mul_dvd_mul_left (by omega : (0:ℕ) < Nat.card ↥(Work.ThmF.Q0sub H) - 1) h4
  have hcop : (orderOf ζ).Coprime (Nat.card ↥(Work.ThmF.Q0sub H)) := by
    rw [hnq]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hζodd)
  exact hcop.dvd_of_dvd_mul_left hmul

end Work.PSU3.StageA
