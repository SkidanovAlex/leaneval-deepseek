/-
# `Work.PSU3.StageB.Omega.beta_pow_m_eq_one` — Peterfalvi II Ch. VII §2 (15)/(16)

The central recursion of §2 (11)–(17): starting from `ω ∈ Q ∖ Q₀` with
`f(ω) = (ω·zc α)^ζ` and a root `β` of `X² + αX + 1` (`β + β⁻¹ = fval α`), the sequences
`u_i = S_{i-1}/S_i` (`S_i = β^i + β^{-i}`) and `d_i = ζ^i (S_i/α)^{2τ}` satisfy
`f(ω·zc u_i) = (ω·Y_i)^{d_i}` for a `Q₀`-element `Y_i` (`induction_rel`).
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.beta_pow_setup
import Submission.Work.PSU3.StageB.Omega.fcan_step10_gen
import Submission.Work.PSU3.StageB.Omega.fcan_eq_qconj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

lemma zU_mem_Q0 (fr : CoarseFrame H Q t n) (β : E n) (hβ : β ≠ 0)
    (hσ : σE β = β ∨ σE β = β⁻¹) (i : ℕ) : ((zU fr β hβ hσ i : ↥Q) : G) ∈ fr.Q0 := by
  rw [zU_coe]; exact fr.zc_mem (uSeq β i) (uSeq_fixed β hβ hσ i)

/-- `ζ` commutes with every element of `Q₀`. -/
lemma zeta_comm_Q0 (fr : CoarseFrame H Q t n) {Y : G} (hY : Y ∈ fr.Q0) :
    (fr.ζ : G) * Y = Y * (fr.ζ : G) := by
  obtain ⟨y, hy, hyz⟩ := fr.zc_surj Y hY
  rw [← hyz]
  have h := fr.act_zc_ζ y hy
  have h2 : (fr.ζ : G) * ((fr.ζ : G)⁻¹ * fr.zc y * (fr.ζ : G)) = (fr.ζ : G) * fr.zc y :=
    congrArg (fun z => (fr.ζ : G) * z) h
  rw [← h2]
  group

/-- **The recursion of §2 (11)–(17).** -/
theorem induction_rel (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    (hωf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    {β : E n} (hβ : β ≠ 0) (hσ : σE β = β ∨ σE β = β⁻¹) (hβα : β + β⁻¹ = fval α)
    (lam : ℕ → ↥(FX n)) {N : ℕ}
    (hlam : ∀ i, 1 ≤ i → i ≤ N → fval (lam i) = wSeq (fval α) β i)
    (hN : ∀ i, 1 ≤ i → i ≤ N → bS β i ≠ 0) :
    ∀ i, 1 ≤ i → i ≤ N → ∃ Y : ↥Q, (Y : G) ∈ fr.Q0 ∧
      fcan hS.split (ω * zU fr β hβ hσ i) =
        qconj hS.split ⟨dSeq hS fr lam i, fr.KW_le (dSeq hS fr lam i).2⟩ (ω * Y) := by
  have hα0 : fval α ≠ 0 := Units.ne_zero α.1
  have hα : σE (fval α) = fval α := α.2
  -- base case `i = 1`
  have base : (1 ≤ N) → ∃ Y : ↥Q, (Y : G) ∈ fr.Q0 ∧
      fcan hS.split (ω * zU fr β hβ hσ 1) =
        qconj hS.split ⟨dSeq hS fr lam 1, fr.KW_le (dSeq hS fr lam 1).2⟩ (ω * Y) := by
    intro h1N
    refine ⟨zcQF fr α, ?_, ?_⟩
    · rw [zcQF_coe]; exact fr.zc_mem (fval α) hα
    · have hzU1 : zU fr β hβ hσ 1 = 1 := by
        apply Subtype.ext
        simp [zU_coe, uSeq_one, zc_zero]
      have hd1 : dSeq hS fr lam 1 = fr.ζ := by
        refine dSeq_one hS fr lam ?_
        rw [hlam 1 le_rfl h1N, wSeq_one hβα hα0]
      rw [hzU1, mul_one, hd1]
      exact hωf
  -- induction step
  have step : ∀ m, 1 ≤ m →
      ((m ≤ N) → ∃ Y : ↥Q, (Y : G) ∈ fr.Q0 ∧
        fcan hS.split (ω * zU fr β hβ hσ m) =
          qconj hS.split ⟨dSeq hS fr lam m, fr.KW_le (dSeq hS fr lam m).2⟩ (ω * Y)) →
      ((m + 1 ≤ N) → ∃ Y : ↥Q, (Y : G) ∈ fr.Q0 ∧
        fcan hS.split (ω * zU fr β hβ hσ (m + 1)) =
          qconj hS.split ⟨dSeq hS fr lam (m + 1), fr.KW_le (dSeq hS fr lam (m + 1)).2⟩
            (ω * Y)) := by
    intro m hm ih hm1N
    have hmN : m ≤ N := by omega
    obtain ⟨Y, hY, hrel⟩ := ih hmN
    have hbm : bS β m ≠ 0 := hN m hm hmN
    have hbm1 : bS β (m + 1) ≠ 0 := hN (m + 1) (by omega) hm1N
    -- the FX-element `u_{m+1}`
    set U : ↥(FX n) := mkFX (uSeq β (m + 1)) (uSeq_fixed β hβ hσ (m + 1))
      (uSeq_ne_zero β hβ m hbm hbm1) with hUdef
    have hU : fval U = uSeq β (m + 1) := rfl
    -- the side conditions of §2 (10)
    have h1 : ((ω * zcQF fr U : ↥Q) : G) ≠ 1 := by
      intro hc
      have hmem : (zcQF fr U : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem (fval U) U.2
      have h2 : (ω : G) = ((ω * zcQF fr U : ↥Q) : G) * (zcQF fr U : G)⁻¹ := by
        rw [Subgroup.coe_mul]; group
      exact hω (by rw [h2, hc, one_mul]; exact fr.Q0.inv_mem hmem)
    have huv : uSeq β m = fval α + (fval U)⁻¹ := by
      rw [hU]
      exact (uSeq_rec_alpha (fval α) β hβα hβ hm hbm hbm1).symm
    have hgen := fcan_step10_gen hS fr hω hωf (uSeq_fixed β hβ hσ m) huv h1
    -- the new `Q₀`-element
    set η : E n := (fval (lam m))⁻¹ * fval U with hηdef
    have hηfix : σE η = η := by
      rw [hηdef, map_mul, map_inv₀, (lam m).2, U.2]
    set Y' : ↥Q := Y * zcQ fr η hηfix with hY'def
    have hY' : (Y' : G) ∈ fr.Q0 := by
      rw [hY'def, Subgroup.coe_mul]
      exact fr.Q0.mul_mem hY (by rw [zcQ_coe]; exact fr.zc_mem η hηfix)
    refine ⟨Y', hY', ?_⟩
    -- `zc η = d·zc u_{m+1}·d⁻¹`
    have hdU : (zcQ fr η hηfix : G)
        = ((dSeq hS fr lam m : fr.KW) : G) * (zcQF fr U : G)
            * ((dSeq hS fr lam m : fr.KW) : G)⁻¹ := by
      have h := dSeq_act hS fr lam m η hηfix
      have h2 : fval (lam m) * η = fval U := by
        rw [hηdef, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero (lam m).1), one_mul]
      rw [h2] at h
      rw [zcQ_coe, zcQF_coe]
      rw [← h]
      group
    -- the §2 (14) recursion for `λ`
    have hrec_lam : fval (lam (m + 1)) = fval (lam m) * (fval U)⁻¹ * (fval U)⁻¹ := by
      rw [hlam m hm hmN, hlam (m + 1) (by omega) hm1N, hU]
      exact wSeq_rec (fval α) β hβ hα0 m hbm
    have hd' : dSeq hS fr lam (m + 1) = dSeq hS fr lam m * zetaExp hS fr U :=
      dSeq_succ hS fr lam U m hrec_lam
    -- assemble
    have hL : ω * zU fr β hβ hσ (m + 1) = ω * zcQF fr U := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, zU_coe, zcQF_coe, hU]
    have hmid : (fcan hS.split (ω * zcQ fr (uSeq β m) (uSeq_fixed β hβ hσ m)) : G)
        = ((dSeq hS fr lam m : fr.KW) : G)⁻¹ * ((ω * Y : ↥Q) : G)
            * ((dSeq hS fr lam m : fr.KW) : G) := by
      have h' := congrArg (fun z : ↥Q => (z : G)) hrel
      rw [qconj_coe] at h'
      rw [show ω * zU fr β hβ hσ m = ω * zcQ fr (uSeq β m) (uSeq_fixed β hβ hσ m) from
        rfl] at h'
      exact h'
    have hdG : ((dSeq hS fr lam (m + 1) : fr.KW) : G)
        = ((dSeq hS fr lam m : fr.KW) : G) * ((zetaExp hS fr U : fr.KW) : G) := by
      rw [hd', Subgroup.coe_mul]
    have hY'G : (Y' : G) = (Y : G) * (zcQ fr η hηfix : G) := by
      rw [hY'def, Subgroup.coe_mul]
    have hZcU : (zcQF fr U : G)
        = ((dSeq hS fr lam m : fr.KW) : G)⁻¹ * (zcQ fr η hηfix : G)
            * ((dSeq hS fr lam m : fr.KW) : G) := by
      rw [hdU]; group
    have hW : ((ω * Y' : ↥Q) : G) = ((ω * Y : ↥Q) : G) * (zcQ fr η hηfix : G) := by
      have h1 : (ω * Y' : ↥Q) = (ω * Y) * zcQ fr η hηfix := by rw [hY'def]; group
      rw [h1, Subgroup.coe_mul]
    have hmul : ((fcan hS.split (ω * zcQ fr (uSeq β m) (uSeq_fixed β hβ hσ m))
          * zcQF fr U : ↥Q) : G)
        = (fcan hS.split (ω * zcQ fr (uSeq β m) (uSeq_fixed β hβ hσ m)) : G)
            * (zcQF fr U : G) := by
      rw [Subgroup.coe_mul]
    rw [hL]
    apply Subtype.ext
    rw [qconj_coe, hgen]
    rw [hmul, hmid, hdG, hZcU, hW]
    group
  have aux : ∀ k, 1 + k ≤ N → ∃ Y : ↥Q, (Y : G) ∈ fr.Q0 ∧
      fcan hS.split (ω * zU fr β hβ hσ (1 + k)) =
        qconj hS.split ⟨dSeq hS fr lam (1 + k), fr.KW_le (dSeq hS fr lam (1 + k)).2⟩
          (ω * Y) := by
    intro k
    induction k with
    | zero => intro _; simpa using base (by omega : 1 ≤ N)
    | succ k ih =>
        intro hk
        have hprev : 1 + k ≤ N := by omega
        have hstep := step (1 + k) (by omega) (fun _ => ih hprev) (by omega)
        simpa only [Nat.add_assoc] using hstep
  intro i hi hiN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  exact aux k hiN

theorem beta_pow_m_eq_one {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    {β : Work.PSU3.E n} (hβ : β ≠ 0) (hβα : β + β⁻¹ = Work.PSU3.StageB.fval α) :
    β ^ orderOf fr.ζ = 1 := by
  have hα0 : fval α ≠ 0 := Units.ne_zero α.1
  have hα : σE (fval α) = fval α := α.2
  have hσ : σE β = β ∨ σE β = β⁻¹ := beta_sigma_dichotomy hβ hβα hα0 hα
  have hβ1 : β ≠ 1 := by
    intro h1
    rw [h1, inv_one] at hβα
    rw [CharTwo.add_self_eq_zero] at hβα
    exact hα0 hβα.symm
  set m := orderOf fr.ζ with hm
  have hmpos : 1 ≤ m := by
    rw [hm]
    exact Nat.one_le_iff_ne_zero.mpr (orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite fr.ζ))
  set lam : ℕ → ↥(FX n) := lamSeq (fval α) β hα hσ with hlamdef
  -- (I) the recursion cannot reach `i = m`
  have hex : ∃ i, 1 ≤ i ∧ i ≤ m ∧ β ^ i = 1 := by
    by_contra hcon
    have hcon' : ∀ i, 1 ≤ i → i ≤ m → β ^ i ≠ 1 :=
      fun i hi hile hbi => hcon ⟨i, hi, hile, hbi⟩
    have hN : ∀ i, 1 ≤ i → i ≤ m → bS β i ≠ 0 := fun i hi hile =>
      (bS_ne_zero_iff β hβ i).mpr (hcon' i hi hile)
    have hlam : ∀ i, 1 ≤ i → i ≤ m → fval (lam i) = wSeq (fval α) β i := fun i hi hile =>
      fval_lamSeq (fval α) β hα hσ (wSeq_ne_zero (fval α) β hα0 i (hN i hi hile))
    obtain ⟨Y, hY, hrel⟩ :=
      induction_rel hS fr hω hωf hβ hσ hβα lam hlam hN m hmpos le_rfl
    have hdK : (((dSeq hS fr lam m : fr.KW)) : G) ∈ Ksub H t := by
      have hzm : fr.ζ ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one fr.ζ
      rw [dSeq, hzm, one_mul]
      exact kElF_mem_Ksub fr _
    have hx0 : ((ω * zU fr β hβ hσ m : ↥Q) : G) ∉ fr.Q0 := by
      intro hx
      have hzmem : ((zU fr β hβ hσ m : ↥Q) : G) ∈ fr.Q0 := zU_mem_Q0 fr β hβ hσ m
      have h2 : (ω : G) = ((ω * zU fr β hβ hσ m : ↥Q) : G)
          * ((zU fr β hβ hσ m : ↥Q) : G)⁻¹ := by
        rw [Subgroup.coe_mul]; group
      exact hω (by rw [h2]; exact fr.Q0.mul_mem hx (fr.Q0.inv_mem hzmem))
    have hy0 : ((((zU fr β hβ hσ m)⁻¹) * Y : ↥Q) : G) ∈ fr.Q0 := by
      rw [Subgroup.coe_mul]
      exact fr.Q0.mul_mem (fr.Q0.inv_mem (zU_mem_Q0 fr β hβ hσ m)) hY
    have hrel' : fcan hS.split (ω * zU fr β hβ hσ m) =
        qconj hS.split ⟨dSeq hS fr lam m, fr.KW_le (dSeq hS fr lam m).2⟩
          ((ω * zU fr β hβ hσ m) * ((zU fr β hβ hσ m)⁻¹ * Y)) := by
      rw [hrel, show (ω * zU fr β hβ hσ m) * ((zU fr β hβ hσ m)⁻¹ * Y) = ω * Y from by
        group]
    obtain ⟨-, hdKnot⟩ := fcan_eq_qconj hS fr hx0 hy0 hrel'
    exact hdKnot hdK
  -- (II) the recursion at the stopping index
  set j₀ := Nat.find hex with hj0def
  have hj1 : 1 ≤ j₀ := by rw [hj0def]; exact (Nat.find_spec hex).1
  have hjm : j₀ ≤ m := by rw [hj0def]; exact (Nat.find_spec hex).2.1
  have hbj : β ^ j₀ = 1 := by rw [hj0def]; exact (Nat.find_spec hex).2.2
  have hj2 : 2 ≤ j₀ := by
    by_contra h
    have h1 : j₀ = 1 := by omega
    rw [h1, pow_one] at hbj
    exact hβ1 hbj
  have hmin : ∀ i < j₀, ¬(1 ≤ i ∧ i ≤ m ∧ β ^ i = 1) := by
    intro i hi
    rw [hj0def] at hi
    exact Nat.find_min hex hi
  have hN' : ∀ i, 1 ≤ i → i ≤ j₀ - 1 → bS β i ≠ 0 := by
    intro i hi hile
    rw [bS_ne_zero_iff β hβ i]
    intro hbi
    exact (hmin i (by omega)) ⟨hi, by omega, hbi⟩
  have hlam' : ∀ i, 1 ≤ i → i ≤ j₀ - 1 → fval (lam i) = wSeq (fval α) β i := fun i hi hile =>
    fval_lamSeq (fval α) β hα hσ (wSeq_ne_zero (fval α) β hα0 i (hN' i hi hile))
  obtain ⟨Y, hY, hrel⟩ :=
    induction_rel hS fr hω hωf hβ hσ hβα lam hlam' hN' (j₀ - 1) (by omega) (by omega)
  have huN : uSeq β (j₀ - 1) = fval α := uSeq_ord_sub_one hβ hβα hα0 hj2 hbj
  have hlamNj : fval (lam (j₀ - 1)) = 1 := by
    rw [hlam' (j₀ - 1) (by omega) (by omega)]
    exact wSeq_ord_sub_one hβα hα0 hj2 hbj
  have hdN : dSeq hS fr lam (j₀ - 1) = fr.ζ ^ (j₀ - 1) := dSeq_stop hS fr lam hlamNj
  have hxN : (ω * zU fr β hβ hσ (j₀ - 1) : ↥Q) = ω * zcQF fr α := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, zU_coe, zcQF_coe, huN]
  -- the two expressions for `f(ω zc α)`
  have hfα : fcan hS.split (ω * zcQF fr α) =
      qconj hS.split ⟨(fr.ζ : G)⁻¹, (twoPoint H t).inv_mem (zeta_mem_D fr)⟩ ω := by
    have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
    have hfω1 : ((fcan hS.split ω : ↥Q) : G) ≠ 1 := fcan_ne_one hS.split hω1
    have hf : (fcan hS.split ω : G)
        = (fr.ζ : G)⁻¹ * ((ω * zcQF fr α : ↥Q) : G) * (fr.ζ : G) := by
      have hh := congrArg (fun z : ↥Q => (z : G)) hωf
      rw [qconj_coe] at hh
      simp only [zetaD, Subtype.coe_mk] at hh
      exact hh
    have heq : ω * zcQF fr α =
        qconj hS.split ⟨(fr.ζ : G)⁻¹, (twoPoint H t).inv_mem (zeta_mem_D fr)⟩
          (fcan hS.split ω) := by
      apply Subtype.ext
      rw [qconj_coe, Subtype.coe_mk, hf]
      group
    rw [heq]
    apply Subtype.ext
    simp only [qconj_coe]
    rw [fcan_qconj hS.split hfω1 ⟨(fr.ζ : G)⁻¹, (twoPoint H t).inv_mem (zeta_mem_D fr)⟩]
    simp only [t_zeta_inv_t hS.split fr, (fcan_fcan hS.split hω1).1]
  have hrelζ : qconj hS.split
        ⟨(fr.ζ : G) ^ (j₀ - 1), (twoPoint H t).pow_mem (zeta_mem_D fr) (j₀ - 1)⟩ (ω * Y)
      = qconj hS.split ⟨(fr.ζ : G)⁻¹, (twoPoint H t).inv_mem (zeta_mem_D fr)⟩ ω := by
    rw [← hfα, ← hxN, hrel,
      show (⟨dSeq hS fr lam (j₀ - 1), fr.KW_le (dSeq hS fr lam (j₀ - 1)).2⟩ : ↥(twoPoint H t))
        = ⟨(fr.ζ : G) ^ (j₀ - 1), (twoPoint H t).pow_mem (zeta_mem_D fr) (j₀ - 1)⟩ from by
          apply Subtype.ext
          rw [hdN, Subgroup.coe_pow]]
  have hqeq : kact hS fr (fr.ζ ^ (j₀ - 1)) (ω * Y) = kact hS fr (fr.ζ⁻¹) ω := by
    have heqG := congrArg (fun z : ↥Q => (z : G)) hrelζ
    simp only [qconj_coe, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv] at heqG
    apply Subtype.ext
    simp only [kact_coe, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
    exact heqG
  have hbY : fr.bar (ω * Y) = fr.bar ω := by
    rw [map_mul, bar_eq_one_of_mem_Q0 fr hY, mul_one]
  have hbar : (fr.κ (fr.ζ ^ (j₀ - 1)) : E n) * Multiplicative.toAdd (fr.bar ω)
      = (fr.κ (fr.ζ⁻¹) : E n) * Multiplicative.toAdd (fr.bar ω) := by
    have h := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) hqeq
    rw [kact_bar, kact_bar, hbY] at h
    exact h
  have hb : Multiplicative.toAdd (fr.bar ω) ≠ 0 := by
    intro h0
    refine bar_ne_one_of_not_mem_Q0 fr hω ?_
    apply Multiplicative.toAdd.injective
    rw [h0]
    rfl
  have hκ : fr.κ (fr.ζ ^ (j₀ - 1)) = fr.κ (fr.ζ⁻¹) :=
    Units.ext (mul_right_cancel₀ hb hbar)
  have hζ : fr.ζ ^ (j₀ - 1) = fr.ζ⁻¹ := fr.κ_injective hκ
  have hζj : fr.ζ ^ j₀ = 1 := by
    rw [show j₀ = (j₀ - 1) + 1 from by omega, pow_succ, hζ, inv_mul_cancel]
  have hmj : m ∣ j₀ := by
    rw [hm]; exact orderOf_dvd_iff_pow_eq_one.mpr hζj
  have hj₀eq : j₀ = m := le_antisymm hjm (Nat.le_of_dvd (by omega) hmj)
  rw [← hj₀eq]; exact hbj

end Work.PSU3.StageB.Omega
