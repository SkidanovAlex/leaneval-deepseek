/-
# `Work.PSU3.StageB.Omega.orderOf_beta_eq` — Peterfalvi II Ch. VII §2 (15)/(16), sharp form

`beta_pow_m_eq_one` proves `β ^ orderOf fr.ζ = 1` for a root `β` of `X² + αX + 1`
(`β + β⁻¹ = fval α`, `β ≠ 0`).  The argument there in fact terminates with the stronger
information that the *least* index `j ≥ 1` with `β ^ j = 1` equals `orderOf fr.ζ`; this file
extracts that: `orderOf β = orderOf fr.ζ`.

The proof reuses the verified induction `induction_rel` of `beta_pow_m_eq_one` and runs the
"stopping" comparison at the exact index `j = orderOf β` (the existence of `j ≤ orderOf fr.ζ`
comes from `beta_pow_m_eq_one`), instead of at an `Nat.find`-minimum as in that file.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.beta_pow_m_eq_one
import Submission.Work.PSU3.StageB.Omega.beta_pow_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

theorem orderOf_beta_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    {β : Work.PSU3.E n} (hβ : β ≠ 0) (hβα : β + β⁻¹ = Work.PSU3.StageB.fval α) :
    orderOf β = orderOf fr.ζ := by
  have hα0 : fval α ≠ 0 := Units.ne_zero α.1
  have hα : σE (fval α) = fval α := α.2
  have hσ : σE β = β ∨ σE β = β⁻¹ := beta_sigma_dichotomy hβ hβα hα0 hα
  have hβ1 : β ≠ 1 := by
    intro h1
    rw [h1, inv_one] at hβα
    rw [CharTwo.add_self_eq_zero] at hβα
    exact hα0 hβα.symm
  -- `orderOf β` is the order of the unit `β`
  have hord : orderOf β = orderOf (Units.mk0 β hβ) := by
    conv_lhs => rw [← Units.val_mk0 hβ]
    exact orderOf_units
  have hv1 : (Units.mk0 β hβ : (E n)ˣ) ≠ 1 := by
    intro h
    apply hβ1
    have h' := congrArg (fun z : (E n)ˣ => (z : E n)) h
    simpa [Units.val_mk0 hβ] using h'
  -- `β ^ j = 1` for `j = orderOf β`
  have hbj : β ^ orderOf (Units.mk0 β hβ) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one β
  have hvj_pos : 1 ≤ orderOf (Units.mk0 β hβ) :=
    Nat.one_le_iff_ne_zero.mpr
      (orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite (Units.mk0 β hβ)))
  have hj2 : 2 ≤ orderOf (Units.mk0 β hβ) := by
    rcases Nat.lt_or_ge (orderOf (Units.mk0 β hβ)) 2 with h | h
    · exfalso
      have h1 : orderOf (Units.mk0 β hβ) = 1 := by omega
      exact hv1 (orderOf_eq_one_iff.mp h1)
    · exact h
  -- minimality of `orderOf β`: `S_i ≠ 0` for `1 ≤ i < orderOf β`
  have hmin : ∀ i, 1 ≤ i → i < orderOf (Units.mk0 β hβ) → bS β i ≠ 0 := by
    intro i hi hlt
    rw [bS_ne_zero_iff β hβ i]
    intro hbi
    have hdvd : orderOf (Units.mk0 β hβ) ∣ i := by
      apply orderOf_dvd_iff_pow_eq_one.mpr
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0 hβ, Units.val_one, hbi]
    exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  set lam : ℕ → ↥(FX n) := lamSeq (fval α) β hα hσ with hlamdef
  have hN : ∀ i, 1 ≤ i → i ≤ orderOf (Units.mk0 β hβ) - 1 → bS β i ≠ 0 :=
    fun i hi hile => hmin i hi (by omega)
  have hlam : ∀ i, 1 ≤ i → i ≤ orderOf (Units.mk0 β hβ) - 1 →
      fval (lam i) = wSeq (fval α) β i :=
    fun i hi hile => fval_lamSeq (fval α) β hα hσ
      (wSeq_ne_zero (fval α) β hα0 i (hN i hi hile))
  obtain ⟨Y, hY, hrel⟩ := induction_rel hS fr hω hωf hβ hσ hβα lam hlam hN
    (orderOf (Units.mk0 β hβ) - 1) (by omega) le_rfl
  have huN : uSeq β (orderOf (Units.mk0 β hβ) - 1) = fval α :=
    uSeq_ord_sub_one hβ hβα hα0 hj2 hbj
  have hlamNj : fval (lam (orderOf (Units.mk0 β hβ) - 1)) = 1 := by
    rw [hlam (orderOf (Units.mk0 β hβ) - 1) (by omega) le_rfl]
    exact wSeq_ord_sub_one hβα hα0 hj2 hbj
  have hdN : dSeq hS fr lam (orderOf (Units.mk0 β hβ) - 1) =
      fr.ζ ^ (orderOf (Units.mk0 β hβ) - 1) := dSeq_stop hS fr lam hlamNj
  have hxN : (ω * zU fr β hβ hσ (orderOf (Units.mk0 β hβ) - 1) : ↥Q) = ω * zcQF fr α := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, zU_coe, zcQF_coe, huN]
  -- the two expressions for `f (ω zc α)`
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
        ⟨(fr.ζ : G) ^ (orderOf (Units.mk0 β hβ) - 1),
          (twoPoint H t).pow_mem (zeta_mem_D fr) (orderOf (Units.mk0 β hβ) - 1)⟩ (ω * Y)
      = qconj hS.split ⟨(fr.ζ : G)⁻¹, (twoPoint H t).inv_mem (zeta_mem_D fr)⟩ ω := by
    rw [← hfα, ← hxN, hrel,
      show (⟨dSeq hS fr lam (orderOf (Units.mk0 β hβ) - 1),
          fr.KW_le (dSeq hS fr lam (orderOf (Units.mk0 β hβ) - 1)).2⟩ : ↥(twoPoint H t))
        = ⟨(fr.ζ : G) ^ (orderOf (Units.mk0 β hβ) - 1),
            (twoPoint H t).pow_mem (zeta_mem_D fr) (orderOf (Units.mk0 β hβ) - 1)⟩ from by
          apply Subtype.ext
          rw [hdN, Subgroup.coe_pow]]
  have hqeq : kact hS fr (fr.ζ ^ (orderOf (Units.mk0 β hβ) - 1)) (ω * Y) =
      kact hS fr (fr.ζ⁻¹) ω := by
    have heqG := congrArg (fun z : ↥Q => (z : G)) hrelζ
    simp only [qconj_coe, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv] at heqG
    apply Subtype.ext
    simp only [kact_coe, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
    exact heqG
  have hbY : fr.bar (ω * Y) = fr.bar ω := by
    rw [map_mul, bar_eq_one_of_mem_Q0 fr hY, mul_one]
  have hbar : (fr.κ (fr.ζ ^ (orderOf (Units.mk0 β hβ) - 1)) : E n) *
      Multiplicative.toAdd (fr.bar ω)
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
  have hκ : fr.κ (fr.ζ ^ (orderOf (Units.mk0 β hβ) - 1)) = fr.κ (fr.ζ⁻¹) :=
    Units.ext (mul_right_cancel₀ hb hbar)
  have hζ : fr.ζ ^ (orderOf (Units.mk0 β hβ) - 1) = fr.ζ⁻¹ := fr.κ_injective hκ
  have hζj : fr.ζ ^ orderOf (Units.mk0 β hβ) = 1 := by
    rw [show orderOf (Units.mk0 β hβ) = (orderOf (Units.mk0 β hβ) - 1) + 1 from by omega,
      pow_succ, hζ, inv_mul_cancel]
  -- both divisibilities
  have hbm : β ^ orderOf fr.ζ = 1 := beta_pow_m_eq_one hS fr hω hωf hβ hβα
  have hvm : (Units.mk0 β hβ) ^ orderOf fr.ζ = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0 hβ, Units.val_one, hbm]
  have hmpos : 1 ≤ orderOf fr.ζ :=
    Nat.one_le_iff_ne_zero.mpr (orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite fr.ζ))
  have hjle : orderOf (Units.mk0 β hβ) ≤ orderOf fr.ζ :=
    Nat.le_of_dvd hmpos (orderOf_dvd_iff_pow_eq_one.mpr hvm)
  have hmle : orderOf fr.ζ ≤ orderOf (Units.mk0 β hβ) :=
    Nat.le_of_dvd hvj_pos (orderOf_dvd_iff_pow_eq_one.mpr hζj)
  rw [hord, le_antisymm hjle hmle]

end Work.PSU3.StageB.Omega
