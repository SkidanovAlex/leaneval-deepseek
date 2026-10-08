/-
# `Work.PSU3.StageB.StepB.shifted_pos_eq_mem` — §2 (20), shifted position, `hcan` only at `ω · zc α`

This is Peterfalvi II Ch. VII §2, Case 2 of the proof of the Proposition of p. 274
("the shifted position `r + α` is a self-position") in the form used by
`StepB.square_eq_shift_of_good_cover`: the original statement
`Omega.shifted_pos_eq` carries the *global* hypothesis

  `hKW : ∀ x : ↥Q, (x : G) ∉ fr.Q0 → ((hcan hS.split x : twoPoint H t) : G) ∈ fr.KW`,

and its proof consumes that hypothesis at *exactly one* element, namely `x = ω · zcQF fr α`
(where the `KW`-conjugator `hh` of the H5-identity is produced).  Here that single instance
is taken as a hypothesis.

The proof is the one of `Omega.shifted_pos_eq`, verbatim apart from the construction of `hh`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Omega.square_eq_shift_of_good_cover_hKW

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

namespace Work.PSU3.StageB.StepB

open Work.PSU3.StageB.Omega
open Work.PSU3.StageB
open Work.ThmF
open Work.PSU3

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

lemma shifted_pos_eq_mem {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    {r x₂ : ↥(Work.PSU3.StageB.FX n)} (hsq : ω * ω = Work.PSU3.StageB.zcQF fr r)
    (hval : Work.PSU3.StageB.fval x₂ = Work.PSU3.StageB.fval r + Work.PSU3.StageB.fval α)
    (hmem : Multiplicative.toAdd
      (fr.bar (Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.zcQF fr x₂)))
      ∈ Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar ω)))
    (hα : ((Work.PSU3.StageB.hcan hS.split (ω * Work.PSU3.StageB.zcQF fr α) :
      ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) :
    r = α := by
  have hω1 : (ω : G) ≠ 1 := fun h => hω (by rw [h]; exact Q0_one_mem fr)
  have hzrQ0 : (zcQF fr r : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem _ r.2
  have hzαQ0 : (zcQF fr α : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem _ α.2
  have hwinv : (ω⁻¹ : ↥Q) = ω * zcQF fr r := by
    apply Subtype.ext
    simp only [Subgroup.coe_inv, Subgroup.coe_mul]
    exact inv_eq_mul_zcQF_of_sq fr hsq
  have hzr_inv : (ω * zcQF fr r)⁻¹ = ω := by
    rw [inv_mul_Q0' fr hzrQ0, hwinv]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, zcQF_coe]
    rw [show ↑ω * fr.zc (fval r) * fr.zc (fval r)
        = ↑ω * (fr.zc (fval r) * fr.zc (fval r)) from by group, zc_self fr r, mul_one]
  have hzx₂ : (zcQF fr r * zcQF fr α : ↥Q) = zcQF fr x₂ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, zcQF_coe]
    rw [hval]
    exact (fr.zc_add (fval r) (fval α) r.2 α.2).symm
  have hzq2 : ∀ (hv : σE (fval x₂ + fval α) = fval x₂ + fval α),
      (zcQ fr (fval x₂ + fval α) hv : ↥Q) = zcQF fr r := by
    intro hv
    apply Subtype.ext
    rw [zcQ_coe, zcQF_coe, hval, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  obtain ⟨d, hd⟩ := good_shift_of_mem_selfSet hS fr hω hωf (x := x₂) hmem
  have hd2 : fcan hS.split (ω * zcQF fr x₂) = kact hS fr d (ω * zcQF fr r) := by
    rw [hd, kact_eq_qconj']
    exact congrArg (fun z : ↥Q => qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ (ω * z)) (hzq2 _)
  have hx5inv : ((ω * zcQF fr α : ↥Q))⁻¹ = ω * zcQF fr x₂ := by
    rw [inv_mul_Q0' fr hzαQ0, hwinv, mul_assoc, hzx₂]
  have hwzα1 : ((ω * zcQF fr α : ↥Q) : G) ≠ 1 := mul_Q0_ne_one fr hω hzαQ0
  have hwzr1 : ((ω * zcQF fr r : ↥Q) : G) ≠ 1 := mul_Q0_ne_one fr hω hzrQ0
  have hfω : fcan hS.split ω = kact hS fr (fr.ζ : fr.KW) (ω * zcQF fr α) := by
    rw [hωf, kact_eq_qconj']
    congr 1
  have hA : fcan hS.split ((ω * zcQF fr α)⁻¹) = kact hS fr d (ω * zcQF fr r) := by
    rw [hx5inv]; exact hd2
  have hA1 : (fcan hS.split ((ω * zcQF fr α)⁻¹))⁻¹ = kact hS fr d ω := by
    rw [hA, kact_inv, hzr_inv]
  have hB : fcan hS.split ((fcan hS.split ((ω * zcQF fr α)⁻¹))⁻¹) =
      kact hS fr (fr.ζ * tconjKW hS fr d) (ω * zcQF fr α) := by
    rw [hA1, fcan_kact hS fr hω1, hfω, kact_mul]
  have hB1 : (fcan hS.split ((fcan hS.split ((ω * zcQF fr α)⁻¹))⁻¹))⁻¹ =
      kact hS fr (fr.ζ * tconjKW hS fr d) (ω * zcQF fr x₂) := by
    rw [hB, kact_inv, hx5inv]
  have hzx₂Q0 : (zcQF fr x₂ : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem _ x₂.2
  have hwz₂1 : ((ω * zcQF fr x₂ : ↥Q) : G) ≠ 1 := mul_Q0_ne_one fr hω hzx₂Q0
  have hC : fcan hS.split ((fcan hS.split ((fcan hS.split ((ω * zcQF fr α)⁻¹))⁻¹))⁻¹) =
      kact hS fr (d * tconjKW hS fr (fr.ζ * tconjKW hS fr d)) (ω * zcQF fr r) := by
    rw [hB1, fcan_kact hS fr hwz₂1, hd2, kact_mul]
  set hh : fr.KW := ⟨(hcan hS.split (ω * zcQF fr α) : ↥(twoPoint H t)), hα⟩ with hhh
  have hH5 : fcan hS.split ((fcan hS.split ((fcan hS.split ((ω * zcQF fr α)⁻¹))⁻¹))⁻¹) =
      kact hS fr hh⁻¹ (ω * zcQF fr α) := by
    apply Subtype.ext
    rw [fcan_jjj hS.split hwzα1]
    simp only [kact_coe, hhh, Subgroup.coe_inv, inv_inv]
  have hcomp : kact hS fr (d * tconjKW hS fr (fr.ζ * tconjKW hS fr d)) (ω * zcQF fr r) =
      kact hS fr hh⁻¹ (ω * zcQF fr α) := by rw [← hC, hH5]
  have hbw₁ : Multiplicative.toAdd (fr.bar (ω * zcQF fr r)) = Multiplicative.toAdd (fr.bar ω) := by
    rw [map_mul, bar_eq_one_of_mem_Q0 fr hzrQ0, mul_one]
  have hbw₂ : Multiplicative.toAdd (fr.bar (ω * zcQF fr α)) = Multiplicative.toAdd (fr.bar ω) := by
    rw [map_mul, bar_eq_one_of_mem_Q0 fr hzαQ0, mul_one]
  have hbar : (fr.κ (d * tconjKW hS fr (fr.ζ * tconjKW hS fr d)) : E n) =
      (fr.κ hh⁻¹ : E n) := by
    have h := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) hcomp
    rw [kact_bar, kact_bar, hbw₁, hbw₂] at h
    exact mul_right_cancel₀ (toAdd_bar_ne_zero fr hω) h
  have hb : d * tconjKW hS fr (fr.ζ * tconjKW hS fr d) = hh⁻¹ :=
    fr.κ_injective (Units.ext hbar)
  have hzr_eq : zcQF fr r = zcQF fr α := by
    have h := hcomp
    rw [hb] at h
    have h2 : ω * zcQF fr r = ω * zcQF fr α := by
      have h3 := congrArg (kact hS fr (hh⁻¹)⁻¹) h
      simpa [kact_mul, kact_one] using h3
    exact mul_left_cancel h2
  have hsum : fval r = fval α := by
    have h := congrArg (fun z : ↥Q => (z : G)) hzr_eq
    simp only [zcQF_coe] at h
    exact fr.zc_inj (fval r) (fval α) r.2 α.2 h
  exact fval_inj hsum

end Work.PSU3.StageB.StepB
