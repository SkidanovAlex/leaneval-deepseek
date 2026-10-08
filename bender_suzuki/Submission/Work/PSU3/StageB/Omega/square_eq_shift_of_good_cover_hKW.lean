import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.Omega.fcan_zU_eq_vSeq
import Submission.Work.PSU3.StageB.Omega.fcan_step10_gen
import Submission.Work.PSU3.StageB.Omega.cross_orbit_shift_proof
import Submission.Work.PSU3.StageB.Omega.cross_orbit_shift_aux
import Submission.Work.PSU3.StageB.Omega.KW_torsion_eq_zpowers
import Submission.Work.PSU3.StageB.Omega.alpha_eq_of_two_orbits
import Submission.Work.PSU3.StageB.Omega.count_self_eq
import Submission.Work.PSU3.StageB.Omega.exists_coset_zeta
import Submission.Work.PSU3.StageB.Omega.exists_beta
import Submission.Work.PSU3.StageB.Omega.omegaHyp_of_sq
import Submission.Work.PSU3.StageB.Omega.orbE_card
import Submission.Work.PSU3.StageB.Omega.good_shift_of_mem_selfSet
import Submission.Work.PSU3.FineCoords.card_KW_odd
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.ThetaOmega
import Submission.Work.PSU3.StageB.NotFpfAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Elementary consequences of `Q₀` being central in `Q` -/

lemma zcQF_mul_self' (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    (zcQF fr u : G) * (zcQF fr u : G) = 1 :=
  Q0_mul_self fr (fr.zc_mem (fval u) u.2)

lemma inv_mul_Q0' (fr : CoarseFrame H Q t n) {x z : ↥Q} (hz : (z : G) ∈ fr.Q0) :
    (x * z)⁻¹ = x⁻¹ * z := by
  apply Subtype.ext
  simp only [Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_rev]
  rw [inv_eq_of_mul_eq_one_right (Q0_mul_self fr hz)]
  exact fr.Q0_central z hz x⁻¹ (Q.inv_mem x.2)

lemma mul_Q0_ne_one (fr : CoarseFrame H Q t n) {x z : ↥Q}
    (hx : (x : G) ∉ fr.Q0) (hz : (z : G) ∈ fr.Q0) : ((x * z : ↥Q) : G) ≠ 1 := by
  intro h
  apply hx
  have h' : (x : G) = (z : G) := by
    have h2 : (x : G) = ((x * z : ↥Q) : G) * (z : G)⁻¹ := by rw [Subgroup.coe_mul]; group
    rw [h2, h, one_mul, inv_eq_of_mul_eq_one_right (Q0_mul_self fr hz)]
  rw [h']
  exact hz

/-- `kact` commutes with inversion. -/
lemma kact_inv (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) (x : ↥Q) :
    (kact hS fr d x)⁻¹ = kact hS fr d x⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_inv, kact_coe]
  group

/-- `t`-conjugation of a `KW`-element is again in `KW`. -/
lemma tconjKW_self (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) :
    tconjKW hS fr (tconjKW hS fr d) = d := by
  apply Subtype.ext
  rw [tconjKW_coe, tconjKW_coe]
  have ht : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hS.split
  calc t * (t * ↑d * t) * t = (t * t) * ↑d * (t * t) := by group
    _ = ↑d := by rw [ht, one_mul, mul_one]

/-- `fcan` of a `KW`-conjugate. -/
lemma fcan_kact (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {x : ↥Q}
    (hx : (x : G) ≠ 1) (d : fr.KW) :
    fcan hS.split (kact hS fr d x) = kact hS fr (tconjKW hS fr d) (fcan hS.split x) := by
  rw [kact_eq_qconj']
  apply Subtype.ext
  simp only [kact_coe, tconjKW_coe]
  exact fcan_qconj hS.split hx ⟨(d : G), fr.KW_le d.2⟩

/-! ## The crux: `x` at a self-position has the sharp shift (sibling module). -/

lemma zc_self (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    fr.zc (fval u) * fr.zc (fval u) = 1 :=
  Q0_mul_self fr (fr.zc_mem (fval u) u.2)

lemma zcQF_sq (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    zcQF fr u * zcQF fr u = (1 : ↥Q) :=
  Subtype.ext (zcQF_mul_self' fr u)

/-- The `bar`-coordinate is unaffected by a `Q₀`-factor. -/
lemma toAdd_bar_mul_Q0 (fr : CoarseFrame H Q t n) (x : ↥Q) {z : ↥Q} (hz : (z : G) ∈ fr.Q0) :
    Multiplicative.toAdd (fr.bar (x * z)) = Multiplicative.toAdd (fr.bar x) := by
  rw [map_mul fr.bar x z, bar_eq_one_of_mem_Q0 fr hz, mul_one]

/-! ## Case 1: `r` is a self-position. -/

lemma self_pos_eq (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    (hωf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    {r : ↥(FX n)} (hsq : ω * ω = zcQF fr r)
    (hmem : Multiplicative.toAdd (fr.bar (fcan hS.split (ω * zcQF fr r))) ∈
      orbE fr (Multiplicative.toAdd (fr.bar ω)))
    (hKW : ∀ x : ↥Q, (x : G) ∉ fr.Q0 →
      ((hcan hS.split x : ↥(twoPoint H t)) : G) ∈ fr.KW) :
    r = α := by
  have hω1 : (ω : G) ≠ 1 := fun h => hω (by rw [h]; exact Q0_one_mem fr)
  have hzrQ0 : (zcQF fr r : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem _ r.2
  have hzαQ0 : (zcQF fr α : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem _ α.2
  set pos : ↥Q := zcQF fr r * zcQF fr α with hposdef
  have hposcoe : (pos : G) = fr.zc (fval r + fval α) := by
    simp only [hposdef, Subgroup.coe_mul, zcQF_coe]
    exact (fr.zc_add (fval r) (fval α) r.2 α.2).symm
  have hposQ0 : (pos : G) ∈ fr.Q0 := by
    rw [hposcoe]; exact fr.zc_mem (fval r + fval α) (by rw [map_add, r.2, α.2])
  have hzq_all : ∀ (hv : σE (fval r + fval α) = fval r + fval α),
      (zcQ fr (fval r + fval α) hv : ↥Q) = pos := by
    intro hv
    apply Subtype.ext
    rw [zcQ_coe, hposcoe]
  have hwinv : (ω⁻¹ : ↥Q) = ω * zcQF fr r := by
    apply Subtype.ext
    simp only [Subgroup.coe_inv, Subgroup.coe_mul]
    exact inv_eq_mul_zcQF_of_sq fr hsq
  obtain ⟨d, hd⟩ := good_shift_of_mem_selfSet hS fr hω hωf (x := r) hmem
  have hd' : fcan hS.split (ω * zcQF fr r) = kact hS fr d (ω * pos) := by
    rw [hd, kact_eq_qconj']
    exact congrArg (fun z : ↥Q => qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ (ω * z)) (hzq_all _)
  have hinv_pos : (ω * pos)⁻¹ = ω * zcQF fr α := by
    rw [inv_mul_Q0' fr hposQ0, hwinv, hposdef]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, zcQF_coe]
    calc (↑ω * fr.zc (fval r)) * (fr.zc (fval r) * fr.zc (fval α))
        = (↑ω * (fr.zc (fval r) * fr.zc (fval r))) * fr.zc (fval α) := by group
      _ = (↑ω * 1) * fr.zc (fval α) := by rw [zc_self fr r]
      _ = ↑ω * fr.zc (fval α) := by rw [mul_one]
  have hwzα1 : ((ω * zcQF fr α : ↥Q) : G) ≠ 1 := mul_Q0_ne_one fr hω hzαQ0
  have hwzr1 : ((ω * zcQF fr r : ↥Q) : G) ≠ 1 := mul_Q0_ne_one fr hω hzrQ0
  have hA : fcan hS.split (ω⁻¹) = kact hS fr d (ω * pos) := by rw [hwinv]; exact hd'
  have hA1 : (fcan hS.split (ω⁻¹))⁻¹ = kact hS fr d (ω * zcQF fr α) := by
    rw [hA, kact_inv, hinv_pos]
  have hfα : fcan hS.split (ω * zcQF fr α) = kact hS fr (fr.ζ⁻¹ : fr.KW) ω := by
    have h := fcan_zcQF_alpha hS fr hω hωf
    rw [h, kact_eq_qconj']
    congr 1
  have hB : fcan hS.split ((fcan hS.split (ω⁻¹))⁻¹) =
      kact hS fr (fr.ζ⁻¹ * tconjKW hS fr d) ω := by
    rw [hA1, fcan_kact hS fr hwzα1, hfα, kact_mul]
  have hB1 : (fcan hS.split ((fcan hS.split (ω⁻¹))⁻¹))⁻¹ =
      kact hS fr (fr.ζ⁻¹ * tconjKW hS fr d) (ω * zcQF fr r) := by
    rw [hB, kact_inv, hwinv]
  have hC : fcan hS.split ((fcan hS.split ((fcan hS.split (ω⁻¹))⁻¹))⁻¹) =
      kact hS fr (d * tconjKW hS fr (fr.ζ⁻¹ * tconjKW hS fr d)) (ω * pos) := by
    rw [hB1, fcan_kact hS fr hwzr1, hd', kact_mul]
  set hh : fr.KW := ⟨(hcan hS.split ω : ↥(twoPoint H t)), hKW ω hω⟩ with hhh
  have hH5 : fcan hS.split ((fcan hS.split ((fcan hS.split (ω⁻¹))⁻¹))⁻¹) =
      kact hS fr hh⁻¹ ω := by
    apply Subtype.ext
    rw [fcan_jjj hS.split hω1]
    simp only [kact_coe, hhh, Subgroup.coe_inv, inv_inv]
  have hcomp : kact hS fr (d * tconjKW hS fr (fr.ζ⁻¹ * tconjKW hS fr d)) (ω * pos) =
      kact hS fr hh⁻¹ ω := by rw [← hC, hH5]
  have hbw : Multiplicative.toAdd (fr.bar (ω * pos)) = Multiplicative.toAdd (fr.bar ω) := by
    rw [map_mul, bar_eq_one_of_mem_Q0 fr hposQ0, mul_one]
  have hbar : (fr.κ (d * tconjKW hS fr (fr.ζ⁻¹ * tconjKW hS fr d)) : E n) =
      (fr.κ hh⁻¹ : E n) := by
    have h := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) hcomp
    rw [kact_bar, kact_bar, hbw] at h
    exact mul_right_cancel₀ (toAdd_bar_ne_zero fr hω) h
  have hb : d * tconjKW hS fr (fr.ζ⁻¹ * tconjKW hS fr d) = hh⁻¹ :=
    fr.κ_injective (Units.ext hbar)
  have hpos1 : pos = 1 := by
    have h := hcomp
    rw [hb] at h
    have h2 : ω * pos = ω := by
      have h3 := congrArg (kact hS fr (hh⁻¹)⁻¹) h
      simpa [kact_mul, kact_one] using h3
    exact mul_left_cancel (h2.trans (mul_one ω).symm)
  have hz : fr.zc (fval r + fval α) = 1 := by
    have h := congrArg (fun z : ↥Q => (z : G)) hpos1
    rw [hposcoe] at h
    simpa using h
  have hsum : fval r + fval α = 0 :=
    fr.zc_inj (fval r + fval α) 0 (by rw [map_add, r.2, α.2]) (map_zero σE)
      (by rw [hz, zc_zero fr])
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hsum
  exact fval_inj hsum

/-! ## Case 2: the shifted position `r + α` is a self-position. -/

lemma shifted_pos_eq (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    (hωf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    {r x₂ : ↥(FX n)} (hsq : ω * ω = zcQF fr r) (hval : fval x₂ = fval r + fval α)
    (hmem : Multiplicative.toAdd (fr.bar (fcan hS.split (ω * zcQF fr x₂))) ∈
      orbE fr (Multiplicative.toAdd (fr.bar ω)))
    (hKW : ∀ x : ↥Q, (x : G) ∉ fr.Q0 →
      ((hcan hS.split x : ↥(twoPoint H t)) : G) ∈ fr.KW) :
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
  have hx5Q0 : ((ω * zcQF fr α : ↥Q) : G) ∉ fr.Q0 := by
    intro hc
    have hbar : fr.bar (ω * zcQF fr α) = 1 := (fr.bar_eq_one_iff _).mpr hc
    rw [map_mul, bar_eq_one_of_mem_Q0 fr hzαQ0, mul_one] at hbar
    exact bar_ne_one_of_not_mem_Q0 fr hω hbar
  have hC : fcan hS.split ((fcan hS.split ((fcan hS.split ((ω * zcQF fr α)⁻¹))⁻¹))⁻¹) =
      kact hS fr (d * tconjKW hS fr (fr.ζ * tconjKW hS fr d)) (ω * zcQF fr r) := by
    rw [hB1, fcan_kact hS fr hwz₂1, hd2, kact_mul]
  set hh : fr.KW := ⟨(hcan hS.split (ω * zcQF fr α) : ↥(twoPoint H t)),
    hKW (ω * zcQF fr α) hx5Q0⟩ with hhh
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

/-- `qconj` depends only on the underlying group element of the `D`-element. -/
lemma qconj_congr_element (h : IsSplitRankOne H Q t) {a b : ↥(twoPoint H t)}
    (hab : (a : G) = (b : G)) (x : ↥Q) : qconj h a x = qconj h b x := by
  apply Subtype.ext
  rw [qconj_coe, qconj_coe, hab]

/-- `(x * (zr * zα))⁻¹ = x * zα` when `x⁻¹ = x * zr`. -/
lemma inv_mul_zr_zα (fr : CoarseFrame H Q t n) {x : ↥Q} {r α : ↥(FX n)}
    (hxr : (x : G)⁻¹ = (x : G) * (zcQF fr r : G)) :
    (x * (zcQF fr r * zcQF fr α))⁻¹ = x * zcQF fr α := by
  have hposQ0 : ((zcQF fr r * zcQF fr α : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul]
    exact fr.Q0.mul_mem (by rw [zcQF_coe]; exact fr.zc_mem _ r.2)
      (by rw [zcQF_coe]; exact fr.zc_mem _ α.2)
  have hxr' : (x⁻¹ : ↥Q) = x * zcQF fr r := by
    apply Subtype.ext
    rw [Subgroup.coe_inv, Subgroup.coe_mul]
    exact hxr
  rw [inv_mul_Q0' fr hposQ0, hxr']
  apply Subtype.ext
  simp only [Subgroup.coe_mul, zcQF_coe]
  calc (↑x * fr.zc (fval r)) * (fr.zc (fval r) * fr.zc (fval α))
      = (↑x * (fr.zc (fval r) * fr.zc (fval r))) * fr.zc (fval α) := by group
    _ = (↑x * 1) * fr.zc (fval α) := by rw [zc_self fr r]
    _ = ↑x * fr.zc (fval α) := by rw [mul_one]

/-! ## Case 3: the cross-orbit chain. -/

/-- The `(f∘j)³`-computation of §2 (20) at the shifted point. -/
lemma cross_chain_step (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {α : ↥(FX n)} {ω₁ ωᵢ ωₖ : ↥Q} {r : ↥(FX n)}
    (hω₁ : (ω₁ : G) ∉ fr.Q0) (hωₖ : (ωₖ : G) ∉ fr.Q0)
    (hω₁f : fcan hS.split ω₁ = qconj hS.split (zetaD fr) (ω₁ * zcQF fr α))
    (hsq : ω₁ * ω₁ = zcQF fr r)
    {d₀ d₂ : fr.KW}
    (hA : fcan hS.split (ω₁ * zcQF fr r) = kact hS fr d₀ (ωᵢ * (zcQF fr r * zcQF fr α)))
    (hB : fcan hS.split (ω₁ * (zcQF fr r * zcQF fr α)) = kact hS fr d₂ (ωₖ * zcQF fr r)) :
    ∃ b : fr.KW, fcan hS.split ((fcan hS.split ((fcan hS.split ((ωₖ⁻¹ * zcQF fr r)⁻¹))⁻¹))⁻¹) =
      kact hS fr b (ωᵢ * (zcQF fr r * zcQF fr α)) := by
  have hzrQ0 : (zcQF fr r : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem _ r.2
  have hzαQ0 : (zcQF fr α : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem _ α.2
  have hposQ0 : ((zcQF fr r * zcQF fr α : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul]; exact fr.Q0.mul_mem hzrQ0 hzαQ0
  have hω₁pos1 : ((ω₁ * (zcQF fr r * zcQF fr α) : ↥Q) : G) ≠ 1 :=
    mul_Q0_ne_one fr hω₁ hposQ0
  have hωₖzr1 : ((ωₖ * zcQF fr r : ↥Q) : G) ≠ 1 := mul_Q0_ne_one fr hωₖ hzrQ0
  have hω₁zα1 : ((ω₁ * zcQF fr α : ↥Q) : G) ≠ 1 := mul_Q0_ne_one fr hω₁ hzαQ0
  have hω₁zr1 : ((ω₁ * zcQF fr r : ↥Q) : G) ≠ 1 := mul_Q0_ne_one fr hω₁ hzrQ0
  have hwinv₁ : (ω₁⁻¹ : ↥Q) = ω₁ * zcQF fr r := by
    apply Subtype.ext
    simp only [Subgroup.coe_inv, Subgroup.coe_mul]
    exact inv_eq_mul_zcQF_of_sq fr hsq
  have hfα : fcan hS.split (ω₁ * zcQF fr α) = kact hS fr (fr.ζ⁻¹ : fr.KW) ω₁ := by
    rw [fcan_zcQF_alpha hS fr hω₁ hω₁f, kact_eq_qconj']
    congr 1
  -- step 1: `f(x₅⁻¹) = kact e₂ (ω₁ · pos)`
  have hx5inv : ((ωₖ⁻¹ * zcQF fr r : ↥Q))⁻¹ = ωₖ * zcQF fr r := by
    rw [inv_mul_Q0' fr hzrQ0, inv_inv]
  have h₂ : fcan hS.split (ωₖ * zcQF fr r) =
      kact hS fr ((tconjKW hS fr d₂)⁻¹) (ω₁ * (zcQF fr r * zcQF fr α)) := by
    have h3 : ω₁ * (zcQF fr r * zcQF fr α) =
        kact hS fr (tconjKW hS fr d₂) (fcan hS.split (ωₖ * zcQF fr r)) := by
      rw [← fcan_kact hS fr hωₖzr1 d₂, ← hB]
      exact (Subtype.ext (fcan_fcan hS.split hω₁pos1).1).symm
    have h4 := congrArg (kact hS fr ((tconjKW hS fr d₂)⁻¹)) h3
    simp only [kact_mul, kact_one, mul_inv_cancel] at h4
    exact h4.symm
  have hstep1 : fcan hS.split ((ωₖ⁻¹ * zcQF fr r : ↥Q)⁻¹) =
      kact hS fr ((tconjKW hS fr d₂)⁻¹) (ω₁ * (zcQF fr r * zcQF fr α)) := by
    rw [hx5inv]; exact h₂
  have hposinv : (ω₁ * (zcQF fr r * zcQF fr α))⁻¹ = ω₁ * zcQF fr α :=
    inv_mul_zr_zα fr (inv_eq_mul_zcQF_of_sq fr hsq)
  have hstep2 : (fcan hS.split ((ωₖ⁻¹ * zcQF fr r : ↥Q)⁻¹))⁻¹ =
      kact hS fr ((tconjKW hS fr d₂)⁻¹) (ω₁ * zcQF fr α) := by
    rw [hstep1, kact_inv, hposinv]
  have hstep3 : fcan hS.split ((fcan hS.split ((ωₖ⁻¹ * zcQF fr r : ↥Q)⁻¹))⁻¹) =
      kact hS fr (fr.ζ⁻¹ * tconjKW hS fr ((tconjKW hS fr d₂)⁻¹)) ω₁ := by
    rw [hstep2, fcan_kact hS fr hω₁zα1, hfα, kact_mul]
  have hstep4 : (fcan hS.split ((fcan hS.split ((ωₖ⁻¹ * zcQF fr r : ↥Q)⁻¹))⁻¹))⁻¹ =
      kact hS fr (fr.ζ⁻¹ * tconjKW hS fr ((tconjKW hS fr d₂)⁻¹)) (ω₁ * zcQF fr r) := by
    rw [hstep3, kact_inv, hwinv₁]
  refine ⟨d₀ * tconjKW hS fr (fr.ζ⁻¹ * tconjKW hS fr ((tconjKW hS fr d₂)⁻¹)), ?_⟩
  rw [hstep4, fcan_kact hS fr hω₁zr1, hA, kact_mul]

theorem square_eq_shift_of_good_cover_hKW {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hfpf : Work.PSU3.DFpfBar H Q t) {ι : Type} [Finite ι] (rep : ι → ↥Q) {α : ↥(Work.PSU3.StageB.FX n)}
    (hne : ∀ i, (rep i : G) ∉ fr.Q0)
    (hgood : ∀ i, Work.PSU3.StageB.fcan hS.split (rep i) =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (rep i * Work.PSU3.StageB.zcQF fr α))
    (hcover : ∀ y : ↥Q, (y : G) ∉ fr.Q0 → ∃ i, y ∈ Work.PSU3.StageB.orbKW hS fr (rep i))
    (hdis : ∀ i j, i ≠ j → Multiplicative.toAdd (fr.bar (rep i)) ∉
      Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar (rep j))))
    (hKW : ∀ x : ↥Q, (x : G) ∉ fr.Q0 →
      ((Work.PSU3.StageB.hcan hS.split x : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) :
    ∃ i, rep i * rep i = Work.PSU3.StageB.zcQF fr α := by
  have hex : ∃ y : ↥Q, (y : G) ∉ fr.Q0 := by
    obtain ⟨y, hy⟩ := fr.bar_surjective (Multiplicative.ofAdd (1 : E n))
    refine ⟨y, fun hc => ?_⟩
    have h1 : fr.bar y = 1 := (fr.bar_eq_one_iff y).mpr hc
    rw [hy] at h1
    have h2 : (1 : E n) = 0 := by
      have h3 := congrArg Multiplicative.toAdd h1
      simpa using h3
    exact one_ne_zero h2
  haveI : Nonempty ι := ⟨(hcover hex.choose hex.choose_spec).choose⟩
  let j₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  let ω₁ : ↥Q := rep j₀
  have hω₁ : (ω₁ : G) ∉ fr.Q0 := hne j₀
  have hω₁f : fcan hS.split ω₁ = qconj hS.split (zetaD fr) (ω₁ * zcQF fr α) := hgood j₀
  have hω₁1 : (ω₁ : G) ≠ 1 := fun h => hω₁ (by rw [h]; exact Q0_one_mem fr)
  have hsq_mem : ((ω₁ * ω₁ : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul, ← pow_two]
    exact fr.sq_mem_Q0 ω₁ ω₁.2
  have hsq_ne : (ω₁ * ω₁ : ↥Q) ≠ 1 := by
    intro h
    have h2 : (ω₁ : G) * (ω₁ : G) = 1 := by
      have h3 := congrArg (fun z : ↥Q => (z : G)) h
      simpa [Subgroup.coe_mul] using h3
    exact hω₁ ((fr.mem_Q0_iff ω₁ ω₁.2).mpr (by rw [pow_two]; exact h2))
  obtain ⟨r, hr⟩ := exists_zcQF_eq_of_mem_Q0 fr hsq_mem hsq_ne
  have hsq : ω₁ * ω₁ = zcQF fr r := hr.symm
  have hzrQ0 : (zcQF fr r : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem _ r.2
  have hα_self : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr α))) ∈
      orbE fr (Multiplicative.toAdd (fr.bar ω₁)) := by
    have h1 : fcan hS.split (ω₁ * zcQF fr α) = kact hS fr (fr.ζ⁻¹ : fr.KW) ω₁ := by
      rw [fcan_zcQF_alpha hS fr hω₁ hω₁f, kact_eq_qconj']
      congr 1
    rw [h1, kact_bar]
    exact ⟨fr.ζ⁻¹, rfl⟩
  have hfzr : ((fcan hS.split (ω₁ * zcQF fr r) : ↥Q) : G) ∉ fr.Q0 := by
    intro hc
    have h3 : ((ω₁ * zcQF fr r : ↥Q) : G) ∈ fr.Q0 :=
      (fcan_mem_Q0_iff hS fr (ω₁ * zcQF fr r)).mp hc
    have h4 : (ω₁ : G) ∈ fr.Q0 := by
      have h5 : (ω₁ * zcQF fr r) * zcQF fr r = ω₁ := by rw [mul_assoc, zcQF_sq fr r, mul_one]
      rw [← h5, Subgroup.coe_mul]
      exact fr.Q0.mul_mem h3 hzrQ0
    exact hω₁ h4
  by_cases hself : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr r))) ∈
      orbE fr (Multiplicative.toAdd (fr.bar ω₁))
  · have hrα := self_pos_eq hS fr hω₁ hω₁f hsq hself hKW
    exact ⟨j₀, by show ω₁ * ω₁ = zcQF fr α; rw [hrα] at hsq; exact hsq⟩
  · have hr_ne : fval r ≠ fval α := by
      intro h
      apply hself
      have h2 : zcQF fr r = zcQF fr α := Subtype.ext (by rw [zcQF_coe, zcQF_coe, h])
      rw [h2]; exact hα_self
    have hfix : σE (fval r + fval α) = fval r + fval α := by rw [map_add, r.2, α.2]
    have hne0 : fval r + fval α ≠ 0 := by
      intro h
      apply hr_ne
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
      exact h
    let x₂ : ↥(FX n) := mkFX (fval r + fval α) hfix hne0
    have hval : fval x₂ = fval r + fval α := fval_mkFX _ _ _
    have hzx₂Q0 : (zcQF fr x₂ : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem _ x₂.2
    have hx2_Q0 : ((ω₁ * zcQF fr x₂ : ↥Q) : G) ∉ fr.Q0 := by
      intro hc
      have h4 : (ω₁ : G) ∈ fr.Q0 := by
        have h5 : (ω₁ * zcQF fr x₂) * zcQF fr x₂ = ω₁ := by
          rw [mul_assoc, zcQF_sq fr x₂, mul_one]
        rw [← h5, Subgroup.coe_mul]
        exact fr.Q0.mul_mem hc hzx₂Q0
      exact hω₁ h4
    have hf2 : ((fcan hS.split (ω₁ * zcQF fr x₂) : ↥Q) : G) ∉ fr.Q0 := by
      intro hc
      exact hx2_Q0 ((fcan_mem_Q0_iff hS fr (ω₁ * zcQF fr x₂)).mp hc)
    by_cases hx2self : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr x₂))) ∈
        orbE fr (Multiplicative.toAdd (fr.bar ω₁))
    · have hrα := shifted_pos_eq hS fr hω₁ hω₁f hsq hval hx2self hKW
      exact ⟨j₀, by show ω₁ * ω₁ = zcQF fr α; rw [hrα] at hsq; exact hsq⟩
    · -- the cross case
      obtain ⟨i, hi⟩ := hcover (fcan hS.split (ω₁ * zcQF fr r)) hfzr
      obtain ⟨k, hk⟩ := hcover (fcan hS.split (ω₁ * zcQF fr x₂)) hf2
      have hi_ne : i ≠ j₀ := by
        intro heq
        apply hself
        have h3 := (mem_orbKW_iff_orbE hS fr (rep i) (fcan hS.split (ω₁ * zcQF fr r))).mp hi
        rwa [heq] at h3
      have hk_ne : k ≠ j₀ := by
        intro heq
        apply hx2self
        have h3 := (mem_orbKW_iff_orbE hS fr (rep k) (fcan hS.split (ω₁ * zcQF fr x₂))).mp hk
        rwa [heq] at h3
      have hwi : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr r))) ∈
          orbE fr (Multiplicative.toAdd (fr.bar (rep i))) :=
        (mem_orbKW_iff_orbE hS fr (rep i) (fcan hS.split (ω₁ * zcQF fr r))).mp hi
      have hwk : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr x₂))) ∈
          orbE fr (Multiplicative.toAdd (fr.bar (rep k))) :=
        (mem_orbKW_iff_orbE hS fr (rep k) (fcan hS.split (ω₁ * zcQF fr x₂))).mp hk
      obtain ⟨d₀, hd₀⟩ := cross_orbit_shift_proof hS fr hω₁ (hne i) hω₁f (hgood i)
        (hdis j₀ i (Ne.symm hi_ne)) hwi
      obtain ⟨d₂, hd₂⟩ := cross_orbit_shift_proof hS fr hω₁ (hne k) hω₁f (hgood k)
        (hdis j₀ k (Ne.symm hk_ne)) hwk
      have hzq_all : ∀ (hv : σE (fval r + fval α) = fval r + fval α),
          (zcQ fr (fval r + fval α) hv : ↥Q) = zcQF fr r * zcQF fr α := by
        intro hv
        apply Subtype.ext
        simp only [zcQ_coe, Subgroup.coe_mul, zcQF_coe]
        exact fr.zc_add (fval r) (fval α) r.2 α.2
      have hA : fcan hS.split (ω₁ * zcQF fr r) =
          kact hS fr d₀ (rep i * (zcQF fr r * zcQF fr α)) := by
        rw [hd₀, kact_eq_qconj']
        exact congrArg (fun z : ↥Q =>
          qconj hS.split ⟨(d₀ : G), fr.KW_le d₀.2⟩ (rep i * z)) (hzq_all _)
      have hzx₂ : (zcQF fr r * zcQF fr α : ↥Q) = zcQF fr x₂ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, zcQF_coe]
        rw [hval]
        exact (fr.zc_add (fval r) (fval α) r.2 α.2).symm
      have hzq2 : ∀ (hv : σE (fval x₂ + fval α) = fval x₂ + fval α),
          (zcQ fr (fval x₂ + fval α) hv : ↥Q) = zcQF fr r := by
        intro hv
        apply Subtype.ext
        simp only [zcQ_coe, zcQF_coe]
        rw [hval, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      have hB : fcan hS.split (ω₁ * (zcQF fr r * zcQF fr α)) =
          kact hS fr d₂ (rep k * zcQF fr r) := by
        rw [hzx₂]
        rw [hd₂, kact_eq_qconj']
        exact congrArg (fun z : ↥Q =>
          qconj hS.split ⟨(d₂ : G), fr.KW_le d₂.2⟩ (rep k * z)) (hzq2 _)
      obtain ⟨b, hb_eq⟩ := cross_chain_step hS fr hω₁ (hne k) hω₁f hsq hA hB
      have hx₅_Q0 : (((rep k)⁻¹ * zcQF fr r : ↥Q) : G) ∉ fr.Q0 := by
        intro hc
        have hinv : (((rep k)⁻¹ : ↥Q) : G) ∈ fr.Q0 := by
          have h5 : (rep k)⁻¹ * zcQF fr r * zcQF fr r = (rep k)⁻¹ := by
            rw [mul_assoc, zcQF_sq fr r, mul_one]
          rw [← h5, Subgroup.coe_mul]
          exact fr.Q0.mul_mem hc hzrQ0
        exact hne k (by
          have h6 := (fr.Q0).inv_mem hinv
          rwa [Subgroup.coe_inv, inv_inv] at h6)
      have hx₅_1 : (((rep k)⁻¹ * zcQF fr r : ↥Q) : G) ≠ 1 :=
        fun h => hx₅_Q0 (by rw [h]; exact Q0_one_mem fr)
      set hh : fr.KW := ⟨(hcan hS.split ((rep k)⁻¹ * zcQF fr r) : ↥(twoPoint H t)),
        hKW ((rep k)⁻¹ * zcQF fr r) hx₅_Q0⟩ with hhh
      have hH5 : fcan hS.split
          ((fcan hS.split ((fcan hS.split (((rep k)⁻¹ * zcQF fr r : ↥Q)⁻¹))⁻¹))⁻¹) =
          kact hS fr hh⁻¹ ((rep k)⁻¹ * zcQF fr r) := by
        apply Subtype.ext
        rw [fcan_jjj hS.split hx₅_1]
        simp only [kact_coe, hhh, Subgroup.coe_inv, inv_inv]
      have hcomp : kact hS fr b (rep i * (zcQF fr r * zcQF fr α)) =
          kact hS fr hh⁻¹ ((rep k)⁻¹ * zcQF fr r) := by rw [← hb_eq, hH5]
      have hposQ0 : ((zcQF fr r * zcQF fr α : ↥Q) : G) ∈ fr.Q0 := by
        rw [Subgroup.coe_mul]
        exact fr.Q0.mul_mem hzrQ0 (by rw [zcQF_coe]; exact fr.zc_mem _ α.2)
      have hbw_i : Multiplicative.toAdd (fr.bar (rep i * (zcQF fr r * zcQF fr α))) =
          Multiplicative.toAdd (fr.bar (rep i)) := toAdd_bar_mul_Q0 fr (rep i) hposQ0
      have hbar_eq : (fr.κ b : E n) * Multiplicative.toAdd (fr.bar (rep i)) =
          (fr.κ hh⁻¹ : E n) * Multiplicative.toAdd (fr.bar ((rep k)⁻¹ * zcQF fr r)) := by
        have h := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) hcomp
        rw [kact_bar, kact_bar, hbw_i] at h
        exact h
      have hbar_k_sq : fr.bar (rep k) * fr.bar (rep k) = 1 := by
        have h := bar_eq_one_of_mem_Q0 fr (x := (rep k) ^ 2) (fr.sq_mem_Q0 (rep k) (rep k).2)
        rw [map_pow, pow_two] at h
        exact h
      have hbarx₅ : Multiplicative.toAdd (fr.bar ((rep k)⁻¹ * zcQF fr r)) =
          Multiplicative.toAdd (fr.bar (rep k)) := by
        rw [map_mul, bar_eq_one_of_mem_Q0 fr hzrQ0, mul_one, map_inv,
          inv_eq_of_mul_eq_one_right hbar_k_sq]
      have hmem_ik : Multiplicative.toAdd (fr.bar (rep i)) ∈
          orbE fr (Multiplicative.toAdd (fr.bar (rep k))) := by
        have h4 : (fr.κ (b⁻¹ * hh⁻¹) : E n) =
            (fr.κ b : E n)⁻¹ * (fr.κ hh⁻¹ : E n) := by
          rw [map_mul fr.κ, map_inv fr.κ, Units.val_mul, Units.val_inv_eq_inv_val]
        refine ⟨b⁻¹ * hh⁻¹, ?_⟩
        rw [h4, mul_assoc]
        calc Multiplicative.toAdd (fr.bar (rep i))
            = 1 * Multiplicative.toAdd (fr.bar (rep i)) := by rw [one_mul]
          _ = ((fr.κ b : E n)⁻¹ * (fr.κ b : E n)) * Multiplicative.toAdd (fr.bar (rep i)) := by
                rw [inv_mul_cancel₀ (Units.ne_zero (fr.κ b))]
          _ = (fr.κ b : E n)⁻¹ * ((fr.κ b : E n) * Multiplicative.toAdd (fr.bar (rep i))) := by
                rw [mul_assoc]
          _ = (fr.κ b : E n)⁻¹ * ((fr.κ hh⁻¹ : E n) *
                Multiplicative.toAdd (fr.bar ((rep k)⁻¹ * zcQF fr r))) := by
                rw [← hbar_eq]
          _ = (fr.κ b : E n)⁻¹ * ((fr.κ hh⁻¹ : E n) * Multiplicative.toAdd (fr.bar (rep k))) := by
                rw [hbarx₅]
      have hik : i = k := by
        by_contra hneik
        exact hdis i k hneik hmem_ik
      have hb : b = hh⁻¹ := by
        apply fr.κ_injective
        apply Units.ext
        have h := hbar_eq
        rw [hbarx₅, ← hik] at h
        exact mul_right_cancel₀ (toAdd_bar_ne_zero fr (hne i)) h
      have hrep_eq : rep k * (zcQF fr r * zcQF fr α) = (rep k)⁻¹ * zcQF fr r := by
        have h := hcomp
        rw [hb, hik] at h
        have h2 := congrArg (kact hS fr (hh⁻¹)⁻¹) h
        simpa [kact_mul, kact_one] using h2
      have hsqk_ne : (rep k * rep k : ↥Q) ≠ 1 := by
        intro h
        have h2 : (rep k : G) * (rep k : G) = 1 := by
          have h3 := congrArg (fun z : ↥Q => (z : G)) h
          simpa [Subgroup.coe_mul] using h3
        exact hne k ((fr.mem_Q0_iff (rep k) (rep k).2).mpr (by rw [pow_two]; exact h2))
      have hsqk_mem : ((rep k * rep k : ↥Q) : G) ∈ fr.Q0 := by
        rw [Subgroup.coe_mul, ← pow_two]
        exact fr.sq_mem_Q0 (rep k) (rep k).2
      obtain ⟨r_k, hr_k⟩ := exists_zcQF_eq_of_mem_Q0 fr hsqk_mem hsqk_ne
      have hsqk : rep k * rep k = zcQF fr r_k := hr_k.symm
      have h2 : zcQF fr r_k * (zcQF fr r * zcQF fr α) = zcQF fr r := by
        rw [← hsqk]
        calc (rep k * rep k) * (zcQF fr r * zcQF fr α)
            = rep k * (rep k * (zcQF fr r * zcQF fr α)) := by group
          _ = rep k * ((rep k)⁻¹ * zcQF fr r) := congrArg (fun z : ↥Q => rep k * z) hrep_eq
          _ = (rep k * (rep k)⁻¹) * zcQF fr r := by group
          _ = zcQF fr r := by rw [mul_inv_cancel, one_mul]
      have hsum : fval r_k + fval r + fval α = fval r := by
        have hh2 : fr.zc (fval r_k) * (fr.zc (fval r) * fr.zc (fval α)) = fr.zc (fval r) := by
          have hh3 := congrArg (fun z : ↥Q => (z : G)) h2
          simpa only [Subgroup.coe_mul, zcQF_coe] using hh3
        have h3 : fr.zc (fval r_k + fval r + fval α) = fr.zc (fval r) := by
          rw [fr.zc_add (fval r_k + fval r) (fval α) (by rw [map_add, r_k.2, r.2]) α.2,
            fr.zc_add (fval r_k) (fval r) r_k.2 r.2, mul_assoc]
          exact hh2
        exact fr.zc_inj (fval r_k + fval r + fval α) (fval r)
          (by rw [map_add, map_add, r_k.2, r.2, α.2]) r.2 h3
      have h7 : fval r_k = fval α := by
        have h8 : fval r_k + fval α = 0 := by
          have hcancel : (fval r_k + fval α) + fval r = fval r := by
            rw [show (fval r_k + fval α) + fval r = fval r_k + fval r + fval α from by abel]
            exact hsum
          exact add_eq_left.mp (by rw [add_comm]; exact hcancel)
        rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h8
        exact h8
      have h9 : zcQF fr r_k = zcQF fr α := by
        apply Subtype.ext
        rw [zcQF_coe, zcQF_coe, h7]
      exact ⟨k, by rw [hsqk, h9]⟩

end Work.PSU3.StageB.Omega
