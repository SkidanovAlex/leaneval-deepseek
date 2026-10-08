/-
# `Work.PSU3.StageB.StepB.self_pos_eq_mem_KW` — §2 (20), self-position, `hcan ω ∈ KW` only

This is the crux `Work.PSU3.StageB.Omega.self_pos_eq` of Peterfalvi II Ch. VII §2 (20) in the
*self-orbit* case, with the hypothesis that its proof uses weakened to the single point `ω`:
that proof invokes `hKW` only at `ω` (to build the `KW`-element `hcan ω`).

Statement: for `ω ∈ Q \ Q₀` with `f(ω) = (ω · zc α)^ζ` (i.e. `ω` is *good* with shift `α`),
if `ω² = zc r` (`r ∈ F*`) and the `bar`-image of `f(ω · zc r)` lies in the `KW`-orbit of
`bar ω` (i.e. `r` is a *self*-position), then `r = α`, provided only that `hcan ω ∈ KW`.

The proof (identical to that of `Omega.self_pos_eq`, with `hKW ω hω` replaced by the
hypothesis `hWω`) composes the `(f ∘ j)³`-values along the chain

  `f (ω · zc r) = ω^d · (ω · zc(r+α))`,  `ω⁻¹ = ω · zc r`,
  `f (ω · zc α) = ω^{ζ⁻¹}`,  `f ((f (ω⁻¹))⁻¹) = (ζ⁻¹ · d^t) · ω`,
  `f (…) = (d · (ζ⁻¹ · d^t)^t) · (ω · zc(r+α))`,

and the H5-identity `(f ∘ j)³(x) = h(x) x h(x)⁻¹`; comparing the two `KW`-conjugators and using
the injectivity of `κ` yields `zc r · zc α = 1`, hence `r = α`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Omega.square_eq_shift_of_good_cover_hKW
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.good_shift_of_mem_selfSet

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
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB
open Work.PSU3.StageB.Omega
open Classical

namespace Work.PSU3.StageB.StepB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

theorem self_pos_eq_mem_KW {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω * Work.PSU3.StageB.zcQF fr α))
    {r : ↥(Work.PSU3.StageB.FX n)} (hsq : ω * ω = Work.PSU3.StageB.zcQF fr r)
    (hmem : Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.zcQF fr r)))
      ∈ Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar ω)))
    (hWω : ((Work.PSU3.StageB.hcan hS.split ω : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) :
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
  set hh : fr.KW := ⟨(hcan hS.split ω : ↥(twoPoint H t)), hWω⟩ with hhh
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

end Work.PSU3.StageB.StepB
