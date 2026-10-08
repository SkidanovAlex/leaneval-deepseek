import Mathlib
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_rel4_aux
import Submission.Work.PSU3.StageB.Omega.API

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.PSU3.StageB.NotFpfStep4

open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Elementary complements of `step4_rel4_aux`

The recursion §2 (2) needs the canonical data of `sᵃ = a⁻¹ s a` (with `h(sᵃ) = a²`) rather than the
one of `s^{a⁻¹}`; the two facts below are the analogues of `hcan_sconjF_inv` / `t_hcan_sconjF_inv`. -/

/-- `h (sᵘ) = a · a` for `a = kElF u`. -/
lemma hcan_sconjF (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    (hcan hS.split (sconjF fr u) : G) =
      ((kElF fr u : fr.KW) : G) * ((kElF fr u : fr.KW) : G) := by
  have h := (canon_sconj fr hS.split (kElF fr u) (kElF_mem_Ksub fr u)).2.2
  rw [sconjF_def]
  exact h

/-- `t · h (sᵘ) · t = a⁻¹ · a⁻¹` for `a = kElF u`. -/
lemma t_hcan_sconjF (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    t * (hcan hS.split (sconjF fr u) : G) * t =
      ((kElF fr u : fr.KW) : G)⁻¹ * ((kElF fr u : fr.KW) : G)⁻¹ := by
  rw [hcan_sconjF hS fr u]
  have h1 : t * ((kElF fr u : fr.KW) : G) * t = ((kElF fr u : fr.KW) : G)⁻¹ :=
    tconj_eq_inv hS.split fr (kElF_mem_Ksub fr u)
  calc t * (((kElF fr u : fr.KW) : G) * ((kElF fr u : fr.KW) : G)) * t
      = (t * ((kElF fr u : fr.KW) : G) * t) * (t * ((kElF fr u : fr.KW) : G) * t) :=
        t_conj_mul hS _ _
    _ = ((kElF fr u : fr.KW) : G)⁻¹ * ((kElF fr u : fr.KW) : G)⁻¹ := by rw [h1]

/-- A product `ω · z` with `ω ∉ Q₀` and `z ∈ Q₀` is never trivial. -/
lemma mul_ne_one_of_nonmem (fr : CoarseFrame H Q t n) {ω z : ↥Q}
    (hω : (ω : G) ∉ fr.Q0) (hz : (z : G) ∈ fr.Q0) : ((ω * z : ↥Q) : G) ≠ 1 := by
  intro hc
  rw [Subgroup.coe_mul] at hc
  refine hω ?_
  rw [eq_inv_of_mul_eq_one_left hc]
  exact fr.Q0.inv_mem hz

/-! ## §4 (4), left half -/

theorem step4_rel4_left {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    (hsq : ω * ω = Work.PSU3.StageB.zcQF fr α)
    (a : ↥(Work.PSU3.StageB.FX n)) :
    Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
        (ω⁻¹ * Work.PSU3.StageB.sconjF fr a⁻¹))) =
      (Work.PSU3.StageB.fval a) ^ 2 *
        ((fr.κ fr.ζ : Work.PSU3.E n)⁻¹ *
          Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
            (ω * Work.PSU3.StageB.sconjF fr a)))) := by
  have hω1 : (ω : G) ≠ 1 := fun h => hω (by rw [h]; exact Q0_one_mem fr)
  have hωinv : (ω⁻¹ : G) ∉ fr.Q0 := by
    intro h
    exact hω (by simpa using fr.Q0.inv_mem h)
  -- §2 (2) with `x = ω` and `zc u = sᵃ`
  have hxu : ((ω * zcQF fr (nmF fr a) : ↥Q) : G) ≠ 1 := by
    rw [← sconjF_eq_zcQF fr hS a]
    exact mul_ne_one_of_nonmem fr hω (sconjF_mem_Q0 hS fr a)
  have hrec := fcan_mul_zcQF (x := ω) hS fr hω1 (nmF fr a) hxu
  rw [← sconjF_eq_zcQF fr hS a, ← nmF_inv, ← sconjF_eq_zcQF fr hS a⁻¹,
      t_hcan_sconjF hS fr a] at hrec
  -- `f ω = ζ⁻¹ ω⁻¹ ζ`
  have hfω : fcan hS.split ω = qconj hS.split (zetaD fr) (ω⁻¹) := by
    rw [hf, ← omega_mul_zcQF_eq_inv fr hsq]
  -- `ζ` commutes with `s^{a⁻¹} ∈ Q₀`
  have hqSb : qconj hS.split (zetaD fr) (sconjF fr a⁻¹) = sconjF fr a⁻¹ :=
    qconj_zetaD_Q0 hS fr (sconjF_mem_Q0 hS fr a⁻¹)
  have hcommζ : (fr.ζ : G) * (sconjF fr a⁻¹ : G) = (sconjF fr a⁻¹ : G) * (fr.ζ : G) := by
    have h := congrArg (fun z : ↥Q => (z : G)) hqSb
    rw [qconj_coe] at h
    simp only [zetaD_coe] at h
    calc (fr.ζ : G) * (sconjF fr a⁻¹ : G)
        = (fr.ζ : G) * ((fr.ζ : G)⁻¹ * (sconjF fr a⁻¹ : G) * (fr.ζ : G)) := by rw [h]
      _ = (sconjF fr a⁻¹ : G) * (fr.ζ : G) := by group
  -- `f (ω) · s^{a⁻¹} = (ω⁻¹ · s^{a⁻¹})^ζ`
  have harg : fcan hS.split ω * sconjF fr a⁻¹ =
      qconj hS.split (zetaD fr) (ω⁻¹ * sconjF fr a⁻¹) := by
    rw [hfω]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, qconj_coe, zetaD_coe, Subgroup.coe_inv]
    calc (fr.ζ : G)⁻¹ * (ω : G)⁻¹ * (fr.ζ : G) * (sconjF fr a⁻¹ : G)
        = (fr.ζ : G)⁻¹ * (ω : G)⁻¹ * ((fr.ζ : G) * (sconjF fr a⁻¹ : G)) := by group
      _ = (fr.ζ : G)⁻¹ * (ω : G)⁻¹ * ((sconjF fr a⁻¹ : G) * (fr.ζ : G)) := by rw [hcommζ]
      _ = (fr.ζ : G)⁻¹ * ((ω : G)⁻¹ * (sconjF fr a⁻¹ : G)) * (fr.ζ : G) := by group
  have hY1 : ((ω⁻¹ * sconjF fr a⁻¹ : ↥Q) : G) ≠ 1 :=
    mul_ne_one_of_nonmem (fr := fr) (ω := ω⁻¹) (z := sconjF fr a⁻¹) hωinv
      (sconjF_mem_Q0 hS fr a⁻¹)
  have hYeq : (fcan hS.split (fcan hS.split ω * sconjF fr a⁻¹) : G) =
      (fr.ζ : G)⁻¹ * (fcan hS.split (ω⁻¹ * sconjF fr a⁻¹) : G) * (fr.ζ : G) := by
    rw [harg, fcan_qconj hS.split hY1 (zetaD fr)]
    simp only [zetaD_coe]
    rw [t_zeta_t hS.split fr]
  rw [hYeq] at hrec
  set B : fr.KW := (kElF fr a)⁻¹ * (kElF fr a)⁻¹ with hBdef
  set Y : ↥Q := fcan hS.split (ω⁻¹ * sconjF fr a⁻¹) with hYdef
  set Z : ↥Q := qconj hS.split (zetaD fr) Y with hZdef
  have hBcoe : (B : G) = ((kElF fr a : fr.KW) : G)⁻¹ * ((kElF fr a : fr.KW) : G)⁻¹ := by
    rw [hBdef]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hBcoe] at hrec
  have hZcoe : (Z : G) = (fr.ζ : G)⁻¹ * (Y : G) * (fr.ζ : G) := by
    rw [hZdef, qconj_coe]; simp only [zetaD_coe]
  -- the `Q`-level identity, both sides coerced
  have hQeq : (fcan hS.split (ω * sconjF fr a) : G)
      = ((qconj hS.split ⟨(B : G), fr.KW_le B.2⟩ Z * sconjF fr a⁻¹ : ↥Q) : G) := by
    rw [Subgroup.coe_mul, hrec, qconj_coe, hZcoe]
  have hwe : fcan hS.split (ω * sconjF fr a)
      = qconj hS.split ⟨(B : G), fr.KW_le B.2⟩ Z * sconjF fr a⁻¹ := Subtype.ext hQeq
  have hbar := congrArg fr.bar hwe
  rw [map_mul, bar_sconjF_eq_one hS fr a⁻¹, mul_one] at hbar
  have hκB : (fr.κ B : E n) = (fval a)⁻¹ * (fval a)⁻¹ := by
    have h2 : fr.κ B = (fr.κ (kElF fr a))⁻¹ * (fr.κ (kElF fr a))⁻¹ := by
      simp only [hBdef, map_mul, map_inv]
    rw [h2]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, kappa_kElF]
  have hstep0 := congrArg Multiplicative.toAdd hbar
  rw [qconj_KW_bar hS fr B Z, hZdef, bar_qconj_zetaD hS fr Y, hκB] at hstep0
  rw [hstep0]
  have hβ : (fval a) ≠ 0 := Units.ne_zero _
  have hγ : (fr.κ fr.ζ : E n) ≠ 0 := Units.ne_zero _
  field_simp

end Work.PSU3.StageB.NotFpfStep4
