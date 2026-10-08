import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.ThetaOmegaAux
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Frame

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Submission.Blueprint
open Work.PSU3.StageB

namespace Work.PSU3.StageB.StepB

/-- `ζ⁻¹` as an element of `D = twoPoint H t`. -/
noncomputable def zetaInvD {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) : ↥(twoPoint H t) :=
  ⟨(fr.ζ : G)⁻¹, (twoPoint H t).inv_mem (zeta_mem_D fr)⟩

@[simp] lemma zetaInvD_coe {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) : ((zetaInvD fr : ↥(twoPoint H t)) : G) = (fr.ζ : G)⁻¹ :=
  rfl

theorem hcan_mul_zcQF_alpha_mem_KW {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hWKW : Work.ThmF.W H t ≤ fr.KW)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω * Work.PSU3.StageB.zcQF fr α))
    (hWω : ((Work.PSU3.StageB.hcan hS.split ω : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈
      Work.ThmF.W H t) :
    (((Work.PSU3.StageB.hcan hS.split (ω * Work.PSU3.StageB.zcQF fr α) :
      ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) := by
  have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
  have hfω1 : ((fcan hS.split ω : ↥Q) : G) ≠ 1 := fcan_ne_one hS.split hω1
  -- H2/H4c: `h (f ω) = h(ω)⁻¹`
  have hfωh : (hcan hS.split (fcan hS.split ω) : G) = ((hcan hS.split ω : G))⁻¹ :=
    (fcan_fcan hS.split hω1).2.1
  -- the defining relation of `ω` as a *good* element: `f ω = ζ⁻¹ · (ω · zc α) · ζ`
  have hfcoe : ((fcan hS.split ω : ↥Q) : G) =
      (fr.ζ : G)⁻¹ * ((ω * zcQF fr α : ↥Q) : G) * (fr.ζ : G) := by
    have h := congrArg (fun x : ↥Q => (x : G)) hωf
    rw [qconj_coe] at h
    simpa only [zetaD, Subtype.coe_mk] using h
  -- consequently `ω · zc α = (f ω)^{ζ⁻¹}`
  have hq : qconj hS.split (zetaInvD fr) (fcan hS.split ω) = ω * zcQF fr α := by
    apply Subtype.ext
    rw [qconj_coe, zetaInvD_coe, hfcoe]
    group
  -- H4a at `ζ⁻¹` and `f ω`
  have hkey : (hcan hS.split (ω * zcQF fr α) : G) =
      (fr.ζ : G) * ((hcan hS.split ω : G))⁻¹ * (fr.ζ : G)⁻¹ := by
    have h1 := hcan_qconj hS.split hfω1 (zetaInvD fr)
    rw [hq, hfωh] at h1
    rw [h1]
    have hta : t * ((zetaInvD fr : ↥(twoPoint H t)) : G) * t = (fr.ζ : G)⁻¹ := by
      rw [zetaInvD_coe]
      exact t_zeta_inv_t hS.split fr
    rw [hta, zetaInvD_coe]
    group
  rw [hkey]
  exact (fr.KW).mul_mem ((fr.KW).mul_mem fr.ζ.2 ((fr.KW).inv_mem (hWKW hWω)))
    ((fr.KW).inv_mem fr.ζ.2)

end Work.PSU3.StageB.StepB
