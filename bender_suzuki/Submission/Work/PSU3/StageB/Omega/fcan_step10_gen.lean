import Mathlib
import Submission.Work.PSU3.StageB.Omega.fcan_step10
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

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Additivity of `zc` for a general element of the fixed field

This is `zcQF_mul_zcQF_inv` with `v : E n` (rather than `v : F*`) allowed, so that it
applies also to `v = 0`. -/

/-- `zc (α + u^{-1}) = zc α · zc u^{-1}` for any `σE`-fixed `v` with `v = α + u⁻¹`. -/
lemma zcQ_eq_zcQF_mul_inv (fr : CoarseFrame H Q t n) {α u : ↥(FX n)} {v : E n}
    (hv : σE v = v) (huv : v = fval α + (fval u)⁻¹) :
    zcQ fr v hv = zcQF fr α * zcQF fr u⁻¹ := by
  apply Subtype.ext
  have hfix : σE ((fval u)⁻¹) = (fval u)⁻¹ := by rw [map_inv₀, u.2]
  rw [Subgroup.coe_mul, zcQ_coe, zcQF_coe, zcQF_coe, huv,
    fr.zc_add (fval α) ((fval u)⁻¹) α.2 hfix, fval_inv]

/-! ## The shift of the `f`-argument, for a general `v : E n` -/

/-- `f (f(ω) · zc u⁻¹) = ζ⁻¹ · f (ω · zc v) · ζ` for a general `σE`-fixed `v = α + u⁻¹`.
This is `fcan_mid_aux` with `v : E n`. -/
lemma fcan_mid_aux_gen (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} {α : ↥(FX n)}
    (hωf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    {u : ↥(FX n)} {v : E n} (hv : σE v = v) (huv : v = fval α + (fval u)⁻¹)
    (hX : ((ω * zcQ fr v hv : ↥Q) : G) ≠ 1) :
    (fcan hS.split (fcan hS.split ω * zcQF fr u⁻¹) : G) =
      (fr.ζ : G)⁻¹ * (fcan hS.split (ω * zcQ fr v hv) : G) * (fr.ζ : G) := by
  have hZcm : zcQ fr v hv = zcQF fr α * zcQF fr u⁻¹ := zcQ_eq_zcQF_mul_inv fr hv huv
  have hf : (fcan hS.split ω : G) = (fr.ζ : G)⁻¹ * ((ω : G) * (zcQF fr α : G)) * (fr.ζ : G) := by
    have hh := congrArg (fun z : ↥Q => (z : G)) hωf
    rw [qconj_coe, Subgroup.coe_mul] at hh
    exact hh
  have hcz' : (fr.ζ : G) * (zcQF fr u⁻¹ : G) = (zcQF fr u⁻¹ : G) * (fr.ζ : G) :=
    zeta_comm_zcQF fr u⁻¹
  have hmid : fcan hS.split ω * zcQF fr u⁻¹ =
      qconj hS.split ⟨(fr.ζ : G), zeta_mem_D fr⟩ (ω * zcQ fr v hv) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, qconj_coe, hf]
    simp only [Subgroup.coe_mul]
    rw [show (zcQ fr v hv : G) = (zcQF fr α : G) * (zcQF fr u⁻¹ : G) from by
      rw [hZcm, Subgroup.coe_mul]]
    calc (fr.ζ : G)⁻¹ * ((ω : G) * (zcQF fr α : G)) * (fr.ζ : G) * (zcQF fr u⁻¹ : G)
        = (fr.ζ : G)⁻¹ * (ω : G) * (zcQF fr α : G) * ((fr.ζ : G) * (zcQF fr u⁻¹ : G)) := by
          group
      _ = (fr.ζ : G)⁻¹ * (ω : G) * (zcQF fr α : G) * ((zcQF fr u⁻¹ : G) * (fr.ζ : G)) := by
          rw [hcz']
      _ = (fr.ζ : G)⁻¹ * ((ω : G) * ((zcQF fr α : G) * (zcQF fr u⁻¹ : G))) * (fr.ζ : G) := by
          group
  rw [hmid, fcan_qconj hS.split hX ⟨(fr.ζ : G), zeta_mem_D fr⟩, t_zeta_t hS.split fr]

/-! ## §2 (10), general form -/

theorem fcan_step10_gen {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    {u : ↥(Work.PSU3.StageB.FX n)} {v : Work.PSU3.E n} (hv : Work.PSU3.σE v = v)
    (huv : v = Work.PSU3.StageB.fval α + (Work.PSU3.StageB.fval u)⁻¹)
    (h1 : ((ω * Work.PSU3.StageB.zcQF fr u : ↥Q) : G) ≠ 1) :
    (Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.zcQF fr u) : G) =
      ((Work.PSU3.StageB.zetaExp hS fr u : fr.KW) : G)⁻¹ *
        ((Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.zcQ fr v hv) *
            Work.PSU3.StageB.zcQF fr u : ↥Q) : G) *
        ((Work.PSU3.StageB.zetaExp hS fr u : fr.KW) : G) := by
  have hExp : ((zetaExp hS fr u : fr.KW) : G) =
      (fr.ζ : G) * (kElF fr (tau hS fr u) : G)⁻¹ * (kElF fr (tau hS fr u) : G)⁻¹ := by
    simp only [zetaExp, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hExp, Subgroup.coe_mul]
  set A : G := (kElF fr (tau hS fr u) : G) with hA
  set Z : G := (fr.ζ : G) with hZ
  set ZcU : G := (zcQF fr u : G) with hZcU
  set ZcU' : G := (zcQF fr u⁻¹ : G) with hZcU'
  set F : G := (fcan hS.split (ω * zcQ fr v hv) : G) with hF
  have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
  have hX : ((ω * zcQ fr v hv : ↥Q) : G) ≠ 1 := by
    intro hc
    have hmem : (zcQ fr v hv : G) ∈ fr.Q0 := by
      rw [zcQ_coe]; exact fr.zc_mem v hv
    have h2 : (ω : G) = ((ω * zcQ fr v hv : ↥Q) : G) * (zcQ fr v hv : G)⁻¹ := by
      rw [Subgroup.coe_mul]; group
    exact hω (by rw [h2, hc, one_mul]; exact fr.Q0.inv_mem hmem)
  have hrec := fcan_mul_zcQF_A hS fr hω1 u h1
  rw [← hA, ← hZcU'] at hrec
  have hmid := fcan_mid_aux_gen hS fr hωf hv huv hX
  rw [← hZ, ← hF] at hmid
  obtain ⟨hZu, hZu'⟩ := zcQF_eq_sconjF hS fr u
  rw [← hZcU, ← hA] at hZu
  rw [← hZcU', ← hA] at hZu'
  -- `A` and `Z` commute (`a ∈ Ksub ≤ KW` is abelian)
  have hAZ : A * Z = Z * A := by
    rw [hA, hZ]
    exact KW_comm fr (kElF fr (tau hS fr u)) fr.ζ
  have h1Z : Z⁻¹ * A * Z = A := by
    calc Z⁻¹ * A * Z = Z⁻¹ * (A * Z) := by group
      _ = Z⁻¹ * (Z * A) := by rw [hAZ]
      _ = A := by group
  have h1ZA : Z⁻¹ * A⁻¹ * Z = A⁻¹ := by
    calc Z⁻¹ * A⁻¹ * Z = (Z⁻¹ * A * Z)⁻¹ := by group
      _ = A⁻¹ := by rw [h1Z]
  have hZs : Z * frameS fr = frameS fr * Z := by rw [hZ]; exact zeta_comm_frameS fr
  have h1s : Z⁻¹ * frameS fr * Z = frameS fr := by
    calc Z⁻¹ * frameS fr * Z = Z⁻¹ * (frameS fr * Z) := by group
      _ = Z⁻¹ * (Z * frameS fr) := by rw [hZs]
      _ = frameS fr := by group
  have hXZ : Z⁻¹ * (A⁻¹ * frameS fr * A) * Z = A⁻¹ * frameS fr * A := by
    calc Z⁻¹ * (A⁻¹ * frameS fr * A) * Z
        = (Z⁻¹ * A⁻¹ * Z) * (Z⁻¹ * frameS fr * Z) * (Z⁻¹ * A * Z) := by group
      _ = A⁻¹ * frameS fr * A := by rw [h1ZA, h1s, h1Z]
  -- the conjugation by `ζ a^{-2}` sends `zc u` to `zc u⁻¹`
  have hkey : (Z*A⁻¹*A⁻¹)⁻¹ * ZcU * (Z*A⁻¹*A⁻¹) = ZcU' := by
    rw [hZu, hZu']
    rw [show (Z*A⁻¹*A⁻¹)⁻¹ = A*A*Z⁻¹ from by
      simp only [mul_inv_rev, inv_inv]; group]
    rw [show A*A*Z⁻¹ * (A⁻¹ * frameS fr * A) * (Z*A⁻¹*A⁻¹)
          = A*A * (Z⁻¹ * (A⁻¹ * frameS fr * A) * Z) * A⁻¹*A⁻¹ from by group]
    rw [hXZ]
    group
  have hK : (Z*A⁻¹*A⁻¹) * ZcU' = ZcU * (Z*A⁻¹*A⁻¹) := by
    rw [← hkey]
    group
  calc (fcan hS.split (ω * zcQF fr u) : G)
      = (A*A) * (Z⁻¹ * F * Z) * (A*A)⁻¹ * ZcU' := by rw [hrec, hmid]
    _ = ((Z*A⁻¹*A⁻¹)⁻¹ * F * (Z*A⁻¹*A⁻¹)) * ZcU' := by
          rw [show (A*A)⁻¹ = A⁻¹ * A⁻¹ from by group]
          rw [show (Z*A⁻¹*A⁻¹)⁻¹ = A*A*Z⁻¹ from by
            simp only [mul_inv_rev, inv_inv]; group]
          group
    _ = (Z*A⁻¹*A⁻¹)⁻¹ * F * ((Z*A⁻¹*A⁻¹) * ZcU') := by group
    _ = (Z*A⁻¹*A⁻¹)⁻¹ * F * (ZcU * (Z*A⁻¹*A⁻¹)) := by rw [hK]
    _ = (Z*A⁻¹*A⁻¹)⁻¹ * (F * ZcU) * (Z*A⁻¹*A⁻¹) := by group

end Work.PSU3.StageB.Omega
