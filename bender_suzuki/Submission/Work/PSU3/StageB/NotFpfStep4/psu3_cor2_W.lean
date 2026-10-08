/-
# `psu3_cor2_W`: Peterfalvi's Cor. (Ch. VII §1) for the model `PSU(3,2ⁿ)`, `W`-form

Given `ζ ∈ W(B̄, w̄)` with `ζ ≠ 1` (`B̄ = psu3B n` the Borel, `w̄ = psu3Weyl n` the Weyl
element of the model `PSU(3,2ⁿ)`), there is `ω ∈ Ū = psu3U n` with

  `ω² ≠ 1`,  `f(ω) = ζ⁻¹ ω⁻¹ ζ`,  `h(ω) = ζ³`,

where `f, h` are the canonical maps of Peterfalvi II Ch. VII §1 (`Work.PSU3.StageB.fcan`,
`hcan`), i.e. the canonical decomposition `w̄ ω w̄ = g(ω) h(ω) w̄ f(ω)`.

Proof.  `W(B̄, w̄) = C_D(w̄)` (the two-point stabiliser `D = B̄ ⊓ B̄^{w̄} = T̄` is the abelian
torus), so `ζ = psu3Hom (suTgSU a)` for some `a ∈ (GF(q²))ˣ` with `a^{q+1} = 1` and `a³ ≠ 1`
(`WTorusLift`).  Apply the model corollary `Work.PSU3.Model.psu3_cor2` with the unit
`b = a⁻³`: it produces `p ∈ SZ(E)` with `p.x ≠ 0`, `p.y = a³` and
`fMapTot p = torusAct b p⁻¹`, and `ω = psu3UEquiv p` is the desired element.  The canonical
data of `ω` are read off `weylFactorM_decomp` + `canon_unique''` (as in `psu3_cor2_hcan`):
`hcan ω = psu3Hom (suTgSU (σ(p.y))⁻¹) = psu3Hom (suTgSU a³) = ζ³`, and `fcan ω = Ā(fMapTot p)`;
finally `torusConj` rewrites `ζ⁻¹ ω⁻¹ ζ` as `Ā(torusAct b p⁻¹) = Ā(fMapTot p)`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.Model.psu3_datum
import Submission.Work.PSU3.Model.psu3_cor2
import Submission.Work.PSU3.StageB.NotFpfStep4.psu3_cor2_hcan
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageB.NotFpfStep4.WTorusLift
import Submission.Work.PSU3.StageB.NotFpfStep4.torusConj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Matrix LeanEval.GroupTheory.Defs

namespace Work.PSU3.StageB.NotFpfStep4

theorem psu3_cor2_W {n : ℕ} (hn : 2 ≤ n) {ζ : LeanEval.GroupTheory.Defs.PSU3Model n}
    (hζ : ζ ∈ Work.ThmF.W (Submission.PSU3.psu3B n) (Submission.PSU3.psu3Weyl n)) (hζ1 : ζ ≠ 1) :
    ∃ ω : ↥(Submission.PSU3.psu3U n),
      ((ω : LeanEval.GroupTheory.Defs.PSU3Model n) *
        (ω : LeanEval.GroupTheory.Defs.PSU3Model n) ≠ 1) ∧
      ((Work.PSU3.StageB.fcan (Work.PSU3.Model.psu3_isSplitRankOne n hn) ω :
          ↥(Submission.PSU3.psu3U n)) : LeanEval.GroupTheory.Defs.PSU3Model n)
        = ζ⁻¹ * (ω : LeanEval.GroupTheory.Defs.PSU3Model n)⁻¹ * ζ ∧
      ((Work.PSU3.StageB.hcan (Work.PSU3.Model.psu3_isSplitRankOne n hn) ω :
          ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
            (Submission.PSU3.psu3Weyl n))) : LeanEval.GroupTheory.Defs.PSU3Model n)
        = ζ ^ 3 := by
  obtain ⟨a, hζa, ha_q1, ha3⟩ := WTorusLift hn hζ hζ1
  set b : (Submission.PSU3.F n)ˣ := a⁻¹ ^ 3 with hbdef
  have hbval : (b : Submission.PSU3.F n) = (a : Submission.PSU3.F n)⁻¹ ^ 3 := by
    rw [hbdef, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  have haq : (a : Submission.PSU3.F n) ^ (2 ^ n) = (a : Submission.PSU3.F n)⁻¹ := by
    have h := ha_q1
    rw [pow_succ] at h
    exact eq_inv_of_mul_eq_one_left h
  have hb1 : b ≠ 1 := by
    intro hb
    apply ha3
    have h : (b : Submission.PSU3.F n) = 1 := by rw [hb]; rfl
    have h' : ((a : Submission.PSU3.F n)⁻¹) ^ 3 = 1 := by rwa [hbval] at h
    have h'' := congrArg (fun z : Submission.PSU3.F n => z⁻¹) h'
    rwa [inv_pow, inv_inv, inv_one] at h''
  have hbsq : (b : Work.PSU3.E n) * Work.PSU3.σE (b : Work.PSU3.E n) = 1 := by
    rw [hbval]
    have hσa : Work.PSU3.σE (a : Submission.PSU3.F n) = (a : Submission.PSU3.F n)⁻¹ := by
      rw [Work.PSU3.Model.sigmaE_eq_pow, haq]
    have hsig : Work.PSU3.σE ((a : Submission.PSU3.F n)⁻¹ ^ 3) =
        (a : Submission.PSU3.F n) ^ 3 := by
      rw [show (a : Submission.PSU3.F n)⁻¹ ^ 3 = (((a : Submission.PSU3.F n)) ^ 3)⁻¹ from
        inv_pow (a : Submission.PSU3.F n) 3]
      rw [map_inv₀, map_pow, hσa, inv_pow, inv_inv]
    rw [hsig, ← mul_pow, inv_mul_cancel₀ (Units.ne_zero a), one_pow]
  obtain ⟨p, hpx, hpy, hpf⟩ := Work.PSU3.Model.psu3_cor2 n b hb1 hbsq
  have hpne : p ≠ 1 := by
    intro hp
    have h0 : p.y = 0 := by rw [hp]; rfl
    rw [hpy] at h0
    exact inv_ne_zero (Units.ne_zero b) h0
  have hpynz : p.y ≠ 0 := Work.PSU3.SZ.y_ne_zero_of_ne_one hpne
  -- ## canonical data of ω
  obtain ⟨g, hh, hhh, hdec⟩ := weylFactorM_decomp
    (ζ := Units.mk0 (Work.PSU3.σE p.y) (Work.PSU3.Model.sigma_ne_zero hpynz)) p hpne rfl
  have hA : ((Work.PSU3.Model.psu3UEquiv n hn p : ↥(Submission.PSU3.psu3U n)) :
      LeanEval.GroupTheory.Defs.PSU3Model n) ≠ 1 := by
    intro hcon
    have h2 : Work.PSU3.Model.psu3UEquiv n hn p = 1 := by
      apply Subtype.ext; simpa using hcon
    exact hpne ((Work.PSU3.Model.psu3UEquiv n hn).injective (by rw [h2, map_one]))
  have heq : Submission.PSU3.psu3Weyl n *
        ((Work.PSU3.Model.psu3UEquiv n hn p : ↥(Submission.PSU3.psu3U n)) :
          LeanEval.GroupTheory.Defs.PSU3Model n) *
        Submission.PSU3.psu3Weyl n =
      (g : LeanEval.GroupTheory.Defs.PSU3Model n) *
        (hh : LeanEval.GroupTheory.Defs.PSU3Model n) *
        Submission.PSU3.psu3Weyl n *
        ((Work.PSU3.Model.psu3UEquiv n hn (Work.PSU3.SZ.fMap p hpne) :
            ↥(Submission.PSU3.psu3U n)) : LeanEval.GroupTheory.Defs.PSU3Model n) := by
    rw [Work.PSU3.Model.psu3UEquiv_apply, Work.PSU3.Model.psu3UEquiv_apply, ← hdec]
    exact Work.PSU3.Model.psu3_weylConj_pglHom n p hpne
  obtain ⟨-, hcan_eq, hfcan_eq⟩ := Work.PSU3.StageB.canon_unique'' (H := Submission.PSU3.psu3B n)
    (Q := Submission.PSU3.psu3U n) (t := Submission.PSU3.psu3Weyl n)
    (Work.PSU3.Model.psu3_isSplitRankOne n hn) hA heq
  have hwinv2 : ((Work.PSU3.Model.psu3UEquiv n hn p : ↥(Submission.PSU3.psu3U n)) :
      LeanEval.GroupTheory.Defs.PSU3Model n)⁻¹ =
      ((Work.PSU3.Model.psu3UEquiv n hn p⁻¹ : ↥(Submission.PSU3.psu3U n)) :
        LeanEval.GroupTheory.Defs.PSU3Model n) := by
    rw [← Subgroup.coe_inv (H := Submission.PSU3.psu3U n), ← map_inv]
  have hζ0 : (Units.mk0 (Work.PSU3.σE p.y) (Work.PSU3.Model.sigma_ne_zero hpynz)) = b := by
    apply Units.ext
    change Work.PSU3.σE p.y = (b : Work.PSU3.E n)
    rw [hpy, map_inv₀, eq_inv_of_mul_eq_one_right hbsq, inv_inv]
  have hbinv : b⁻¹ = a ^ 3 := by
    rw [hbdef, inv_pow, inv_inv]
  refine ⟨Work.PSU3.Model.psu3UEquiv n hn p, ?_, ?_, ?_⟩
  · -- ω · ω ≠ 1
    intro hcon
    have h1 : ((Work.PSU3.Model.psu3UEquiv n hn (p * p) :
        ↥(Submission.PSU3.psu3U n)) : LeanEval.GroupTheory.Defs.PSU3Model n) = 1 := by
      rw [map_mul, Subgroup.coe_mul]
      exact hcon
    have h2 : Work.PSU3.Model.psu3UEquiv n hn (p * p) = 1 := by
      apply Subtype.ext; simpa using h1
    have h3 : p * p = 1 := (Work.PSU3.Model.psu3UEquiv n hn).injective (by rw [h2, map_one])
    have hy : p.x * Work.PSU3.σE p.x = 0 := by
      have h := congrArg Work.PSU3.SZ.y h3
      rw [Work.PSU3.SZ.mul_y, Work.PSU3.SZ.one_y] at h
      have hpyy : p.y + p.y = 0 := CharTwo.add_self_eq_zero p.y
      rwa [hpyy, zero_add] at h
    exact (mul_ne_zero hpx (Work.PSU3.Model.sigma_ne_zero hpx)) hy
  · -- fcan ω = ζ⁻¹ ω⁻¹ ζ
    have hL : ((Work.PSU3.StageB.fcan (H := Submission.PSU3.psu3B n)
          (Q := Submission.PSU3.psu3U n) (t := Submission.PSU3.psu3Weyl n)
          (Work.PSU3.Model.psu3_isSplitRankOne n hn)
          (Work.PSU3.Model.psu3UEquiv n hn p) : ↥(Submission.PSU3.psu3U n)) :
        LeanEval.GroupTheory.Defs.PSU3Model n) =
        (⟨Work.PSU3.pglHom (Work.PSU3.SZ.torusAct b p⁻¹),
          Work.PSU3.Model.pglHom_mem_PSU3Model n _⟩ : LeanEval.GroupTheory.Defs.PSU3Model n) := by
      rw [← hfcan_eq, Work.PSU3.Model.psu3UEquiv_apply]
      apply Subtype.ext
      rw [← Work.PSU3.fMapTot_of_ne_one hpne, hpf]
    have hR : ζ⁻¹ * ((Work.PSU3.Model.psu3UEquiv n hn p : ↥(Submission.PSU3.psu3U n)) :
        LeanEval.GroupTheory.Defs.PSU3Model n)⁻¹ * ζ =
        (⟨Work.PSU3.pglHom (Work.PSU3.SZ.torusAct b p⁻¹),
          Work.PSU3.Model.pglHom_mem_PSU3Model n _⟩ : LeanEval.GroupTheory.Defs.PSU3Model n) := by
      rw [hζa, hwinv2, Work.PSU3.Model.psu3UEquiv_apply]
      rw [show b = a⁻¹ ^ 3 from hbdef]
      exact torusConj hn a ha_q1 p⁻¹
    exact hL.trans hR.symm
  · -- hcan ω = ζ³
    show ((Work.PSU3.StageB.hcan (H := Submission.PSU3.psu3B n)
        (Q := Submission.PSU3.psu3U n) (t := Submission.PSU3.psu3Weyl n)
        (Work.PSU3.Model.psu3_isSplitRankOne n hn)
        (Work.PSU3.Model.psu3UEquiv n hn p)) : LeanEval.GroupTheory.Defs.PSU3Model n) = ζ ^ 3
    rw [← hcan_eq, hhh]
    rw [hζ0]
    rw [hbinv]
    show (Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n (a ^ 3))) = ζ ^ 3
    have hpow : Submission.PSU3.suTgSU n (a ^ 3) = (Submission.PSU3.suTgSU n a) ^ 3 :=
      map_pow (Submission.PSU3.suTgSU n) a 3
    rw [hpow, map_pow, ← hζa]

end Work.PSU3.StageB.NotFpfStep4
