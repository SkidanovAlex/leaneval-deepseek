/-
# `N4C/rows/rowN1sg` — §8 row 10 (`N₁^{sg} = 2ℛ(Φ̃_*)·g`) in the honest class

`CtxT` carries the honest profile data (`ClassC α g`, `CoerAdmO α g`) and the *upgraded* star
package `StarPkgo2 α Cs Φs`, whose field `RW` is exactly the `𝒲^{4,∞}`-pricing of the star
coefficient `H = ((z+1)/z)·ℛ(Φ̃_*)` that rows 10/11 need (the field that the older
`StarPkgo`/`WDp`-priced interfaces lack, see `NonlinRows/NRow10.lean`).

With that field the row is the product rule `N4Norm'.wprod` applied to `H` and to the bounded
radial factor `φ(z) = z/(1+z)`:

  `N₁^{sg} = 2·H·(φ·g)`  on the open quadrant,

`WlInf α 4 H ≤ Cs·α` (so the `α^{-1/2}` of `wprod` becomes `√α`), and `φ` costs nothing in
`ℋ⁴` (`NRow10aux.mul_phi_Hk`).  The proof is the body of `NonlinRows.NRow10_of_WlInfStar` /
`NonlinRows.NRow10T2`, transposed to the honest vocabulary; the `IP`-level hypothesis `hE` is
*not* used by this row.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.HonDecay
import Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
import Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.Nonlinear.Pieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem rowN1sg (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨Cφ, hCφ, hφb⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  refine ⟨2 * Ci * (Cφ * Cφ + 1) * max Cs 0 + 1, by positivity, ?_⟩
  intro α g Φs Φg hCtx
  have hα : 0 < α := hCtx.hα
  have hα1 : α ≤ 1 := hCtx.hα1
  have hαα₂ : α ≤ α₂ := hCtx.hαα₂
  have hs2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hCtx.hs
  have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
  -- the star coefficient `H = ((z+1)/z)·ℛ(Φ̃_*)`, in the `𝒲^{4,∞}`-class with the `α`-rate
  obtain ⟨hHmem, hHle⟩ := hs2.RW
  have hHle' : Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      ≤ max Cs 0 * α :=
    le_trans hHle (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
  have hHsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen hα hα1 hs
  -- the bounded radial factor `φ(z) = z/(1+z)`
  have hg4 : Work.FTS.VocabO.HQo α 4 g := hCtx.hqo4
  obtain ⟨hφmem, hφbnd⟩ := hφb hα hα1 hg4
  have hφsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * g z θ) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 / (1 + p.1)) Work.FTS.EllipticEst.Q0 := by
      refine ContDiffOn.div ?_ ?_ ?_
      · exact contDiffOn_fst
      · exact contDiffOn_const.add contDiffOn_fst
      · intro p hp
        have hp1 : (0 : ℝ) < 1 + p.1 := by
          have := Set.mem_Ioi.mp hp.1
          linarith
        positivity
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0 := hg4.1
    exact h1.mul h2
  -- the product rule of the primed interface, priced by the weighted norm
  have hprod := hN.wprod α ⟨hα, hαα₂⟩
    (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    (fun z θ => z / (1 + z) * g z θ) hHsm hHmem ⟨hφsm, hφmem⟩
  -- the row-10 piece is `2` times that product on the open quadrant
  have hagree : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Nonlin.N1sg α Φs g z θ
        = 2 * (((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
            * (z / (1 + z) * g z θ)) := by
    intro z θ hz _ _
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    simp only [Work.FTS.Nonlin.N1sg]
    field_simp
    ring
  have hSeq : Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N1sg α Φs g)
      = Work.Spaces.HkSq α 4
          (fun z θ => 2 * (((z + 1) / z
              * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
            * (z / (1 + z) * g z θ))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 hagree
  have hXn : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
      = 2 * Work.FTS.Nonlin.Xn α
          (fun z θ => ((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
            * (z / (1 + z) * g z θ)) := by
    rw [show Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
          = Work.FTS.Nonlin.Xn α
              (fun z θ => 2 * (((z + 1) / z
                  * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
                * (z / (1 + z) * g z θ))) from by
        simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hSeq],
      Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α 2
        (fun z θ => ((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
          * (z / (1 + z) * g z θ)),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hXn]
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hS : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.sqrt_nonneg α) hXg
  have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
    rw [Real.sqrt_eq_rpow]
    have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
    rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
    exact h.symm
  have hbnd1 : Work.FTS.Nonlin.Xn α
        (fun z θ => ((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
          * (z / (1 + z) * g z θ))
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cφ * Work.FTS.Nonlin.Xn α g) := by
    refine le_trans hprod.2 ?_
    have hWnn : 0 ≤ Work.Spaces.WlInf α 4
        (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
      Work.Spaces.WlInf_nonneg α 4 _ hHmem
    have hA : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hCi.le (Real.rpow_nonneg hα.le _)
    have hB : 0 ≤ Cφ * Work.FTS.Nonlin.Xn α g := mul_nonneg hCφ.le hXg
    calc Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4
            (fun z θ => (z + 1) / z
              * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
            * Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4
            (fun z θ => (z + 1) / z
              * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
            * (Cφ * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_left hφbnd (mul_nonneg hA hWnn)
      _ = Ci * α ^ (-(1 / 2 : ℝ)) * (Cφ * Work.FTS.Nonlin.Xn α g)
            * Work.Spaces.WlInf α 4
              (fun z θ => (z + 1) / z
                * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) := by ring
      _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cφ * Work.FTS.Nonlin.Xn α g)
            * (max Cs 0 * α) := mul_le_mul_of_nonneg_left hHle' (mul_nonneg hA hB)
      _ = Ci * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α)
            * (Cφ * Work.FTS.Nonlin.Xn α g) := by ring
  have hbnd2 : 2 * Work.FTS.Nonlin.Xn α
        (fun z θ => ((z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
          * (z / (1 + z) * g z θ))
      ≤ (2 * Ci * Cφ * max Cs 0) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
    refine le_trans (mul_le_mul_of_nonneg_left hbnd1 (by norm_num)) ?_
    rw [show 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α)
          * (Cφ * Work.FTS.Nonlin.Xn α g))
        = 2 * Ci * Cφ * max Cs 0 * (α ^ (-(1 / 2 : ℝ)) * α)
            * Work.FTS.Nonlin.Xn α g from by ring, hsqrt]
    exact le_of_eq (by ring)
  refine le_trans hbnd2 ?_
  have hCs : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hle : 2 * Ci * Cφ * max Cs 0 ≤ 2 * Ci * (Cφ * Cφ + 1) * max Cs 0 + 1 := by
    have hφ' : Cφ ≤ Cφ * Cφ + 1 := by nlinarith [hCφ.le]
    nlinarith [hCi.le, hCs, hφ', mul_nonneg hCi.le hCs, sq_nonneg Cφ]
  exact mul_le_mul_of_nonneg_right hle hS

end Work.FTS.StrongEps.E4R3.N4C.rows
