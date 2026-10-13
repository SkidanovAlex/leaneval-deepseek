import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row18
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Row 18 of the design table** (`|(N₃^{*g}, g)| ≤ C α^{3/2} X²`, Elgindi §8, tex 1484), in
the open-quadrant (primed) vocabulary.

`N₃^{*g} = -2α V(Φ̃_*)·D_z g`, so the piece is a constant times the product `f·D_z g` of the
coefficient `f = V(Φ̃_*)` and the `D_z`-derivative of the perturbation.

* the `ℋ⁴`-honesty conjunct is the primed product rule `N4Norm'.wprod` (multiplication by a
  `𝒲^{4,∞}`-function) applied to the coefficient `f = V(Φ̃_*)` — whose `𝒲^{4,∞}`-membership is
  the `VW`-clause of `StarPkgo2` and whose `C^∞`-regularity on the open quadrant follows from
  `StarPkgo.smooth` through `smoothOpen_PhiTs`/`smoothOpen_Vop` — and to `D_z g ∈ HQo α 4`
  (from `HkMem α 5 g` of `GalClass`), transported along the constant multiplication `-2α`;
* the pairing bound is the `D_z`-transport clause `N4Extra'.t3`, whose hypotheses
  (`SmoothOpen f`, `WlInfMem α 4 f`, `CoefThMem 3 f`, `RegQ α 4 g`, `HkMem α 5 g`,
  `DecayAll 4 g`) are exactly what `StarPkgo2` (`VW`, `Vth`), `smoothOpen_PhiTs`,
  `smoothOpen_Vop` and `GalClass` supply.  It gives
  `|(f·D_z g, g)| ≤ Ct α^{-1/2}(|f|_{𝒲} + CoefTh 3 f) X²`, and the two coefficient norms are
  both `≤ Cs·α`, so `2α · Ct α^{-1/2} · 2Csα = 4·Ct·Cs·α^{3/2}`, exactly the stated rate.

The sign of `Cs` is absorbed by replacing it with `max Cs 1`, and the elliptic package `EllPkgGo`
is not needed. -/
theorem Row18 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N3sg α Φs g) ∧
      |IP α (Work.FTS.Nonlin.N3sg α Φs g) g| ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  have hCt : 0 < Ct := hE.pos.1
  refine ⟨4 * Ct * max Cs 1 + 1, by positivity, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hs2 hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hCs1 : 0 ≤ max Cs 1 := le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1))
  -- the frozen star package and the coefficient `f = V(Φ̃_*)`
  have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
  have hfsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Vop
      (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs)
  have hfWmem : Work.Spaces.WlInfMem α 4
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) := hs2.VW.1
  have hfWle : Work.Spaces.WlInf α 4
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) ≤ max Cs 1 * α :=
    le_trans hs2.VW.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)
  have hfΔmem : Work.FTS.VocabO.CoefThMem 3
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) := hs.Vth.1
  have hfΔle : Work.FTS.VocabO.CoefTh 3
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) ≤ max Cs 1 * α :=
    le_trans hs.Vth.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)
  -- the `g`-side
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hsmQ : Work.FTS.LocData.SmoothQuad g := hreg4.1
  have hmem5 : Work.Spaces.HkMem α 5 g := Work.FTS.OpenPkg.galClass_HkMem5 hgal
  have hDzMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.CoercivityFix.QuadPorts.HkMem_Dz_quad α 4 hsmQ hmem5
  have hDzSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) :=
    (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hsmQ).Dz
  -- the product `V(Φ̃_*)·D_z g` is in `ℋ⁴` (this is also the honesty of the first argument of `IP`)
  have hprod : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.Dz g z θ) :=
    (hN.wprod α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) (Work.Spaces.Dz g)
      hfsm hfWmem ⟨hDzSm, hDzMem⟩).1
  -- `N₃^{*g}` is `-2α` times that product
  have hN3 : Work.FTS.Nonlin.N3sg α Φs g
      = fun z θ => (-2 * α) * (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * Work.Spaces.Dz g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N3sg]
    ring
  constructor
  · rw [hN3]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-2 * α) hprod
  · have hIPeq : IP α (Work.FTS.Nonlin.N3sg α Φs g) g
        = (-2 * α) * IP α (fun z θ => Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
            * Work.Spaces.Dz g z θ) g := by
      rw [hN3]
      exact hE.smul α hIoc (-2 * α) _ g hprod hreg4
    rw [hIPeq]
    have habs : |(-2 : ℝ) * α| = 2 * α := by
      rw [abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]
      ring
    rw [abs_mul, habs]
    -- the `D_z`-transport estimate for the coefficient `V(Φ̃_*)`
    have ht3 := hE.t3 α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) g
      hfsm hfWmem hfΔmem hreg4 hmem5 (Work.FTS.OpenPkg.galClass_DecayAll4 hgal)
    refine (mul_le_mul_of_nonneg_left ht3 (by linarith : (0 : ℝ) ≤ 2 * α)).trans ?_
    -- the weighted sum of the two coefficient norms is `≤ 2 Cs α`
    have hWsum : Work.Spaces.WlInf α 4
          (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
        + Work.FTS.VocabO.CoefTh 3 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
        ≤ 2 * (max Cs 1 * α) := by
      linarith
    have hstep : Ct * α ^ (-(1 / 2 : ℝ))
          * (Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
            + Work.FTS.VocabO.CoefTh 3 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)))
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
      have hpre : (0 : ℝ) ≤ Ct * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCt.le hA0
      have hX2 : 0 ≤ Work.FTS.Nonlin.Xn α g ^ 2 := pow_nonneg hX0 2
      calc Ct * α ^ (-(1 / 2 : ℝ))
            * (Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
              + Work.FTS.VocabO.CoefTh 3 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)))
            * Work.FTS.Nonlin.Xn α g ^ 2
          = (Ct * α ^ (-(1 / 2 : ℝ))
              * (Work.Spaces.WlInf α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))
                + Work.FTS.VocabO.CoefTh 3
                    (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))))
            * Work.FTS.Nonlin.Xn α g ^ 2 := by ring
        _ ≤ (Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α))) * Work.FTS.Nonlin.Xn α g ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWsum hpre) hX2
        _ = Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
            ring
    refine (mul_le_mul_of_nonneg_left hstep (by linarith : (0 : ℝ) ≤ 2 * α)).trans ?_
    -- `α · α^{-1/2} · α = α^{3/2}`
    have hpow : α * α ^ (-(1 / 2 : ℝ)) * α = α ^ (3 / 2 : ℝ) := by
      have h1 := Real.rpow_add hα (1 : ℝ) (1 / 2 : ℝ)
      rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, Real.rpow_one] at h1
      have h2 := Real.rpow_add hα (1 : ℝ) (-(1 / 2 : ℝ))
      rw [show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num, Real.rpow_one] at h2
      rw [h1, h2]
      ring
    have harith : 2 * α * (Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Cs 1 * α))
          * Work.FTS.Nonlin.Xn α g ^ 2)
        = 4 * Ct * max Cs 1 * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2) := by
      rw [← hpow]
      ring
    rw [harith]
    have h32 : 0 ≤ α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (pow_nonneg hX0 2)
    have hcs : 0 ≤ 4 * Ct * max Cs 1 := by positivity
    nlinarith [mul_nonneg hcs h32]

end Work.FTS.Nonlinear.Open
