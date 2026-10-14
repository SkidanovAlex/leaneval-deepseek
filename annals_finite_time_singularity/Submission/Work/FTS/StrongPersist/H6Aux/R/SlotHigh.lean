import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.CoercivityFix.Transfer.L4Step
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.StrongEps.exists_limG
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotData
import Submission.Work.FTS.TransportS.T2Sup.srestBound
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.level4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rowsN0T =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `E4R3/N4C/rowsN0T` — the `N₀`-block of the honest §8 table over the class-`C` context

`N0Rows IP α K g Φs Φg` (rows 1--7 of design §3.4) over the honest context `CtxT`, from the two
interfaces `N4Norm'`, `N4ExtraH`.

The seven rows are the honest (open-quadrant) twins of `Work.FTS.NonlinRows.NRow1_7`, proved in
the sibling modules of this directory:

* rows 2--7 in `Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row{2..7}u` (uniform in the package
  constants `Cs`, `Ce`, which the target quantifies *after* the `∃ K`);
* row 1 is unconditional: `Work.FTS.Nonlinear.Pieces.RowsN0Aux.N0fix_bound`.

The passage from `CtxT` to the hypothesis list of each row is elementary: `ClassC` supplies
`SmoothOpen g`, `HkMem α k g` (`k ≤ 7`) and `L12 g 0 = 0`, and `decayAll_of_classC` supplies the
`L¹`-decay `DecayAll 4 g` used by the `ℋ⁴`-transport clauses of `N4ExtraH`; the two elliptic
packages are the `StarPkgo2`/`EllPkgGo` fields of the context itself.
-/

theorem rowsN0T (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlinear.Pieces.N0Rows IP α K g Φs Φg := by
  obtain ⟨K1, hK1, h1⟩ := Work.FTS.Nonlinear.Pieces.RowsN0Aux.N0fix_bound
  obtain ⟨K2, hK2, h2⟩ := HonRowsU.n0row2u IP hN hE
  obtain ⟨K3, hK3, h3⟩ := HonRowsU.n0row3u IP hN hE
  obtain ⟨K4, hK4, h4⟩ := HonRowsU.n0row4u IP hN hE
  obtain ⟨K5, hK5, h5⟩ := HonRowsU.n0row5u IP hN hE
  obtain ⟨K6, hK6, h6⟩ := HonRowsU.n0row6u IP hN hE
  obtain ⟨K7, hK7, h7⟩ := HonRowsU.n0row7u IP hN hE
  refine ⟨K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1, by linarith, ?_⟩
  intro Cs Ce α g Φs Φg hctx
  have hK1' : K1 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK2' : K2 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK3' : K3 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK4' : K4 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK5' : K5 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK6' : K6 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK7' : K7 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hα0 : (0 : ℝ) ≤ α := hctx.hα.le
  have hsp : (0 : ℝ) ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hA1 : (0 : ℝ) ≤ α ^ (-(1 : ℝ)) := Real.rpow_nonneg hα0 _
  have hA3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have hA2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have hsm : Work.FTS.EllipticEst.SmoothOpen g := hctx.hg.reg
  have hm4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hctx.hg.reg 4 (by norm_num) hctx.hg.mem
  have hm5 : Work.Spaces.HkMem α 5 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hctx.hg.reg 5 (by norm_num) hctx.hg.mem
  have hl12 : Work.Construction.L12 g 0 = 0 := hctx.hg.l12
  have hdec : Work.Spaces.DecayAll 4 g := decayAll_of_classC hctx.hα hctx.hg hctx.hco
  obtain ⟨-, hr2⟩ := h2 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  obtain ⟨-, hr3⟩ := h3 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  obtain ⟨-, hr4⟩ := h4 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  obtain ⟨-, hr5⟩ := h5 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  obtain ⟨-, hr6⟩ := h6 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  obtain ⟨-, hr7⟩ := h7 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  exact
    { r1 := le_trans (h1 α hctx.hα hctx.hα1)
        (mul_le_mul_of_nonneg_right hK1' (sq_nonneg α))
      r2 := le_trans hr2
        (mul_le_mul_of_nonneg_right hK2' (mul_nonneg hA1 (pow_nonneg hX 2)))
      r3 := le_trans hr3
        (mul_le_mul_of_nonneg_right hK3' (mul_nonneg hsp hX))
      r4 := le_trans hr4
        (mul_le_mul_of_nonneg_right hK4' (mul_nonneg hA3 (pow_nonneg hX 3)))
      r5 := le_trans hr5
        (mul_le_mul_of_nonneg_right hK5' (mul_nonneg hsp hX))
      r6 := le_trans hr6
        (mul_le_mul_of_nonneg_right hK6' (mul_nonneg hA2 (pow_nonneg hX 3)))
      r7 := le_trans hr7
        (mul_le_mul_of_nonneg_right hK7' (mul_nonneg hsp (pow_nonneg hX 2))) }

end Work.FTS.StrongEps.E4R3.N4C
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.SlotHigh =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The a.e. hypothesis `(z,θ) ∈ Qd` (the open quadrant `(0,∞) × (0,π/2)`) of
`LhatCommOpen`. -/
theorem ae_mem_Qd :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (p.1, p.2) ∈ Work.Construction.Qd := by
  filter_upwards [ae_angle_Ioo, ae_radius_pos] with p hθ hz
  rw [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨hz, hθ.1, hθ.2⟩

/-- A nonnegative weight is a.e. nonnegative on the quadrant. -/
theorem ae_Rhoq_nonneg (β : ℝ) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 ≤ Rhoq β p.1 p.2 := by
  filter_upwards [ae_snd_mem_Iθ] with p hθ
  exact Work.FTS.CoercivityFix.Coer1.Rho_nonneg β p.1 p.2 hθ

/-- **The `D_z`-slot of `base_R`.** -/
theorem SlotOne (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) {h : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α 2 h) :
    -(4 : ℝ) * Work.Spaces.HkSq α 1 h
      ≤ Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.Spaces.Dz
          (Work.FTS.CoercivityFix.Lhat h)) (Work.Spaces.Dz h) := by
  have hm1 : Work.Spaces.HkMem α 1 h := Work.FTS.IPGen.HkMem_mono_le hs 1 (by norm_num) hm
  -- ### the pointwise block bounds
  have hbDz1 : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dz h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 1 h p.1 p.2 := by
    filter_upwards [sq_dz_le_Hk (h := h) (k := 1) α 1 (by norm_num)] with p hp
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.mixed] using hp
  have hbDz2 : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dz h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 := by
    filter_upwards [sq_dz_le_Hk (h := h) (k := 2) α 1 (by norm_num)] with p hp
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.mixed] using hp
  have hbDz2' : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.DzIter 2 h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 :=
    sq_dz_le_Hk (h := h) (k := 2) α 2 (by norm_num)
  have hbTDz : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dth (Work.Spaces.Dz h) p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 :=
    sq_DthDz_le_Hk (h := h) (k := 2) α hα0 hs (by norm_num)
  have hbE1 : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.FTS.CoercivityFix.E2hat h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ (2 : ℝ) * Work.Spaces.HkIntegrand α 2 h p.1 p.2 :=
    sq_E2_le_Hk (h := h) (k := 2) α hα0 (by norm_num)
  have hbE1' : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.FTS.CoercivityFix.E2hat h p.1 p.2) ^ 2 * Rhoq Work.Spaces.eta p.1 p.2
        ≤ (2 : ℝ) * Work.Spaces.HkIntegrand α 1 h p.1 p.2 :=
    sq_E2_le_Hk (h := h) (k := 1) α hα0 (by norm_num)
  -- ### the corresponding integrability facts
  have hUz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dz h z θ) ^ 2
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_sq_of_bound α 1 hs hm1 (C := 1) (by norm_num)
      (hs.Dz.continuousOn) (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _)
      (by filter_upwards [hbDz1] with p hp; simpa using hp)
  have hUzS : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz h z θ * Work.Spaces.Dz h z θ
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_sq_to_mul hUz
  have hEz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter 2 h z θ) ^ 2
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_sq_of_bound α 2 hs hm (C := 1) (by norm_num)
      ((hs.DzIter 2).continuousOn) (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _)
      (by filter_upwards [hbDz2'] with p hp; simpa using hp)
  have hEz2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth (Work.Spaces.Dz h) z θ) ^ 2
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_sq_of_bound α 2 hs hm (C := 1) (by norm_num)
      (continuousOn_Dth_Q0 hs.Dz) (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _)
      (by filter_upwards [hbTDz] with p hp; simpa using hp)
  have hE2z : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.FTS.CoercivityFix.E2hat h z θ) ^ 2
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_sq_of_bound α 2 hs hm (C := 2) (by norm_num)
      (continuousOn_E2hat_Q0 hs) (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _) hbE1
  have hEzS : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.DzIter 2 h z θ * Work.Spaces.Dz h z θ
        * Rhoq Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 1) (Cv := 1) (by norm_num) (by norm_num)
      ((hs.DzIter 2).continuousOn) (hs.Dz.continuousOn) (continuousOn_Rhoq_Q0 _)
      (ae_Rhoq_nonneg _)
      (by filter_upwards [hbDz2'] with p hp; simpa using hp)
      (by filter_upwards [hbDz2] with p hp; simpa using hp)
  have hEz2S : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dz h) z θ
        * Work.Spaces.Dz h z θ * Rhoq Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 1) (Cv := 1) (by norm_num) (by norm_num)
      (continuousOn_Dth_Q0 hs.Dz) (hs.Dz.continuousOn) (continuousOn_Rhoq_Q0 _)
      (ae_Rhoq_nonneg _)
      (by filter_upwards [hbTDz] with p hp; simpa using hp)
      (by filter_upwards [hbDz2] with p hp; simpa using hp)
  have hE2zS : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat h z θ
        * Work.FTS.CoercivityFix.E2hat h z θ * Rhoq Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_sq_to_mul hE2z
  -- ### the slot norm
  have hNz : Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.Spaces.Dz h)
      (Work.Spaces.Dz h) ≤ Work.Spaces.HkSq α 1 h :=
    wip_self_le_HkSq α 1 hs hm1 hUz hbDz1
  -- ### the two integrability facts for `wip_add`
  have hLz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
        * Work.Spaces.Dz h z θ * Rhoq Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 60) (Cv := 1) (by norm_num) (by norm_num)
      (continuousOn_Lhat_Q0 hs.Dz) (hs.Dz.continuousOn) (continuousOn_Rhoq_Q0 _)
      (ae_Rhoq_nonneg _)
      (sq_LhatDz_le_Hk (h := h) (k := 2) α hα0 hs (by norm_num))
      (by filter_upwards [hbDz2] with p hp; simpa using hp)
  have hDz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat h z θ
        * Work.Spaces.Dz h z θ * Rhoq Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 2) (Cv := 1) (by norm_num) (by norm_num)
      (continuousOn_E2hat_Q0 hs) (hs.Dz.continuousOn) (continuousOn_Rhoq_Q0 _)
      (ae_Rhoq_nonneg _) hbE1
      (by filter_upwards [hbDz2] with p hp; simpa using hp)
  -- ### the commutator identity
  have hcomm : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat h) p.1 p.2
        = (fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
            + Work.FTS.CoercivityFix.E2hat h z θ) p.1 p.2 := by
    filter_upwards [ae_mem_Qd] with p hp
    exact (LhatCommOpen hs).2 p.1 p.2 hp
  rw [wip_congr_fst_ae (ρ := Rhoq Work.Spaces.eta)
      (A := Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat h))
      (B := fun z θ => Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
        + Work.FTS.CoercivityFix.E2hat h z θ) (g := Work.Spaces.Dz h) hcomm]
  rw [Work.Coercivity.wip_add _ _ _ _ hLz hDz]
  -- ### the defect bound via Cauchy–Schwarz
  have hdef : -(3 / 2) * Work.Spaces.HkSq α 1 h
      ≤ Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.FTS.CoercivityFix.E2hat h)
          (Work.Spaces.Dz h) := by
    have h1 : Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.FTS.CoercivityFix.E2hat h)
        (Work.FTS.CoercivityFix.E2hat h) ≤ 2 * Work.Spaces.HkSq α 1 h :=
      wip_self_le_mul_HkSq α 1 hs hm1 (C := 2) (by norm_num) hE2zS
        (by filter_upwards [hbE1'] with p hp; simpa only [sq] using hp)
    have h2 := Work.FTS.CoercivityFix.DzSelf.wip_abs_le_half
      (ρ := Rhoq Work.Spaces.eta) (ρ' := Rhoq Work.Spaces.eta)
      (u := Work.FTS.CoercivityFix.E2hat h) (v := Work.Spaces.Dz h)
      (ae_Rhoq_nonneg _) (Filter.Eventually.of_forall fun p => le_rfl) hE2zS hUzS hDz
    have h3 : -|Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.FTS.CoercivityFix.E2hat h)
        (Work.Spaces.Dz h)| ≤ Work.Coercivity.wip (Rhoq Work.Spaces.eta)
          (Work.FTS.CoercivityFix.E2hat h) (Work.Spaces.Dz h) := neg_abs_le _
    linarith [h1, h2, h3, hNz]
  -- ### the main bound
  have hmain : -(5 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
      ≤ Work.Coercivity.wip (Rhoq Work.Spaces.eta)
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h)) (Work.Spaces.Dz h) :=
    WipLhatGe (u := Work.Spaces.Dz h) (q := Work.Spaces.eta) hs.Dz
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)
      hEzS hEz2S hUzS
  have hUne : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz h z θ) ^ 2 * Rhoq Work.Spaces.eta z θ)
      = Work.Coercivity.wip (Rhoq Work.Spaces.eta) (Work.Spaces.Dz h)
          (Work.Spaces.Dz h) := (wip_self_eq _ _).symm
  rw [hUne] at hmain
  have hE0 : 0 ≤ Work.Spaces.HkSq α 1 h := Work.Spaces.HkSq_nonneg α 1 h
  linarith [hmain, hdef, hNz, hE0]

/-- **The `D_θ`-slot of `base_R`.** -/
theorem SlotFour (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) {h : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen h) (hm : Work.Spaces.HkMem α 2 h) :
    -(3 : ℝ) * Work.Spaces.HkSq α 1 h
      ≤ Work.Coercivity.wip (Rhoq (Work.Spaces.gam α)) (Work.Spaces.Dth
          (Work.FTS.CoercivityFix.Lhat h)) (Work.Spaces.Dth h) := by
  have hm1 : Work.Spaces.HkMem α 1 h := Work.FTS.IPGen.HkMem_mono_le hs 1 (by norm_num) hm
  have hγ0 : (0 : ℝ) ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  -- ### the pointwise block bounds
  have hbDth1 : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dth h p.1 p.2) ^ 2 * Rhoq (Work.Spaces.gam α) p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 1 h p.1 p.2 :=
    sq_mixed_le_Hk_gam (h := h) (k := 1) (j := 0) (i := 1) α hα0 (by norm_num) (by norm_num)
  have hbDth2 : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dth h p.1 p.2) ^ 2 * Rhoq (Work.Spaces.gam α) p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 :=
    sq_mixed_le_Hk_gam (h := h) (k := 2) (j := 0) (i := 1) α hα0 (by norm_num) (by norm_num)
  have hbZ : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dz (Work.Spaces.Dth h) p.1 p.2) ^ 2 * Rhoq (Work.Spaces.gam α) p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 := by
    filter_upwards [sq_mixed_le_Hk_gam (h := h) (k := 2) (j := 1) (i := 1) α hα0
      (by norm_num) (by norm_num)] with p hp
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.mixed] using hp
  have hbT : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.Dth (Work.Spaces.Dth h) p.1 p.2) ^ 2 * Rhoq (Work.Spaces.gam α) p.1 p.2
        ≤ Work.Spaces.HkIntegrand α 2 h p.1 p.2 := by
    filter_upwards [sq_mixed_le_Hk_gam (h := h) (k := 2) (j := 0) (i := 2) α hα0
      (by norm_num) (by norm_num)] with p hp
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.mixed] using hp
  -- ### integrability
  have hUt : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth h z θ) ^ 2
        * Rhoq (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_sq_of_bound α 1 hs hm1 (C := 1) (by norm_num)
      (hs.Dth.continuousOn) (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _)
      (by filter_upwards [hbDth1] with p hp; simpa using hp)
  have hZt : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz (Work.Spaces.Dth h) z θ
        * Work.Spaces.Dth h z θ * Rhoq (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 1) (Cv := 1) (by norm_num) (by norm_num)
      (((hs.Dth).Dz).continuousOn) (hs.Dth.continuousOn)
      (continuousOn_Rhoq_Q0 _) (ae_Rhoq_nonneg _)
      (by filter_upwards [hbZ] with p hp; simpa using hp)
      (by filter_upwards [hbDth2] with p hp; simpa using hp)
  have hTt : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.Dth h) z θ
        * Work.Spaces.Dth h z θ * Rhoq (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrable_mul_of_sq α 2 hs hm (Cu := 1) (Cv := 1) (by norm_num) (by norm_num)
      (continuousOn_Dth_Q0 hs.Dth) (hs.Dth.continuousOn) (continuousOn_Rhoq_Q0 _)
      (ae_Rhoq_nonneg _)
      (by filter_upwards [hbT] with p hp; simpa using hp)
      (by filter_upwards [hbDth2] with p hp; simpa using hp)
  -- ### the slot norm
  have hUtS : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth h z θ * Work.Spaces.Dth h z θ
        * Rhoq (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_sq_to_mul hUt
  have hNt : Work.Coercivity.wip (Rhoq (Work.Spaces.gam α)) (Work.Spaces.Dth h)
      (Work.Spaces.Dth h) ≤ Work.Spaces.HkSq α 1 h :=
    wip_self_le_HkSq α 1 hs hm1 hUt hbDth1
  -- ### the commutator identity and the main bound
  have hcomm : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat h) p.1 p.2
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h) p.1 p.2 := by
    filter_upwards [ae_mem_Qd] with p hp
    exact (LhatCommOpen hs).1 p.1 p.2 hp
  rw [wip_congr_fst_ae (ρ := Rhoq (Work.Spaces.gam α))
      (A := Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat h))
      (B := Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h))
      (g := Work.Spaces.Dth h) hcomm]
  have hmain : -(5 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dth h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ)
      ≤ Work.Coercivity.wip (Rhoq (Work.Spaces.gam α))
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h)) (Work.Spaces.Dth h) :=
    WipLhatGe (u := Work.Spaces.Dth h) (q := Work.Spaces.gam α) hs.Dth hγ0 hγ2 hZt hTt hUtS
  have hUne : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dth h z θ) ^ 2 * Rhoq (Work.Spaces.gam α) z θ)
      = Work.Coercivity.wip (Rhoq (Work.Spaces.gam α)) (Work.Spaces.Dth h)
          (Work.Spaces.Dth h) := (wip_self_eq _ _).symm
  rw [hUne] at hmain
  have hE0 : 0 ≤ Work.Spaces.HkSq α 1 h := Work.Spaces.HkSq_nonneg α 1 h
  linarith [hmain, hNt, hE0]

end Work.FTS.StrongPersist.H6Aux.R
end
end
