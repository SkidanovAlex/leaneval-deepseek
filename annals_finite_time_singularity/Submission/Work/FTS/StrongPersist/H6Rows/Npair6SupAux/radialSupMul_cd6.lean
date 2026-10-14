import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.HkNorm_Dz_le_open
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstTendsto
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.HonestHardSlotLem
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgBasic
import Submission.Work.FTS_EllLimOK.ThetaJets.ClassC_le
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXA1.abs_mixed_le_HkNorm_C4_proved
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.H2W.weakSliceZContinuousAe
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.ClassC.vthQuarter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The angular Poincaré estimate for the straightened unknown with the range `α ≤ 1/4`
explicit** (the `∀`-form of `VthAuxC.poinC`, whose statement returns an existential `α₀`; the
witness there is `1/4`, but Lean cannot see that through the opaque `∃`). -/
theorem poinC_quarter : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      ClassC α g → Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
        (ellShift α g Φg) →
      Work.Spaces.HkMem α 4 (ellShift α g Φg) ∧
      Work.Spaces.HkMem α 4 (Work.Spaces.pth (ellShift α g Φg)) ∧
      Work.Spaces.HkNorm α 4 (ellShift α g Φg)
        ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (ellShift α g Φg)) ∧
      Work.Spaces.HkNorm α 4 (Work.Spaces.pth (ellShift α g Φg))
        ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (ellShift α g Φg)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllSol.ropPoincareAe
  refine ⟨C, hCpos, ?_⟩
  intro α g Φg hα hα4 _hcls _hsol _hsm hW
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨htr3, htr4⟩ := VthAuxC.pc_traces (α := α) (F := Work.Elliptic.orthSource g)
    (Ψ := ellShift α g Φg) hα hα4 hW
  have hvan : Work.Spaces.VanishTheta (ellShift α g Φg) := ⟨hW.zero, hW.pi_half⟩
  exact hC α (ellShift α g Φg) hα hα1 hW.smooth htr3 htr4
    (fun j _hj z _hz => ⟨VthAuxC.pc_dzIter_value_zero hvan j z,
      VthAuxC.pc_dzIter_value_pi_half hvan j z⟩) hW.memB

/-- **The `V^{th}` slot from its three analytic inputs, with the `α`-range `1/4` explicit.**

A copy of `Work.FTS.EllSol.VthAuxC.ellVth_transferC_of_pieces` in which the angular Poincaré
input is taken in its `∀`-form for `α ≤ 1/4` (so that the returned constant needs no existential
`α₀`), so that the slot is obtained for the whole range `α ∈ (0, 1/4]` demanded by
`Work.FTS.ClassC.VthSlot`.  Everything else is verbatim. -/
theorem ellVth_transferC_of_pieces_quarter
    (hE : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C)
    (hCert : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 → ClassC α g →
      Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) ∧
      Work.Spaces.HkMem α 4 (Work.Elliptic.orthSource g) ∧
      Work.Spaces.HkNorm α 4 (Work.Elliptic.orthSource g) ≤ C * Work.Spaces.HkNorm α 4 g ∧
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) ∧
      Work.Spaces.HkMem α 4 (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) ∧
      Work.Spaces.HkNorm α 4 (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α 4 g)
    (hPoin : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g Φg : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 / 4 → ClassC α g → Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
        (ellShift α g Φg) →
      Work.Spaces.HkMem α 4 (ellShift α g Φg) ∧
      Work.Spaces.HkMem α 4 (Work.Spaces.pth (ellShift α g Φg)) ∧
      Work.Spaces.HkNorm α 4 (ellShift α g Φg)
        ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (ellShift α g Φg)) ∧
      Work.Spaces.HkNorm α 4 (Work.Spaces.pth (ellShift α g Φg))
        ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (ellShift α g Φg))) :
    ∃ Ce : ℝ, 0 < Ce ∧
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg → Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g) (ellShift α g Φg) →
    Work.FTS.VocabO.CoefThMem 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
    Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
      ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g := by
  obtain ⟨C1, hC1pos, hE'⟩ := hE
  obtain ⟨C2, hC2pos, hCert'⟩ := hCert
  obtain ⟨C3, hC3pos, hPoin'⟩ := hPoin
  obtain ⟨CS, hCSpos, hS'⟩ := VthAux.mixedSlot_sup_le_hk_open
  obtain ⟨C4, hC4pos, hDz'⟩ := Work.FTS.EllipticEst.HkNorm_Dz_le_open 4
  refine ⟨4 * (CS * Real.sqrt 10
      * (32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
          + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2))))),
    by positivity, ?_⟩
  intro α g Φg hα hαm hg hsol hsmΦ hweak
  have hα4 : α ≤ 1 / 4 := hαm
  have hα1 : α ≤ 1 := by linarith
  have hαnn : 0 ≤ α := le_of_lt hα
  let F : ℝ → ℝ → ℝ := Work.Elliptic.orthSource g
  let W : ℝ → ℝ → ℝ := ellShift α g Φg
  let GB : ℝ → ℝ → ℝ := fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)
  let GBm : ℝ → ℝ → ℝ := fun z θ => -(Work.Elliptic.Gbar α g z) * Real.sin (2 * θ)
  let A : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 W z θ
  let DZ : ℝ → ℝ → ℝ := Work.Spaces.Dz W
  let V : ℝ → ℝ → ℝ := Work.Construction.Vop (Work.Construction.PhiTil α g Φg)
  let K : ℝ := Work.Spaces.HkNorm α 4 g
  have hKnn : 0 ≤ K := Work.Spaces.HkNorm_nonneg α 4 g
  obtain ⟨hFsm, hFmem, hFle, hGBsm, hGBmem, hGBle⟩ := hCert' α g hα hα1 hg
  have hEll := hE' α F W hα hα4 hweak
  have hAle : α ^ 2 * Work.Spaces.HkNorm α 4 A ≤ C1 * (C2 * K) := by
    have h1 : α ^ 2 * Work.Spaces.HkNorm α 4 A ≤ C1 * Work.Spaces.HkNorm α 4 F := by
      linarith [hEll, Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.pthIter 2 W)]
    calc α ^ 2 * Work.Spaces.HkNorm α 4 A ≤ C1 * Work.Spaces.HkNorm α 4 F := h1
      _ ≤ C1 * (C2 * K) := mul_le_mul_of_nonneg_left hFle (le_of_lt hC1pos)
  have hBle : Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 W) ≤ C1 * (C2 * K) := by
    have h1 : Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 W)
        ≤ C1 * Work.Spaces.HkNorm α 4 F := by
      linarith [hEll, mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α 4 A)]
    calc Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 W) ≤ C1 * Work.Spaces.HkNorm α 4 F := h1
      _ ≤ C1 * (C2 * K) := mul_le_mul_of_nonneg_left hFle (le_of_lt hC1pos)
  obtain ⟨hWmem, hWpmem, hWle, hWple⟩ := hPoin' α g Φg hα hα4 hg hsol hsmΦ hweak
  have hWle' : Work.Spaces.HkNorm α 4 W ≤ C3 * (C1 * (C2 * K)) :=
    le_trans hWle (mul_le_mul_of_nonneg_left hBle (le_of_lt hC3pos))
  have hSmW : Work.FTS.EllipticEst.SmoothOpen W :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hweak.smooth
  have hSmA : Work.FTS.EllipticEst.SmoothOpen A :=
    Work.FTS.EllipticEst.SmoothOpen.zsq_mul (hSmW.pz.pz)
  have hSmGBm : Work.FTS.EllipticEst.SmoothOpen GBm := by
    have h1 := Work.FTS.EllipticEst.SmoothOpen.const_mul' (-1) hGBsm
    exact Work.FTS.EllipticEst.SmoothOpen.congr h1 (fun z θ _ _ _ => by
      simp only [GBm, GB]; ring)
  have hGBmmem : Work.Spaces.HkMem α 4 GBm := by
    have h1 : Work.Spaces.HkMem α 4 ((-1 : ℝ) • GB) :=
      Work.FTS.EllipticEst.HkMem_smul (by norm_num) α 4 hGBmem
    refine Work.FTS.EllipticEst.HkMem_agreeOnQ hSmGBm (fun z θ _ _ _ => ?_) h1
    simp only [GBm, GB, Pi.smul_apply, smul_eq_mul]
    ring
  have hGBm_norm : Work.Spaces.HkNorm α 4 GBm = Work.Spaces.HkNorm α 4 GB := by
    have h1 : GBm = - GB := by
      funext z θ
      simp only [GBm, GB, Pi.neg_apply]
      ring
    rw [h1, Work.FTS.EllipticEst.HkNorm_neg]
  have hDZ := hDz' α W hα hα1 hSmW.forall hWmem (Work.FTS.EllipticEst.TT.EllWeakPos.memA hweak)
  obtain ⟨hDZmem, hDZbnd⟩ := hDZ
  have hDZle : (α * (5 + α)) * Work.Spaces.HkNorm α 4 DZ
      ≤ 6 * (C4 * (C3 * (C1 * (C2 * K)) + C1 * (C2 * K))) := by
    have h1 : α * Work.Spaces.HkNorm α 4 DZ
        ≤ C4 * (Work.Spaces.HkNorm α 4 W + α ^ 2 * Work.Spaces.HkNorm α 4 A) := hDZbnd
    have h2 : Work.Spaces.HkNorm α 4 W + α ^ 2 * Work.Spaces.HkNorm α 4 A
        ≤ C3 * (C1 * (C2 * K)) + C1 * (C2 * K) := add_le_add hWle' hAle
    have h3 : α * Work.Spaces.HkNorm α 4 DZ
        ≤ C4 * (C3 * (C1 * (C2 * K)) + C1 * (C2 * K)) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt hC4pos))
    calc (α * (5 + α)) * Work.Spaces.HkNorm α 4 DZ
        = (5 + α) * (α * Work.Spaces.HkNorm α 4 DZ) := by ring
      _ ≤ 6 * (α * Work.Spaces.HkNorm α 4 DZ) := by
          refine mul_le_mul_of_nonneg_right ?_
            (mul_nonneg hαnn (Work.Spaces.HkNorm_nonneg α 4 DZ))
          linarith
      _ ≤ 6 * (C4 * (C3 * (C1 * (C2 * K)) + C1 * (C2 * K))) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
  have hSm6W : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 6 * W z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' 6 hSmW
  have hSm6GBm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 6 * GBm z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' 6 hSmGBm
  have hSmA2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α ^ 2 * A z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' (α ^ 2) hSmA
  have hSmDZ2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (α * (5 + α)) * DZ z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' (α * (5 + α)) hSmW.Dz
  have hSmF6W : Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ + 6 * W z θ) :=
    vthC_smoothOpen_add hFsm hSm6W
  have hSmF6WGB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ) :=
    vthC_smoothOpen_add (vthC_smoothOpen_add hFsm hSm6W) hSm6GBm
  have hSmF6WGBA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ) :=
    vthC_smoothOpen_add (vthC_smoothOpen_add (vthC_smoothOpen_add hFsm hSm6W) hSm6GBm) hSmA2
  have hMem6W : Work.Spaces.HkMem α 4 (fun z θ => 6 * W z θ) :=
    Work.FTS.EllipticEst.HkMem_smul (by norm_num) α 4 hWmem
  have hMem6GBm : Work.Spaces.HkMem α 4 (fun z θ => 6 * GBm z θ) :=
    Work.FTS.EllipticEst.HkMem_smul (by norm_num) α 4 hGBmmem
  have hMemA2 : Work.Spaces.HkMem α 4 (fun z θ => α ^ 2 * A z θ) :=
    Work.FTS.EllipticEst.HkMem_smul (pow_ne_zero 2 (ne_of_gt hα)) α 4
      (Work.FTS.EllipticEst.TT.EllWeakPos.memA hweak)
  have hMemDZ2 : Work.Spaces.HkMem α 4 (fun z θ => (α * (5 + α)) * DZ z θ) :=
    Work.FTS.EllipticEst.HkMem_smul (ne_of_gt (by positivity : (0 : ℝ) < α * (5 + α))) α 4 hDZmem
  have hMemF6W : Work.Spaces.HkMem α 4 (fun z θ => F z θ + 6 * W z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hFsm hSm6W hFmem hMem6W
  have hMemF6WGB : Work.Spaces.HkMem α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open (vthC_smoothOpen_add hFsm hSm6W) hSm6GBm hMemF6W hMem6GBm
  have hMemF6WGBA : Work.Spaces.HkMem α 4
      (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open (vthC_smoothOpen_add (vthC_smoothOpen_add hFsm hSm6W)
      hSm6GBm) hSmA2 hMemF6WGB hMemA2
  have hn1 : Work.Spaces.HkNorm α 4 F ≤ C2 * K := hFle
  have hn2 : Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ) ≤ 6 * (C3 * (C1 * (C2 * K))) := by
    have h1 : Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)
        = |(6 : ℝ)| * Work.Spaces.HkNorm α 4 W :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 6 hSmW.forall
    rw [h1, show |(6 : ℝ)| = 6 by norm_num]
    exact mul_le_mul_of_nonneg_left hWle' (by norm_num)
  have hn3 : Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ) ≤ 6 * (C2 * K) := by
    have h1 : Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)
        = |(6 : ℝ)| * Work.Spaces.HkNorm α 4 GBm :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 6 hSmGBm.forall
    rw [h1, show |(6 : ℝ)| = 6 by norm_num, hGBm_norm]
    exact mul_le_mul_of_nonneg_left hGBle (by norm_num)
  have hn4 : Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ) ≤ C1 * (C2 * K) := by
    have h1 : Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)
        = |α ^ 2| * Work.Spaces.HkNorm α 4 A :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 (α ^ 2) hSmA.forall
    rw [h1, abs_of_nonneg (sq_nonneg α)]
    exact hAle
  have hn5 : Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)
      ≤ 6 * (C4 * (C3 * (C1 * (C2 * K)) + C1 * (C2 * K))) := by
    have h1 : Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)
        = |α * (5 + α)| * Work.Spaces.HkNorm α 4 DZ :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 4 (α * (5 + α)) hSmW.Dz.forall
    rw [h1, abs_of_nonneg (by positivity)]
    exact hDZle
  have hpoint : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      -(F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ + (α * (5 + α)) * DZ z θ)
        = Work.Spaces.pth V z θ := by
    intro z θ hz hθ0 hθ1
    exact (pth_Vop_PhiTil_eq α g Φg hweak hGBsm hz ⟨hθ0, hθ1⟩).symm
  let S5 : ℝ → ℝ → ℝ := fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ
    + (α * (5 + α)) * DZ z θ
  have hSmS5 : Work.FTS.EllipticEst.SmoothOpen S5 :=
    Work.FTS.EllipticEst.SmoothOpen.congr (vthC_smoothOpen_add hSmF6WGBA hSmDZ2)
      (fun z θ _ _ _ => by simp only [S5])
  have hMemS5 : Work.Spaces.HkMem α 4 S5 :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ hSmS5 (fun z θ _ _ _ => by
      simp only [S5])
      (Work.FTS.EllipticEst.HkMem_add_open hSmF6WGBA hSmDZ2 hMemF6WGBA hMemDZ2)
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have htri1 : Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ)
      ≤ 2 * (Work.Spaces.HkNorm α 4 F + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)) := by
    have h := Work.FTS.EllipticEst.HkNorm_add_le α 4 hFsm.forall hSm6W.forall hFmem hMem6W
    calc Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 F
            + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)) := h
      _ ≤ 2 * (Work.Spaces.HkNorm α 4 F
            + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)) := by
          refine mul_le_mul_of_nonneg_right hsqrt2 ?_
          exact add_nonneg (Work.Spaces.HkNorm_nonneg α 4 F)
            (Work.Spaces.HkNorm_nonneg α 4 _)
  have htri2 : Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ)
      ≤ 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)) := by
    have h := Work.FTS.EllipticEst.HkNorm_add_le α 4 hSmF6W.forall hSm6GBm.forall
      hMemF6W hMem6GBm
    calc Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)) := h
      _ ≤ 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)) := by
          refine mul_le_mul_of_nonneg_right hsqrt2 ?_
          exact add_nonneg (Work.Spaces.HkNorm_nonneg α 4 _) (Work.Spaces.HkNorm_nonneg α 4 _)
  have htri3 : Work.Spaces.HkNorm α 4
        (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
      ≤ 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)) := by
    have h := Work.FTS.EllipticEst.HkNorm_add_le α 4 hSmF6WGB.forall hSmA2.forall
      hMemF6WGB hMemA2
    calc Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)) := h
      _ ≤ 2 * (Work.Spaces.HkNorm α 4 (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)) := by
          refine mul_le_mul_of_nonneg_right hsqrt2 ?_
          exact add_nonneg (Work.Spaces.HkNorm_nonneg α 4 _) (Work.Spaces.HkNorm_nonneg α 4 _)
  have htri4 : Work.Spaces.HkNorm α 4 S5
      ≤ 2 * (Work.Spaces.HkNorm α 4
            (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)) := by
    have h := Work.FTS.EllipticEst.HkNorm_add_le α 4 hSmF6WGBA.forall hSmDZ2.forall
      hMemF6WGBA hMemDZ2
    have heq : S5 = fun z θ => (F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
        + (α * (5 + α)) * DZ z θ := rfl
    rw [heq]
    calc Work.Spaces.HkNorm α 4 (fun z θ => (F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
          + (α * (5 + α)) * DZ z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4
              (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)) := h
      _ ≤ 2 * (Work.Spaces.HkNorm α 4
              (fun z θ => F z θ + 6 * W z θ + 6 * GBm z θ + α ^ 2 * A z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)) := by
          refine mul_le_mul_of_nonneg_right hsqrt2 ?_
          exact add_nonneg (Work.Spaces.HkNorm_nonneg α 4 _) (Work.Spaces.HkNorm_nonneg α 4 _)
  have hVhd : Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)
      ≤ 32 * (Work.Spaces.HkNorm α 4 F + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)) := by
    have hsq : Work.Spaces.HkSq α 4 (Work.Spaces.pth V)
        = Work.Spaces.HkSq α 4 (fun z θ => -(S5 z θ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ0 hθ1 => by
        rw [hpoint z θ hz hθ0 hθ1])
    have hnorm : Work.Spaces.HkNorm α 4 (Work.Spaces.pth V) = Work.Spaces.HkNorm α 4 S5 := by
      have h2 : Work.Spaces.HkNorm α 4 (fun z θ => -(S5 z θ)) = Work.Spaces.HkNorm α 4 S5 := by
        have hneg : (fun z θ => -(S5 z θ)) = -S5 := by
          funext z θ; simp only [Pi.neg_apply]
        rw [hneg, Work.FTS.EllipticEst.HkNorm_neg]
      have h3 : Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)
          = Work.Spaces.HkNorm α 4 (fun z θ => -(S5 z θ)) := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsq]
      rw [h3, h2]
    rw [hnorm]
    have hnn1 : 0 ≤ Work.Spaces.HkNorm α 4 F := Work.Spaces.HkNorm_nonneg α 4 F
    have hnn2 : 0 ≤ Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have hnn3 : 0 ≤ Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have hnn4 : 0 ≤ Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    have hnn5 : 0 ≤ Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    linarith [htri1, htri2, htri3, htri4]
  have hVle : Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)
      ≤ (32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
          + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))) * K := by
    have hsum : Work.Spaces.HkNorm α 4 F + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)
          + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)
        ≤ (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2))) * K := by
      nlinarith [hn1, hn2, hn3, hn4, hn5, hKnn, le_of_lt hC1pos, le_of_lt hC2pos,
        le_of_lt hC3pos, le_of_lt hC4pos]
    calc Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)
        ≤ 32 * (Work.Spaces.HkNorm α 4 F + Work.Spaces.HkNorm α 4 (fun z θ => 6 * W z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => 6 * GBm z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => α ^ 2 * A z θ)
            + Work.Spaces.HkNorm α 4 (fun z θ => (α * (5 + α)) * DZ z θ)) := hVhd
      _ ≤ 32 * ((C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2))) * K) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))) * K := by ring
  have hSmΞ : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g Φg) := by
    have hdec : (fun z θ => ellShift α g Φg z θ
        + (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ))
        = Work.Construction.PhiTil α g Φg := by
      rw [Work.FTS.EllipticEst.PhiTil_eq_EllResid]
      exact (vthC_EllResid_eq_ellShift α g Φg).symm
    exact Work.FTS.EllipticEst.SmoothOpen.congr (vthC_smoothOpen_add hSmW hSmGBm)
      (fun z θ _ _ _ => by rw [← hdec])
  have hSmV : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth V) := by
    have hVeq : V = fun z θ => Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ
        - Real.tan θ * Work.Construction.PhiTil α g Φg z θ := by
      funext z θ; simp only [V, Work.Construction.Vop]
    rw [hVeq]
    exact (vthC_smoothOpen_sub hSmΞ.pth (vthC_smoothOpen_tan_mul hSmΞ)).pth
  have hMemV : Work.Spaces.HkMem α 4 (Work.Spaces.pth V) := by
    have h2 : Work.Spaces.HkMem α 4 ((-1 : ℝ) • S5) :=
      Work.FTS.EllipticEst.HkMem_smul (c := (-1 : ℝ)) (by norm_num) α 4 hMemS5
    refine Work.FTS.EllipticEst.HkMem_agreeOnQ (f := (-1 : ℝ) • S5) hSmV ?_ h2
    intro z θ hz hθ0 hθ1
    simpa only [Pi.smul_apply, smul_eq_mul, neg_one_mul, S5]
      using hpoint z θ hz hθ0 hθ1
  have hratio : 0 ≤ CS / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (le_of_lt hCSpos) (Real.sqrt_nonneg _)
  refine ⟨fun b i hbi => ⟨CS / Real.sqrt (Work.Spaces.gam α - 1)
      * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V),
      fun z θ hz hθ0 hθ1 => hS' α (Work.Spaces.pth V) b i hα hα1 (by omega) hSmV hMemV
        z θ hz hθ0 hθ1⟩, ?_⟩
  have hcoef : Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
      ≤ 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)) := by
    have h := Work.FTS.TransportS.coefTh_le_of_supAbsO_le (l := 1)
      (f := Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
      (K := CS / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V))
      (fun b i hbi => Work.FTS.H2.supAbsO_le
        (fun z θ hz hθ0 hθ1 => hS' α (Work.Spaces.pth V) b i hα hα1 (by omega) hSmV hMemV
          z θ hz hθ0 hθ1))
    have h4 : (((1 : ℕ) : ℝ) + 1) * (((1 : ℕ) : ℝ) + 1) = 4 := by norm_num
    calc _ ≤ (((1 : ℕ) : ℝ) + 1) * (((1 : ℕ) : ℝ) + 1)
          * (CS / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)) := h
      _ = 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
            * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)) := by rw [h4]
  have hstep : 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V))
      ≤ 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
        * ((32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))) * K)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVle hratio) (by norm_num)
  have hfin : 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
        * ((32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))) * K))
      = (4 * (CS * Real.sqrt 10 * (32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))))) * α ^ (-(1 / 2 : ℝ)) * K := by
    rw [show CS / Real.sqrt (Work.Spaces.gam α - 1)
          = CS * (1 / Real.sqrt (Work.Spaces.gam α - 1)) from by ring,
      vthC_inv_sqrt_gam_sub_one hα]
    ring
  calc Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
      ≤ 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 (Work.Spaces.pth V)) := hcoef
    _ ≤ 4 * (CS / Real.sqrt (Work.Spaces.gam α - 1)
          * ((32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
              + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))) * K)) := hstep
    _ = (4 * (CS * Real.sqrt 10 * (32 * (C2 + 6 * (C3 * (C1 * C2)) + 6 * C2 + C1 * C2
            + 6 * (C4 * (C3 * (C1 * C2) + C1 * C2)))))) * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.HkNorm α 4 g := by
        rw [hfin]

end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.interpFamOfTrace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-- **The family interpolation in the trace class.**  From the single-function trace-class
estimate `InterpOpenTraceStmt` one gets the `i = 0` family bound of `InterpFam k`: exactly
`i0Family_le_of_interpOpen` with the general `InterpOpen` replaced by the trace-class version and
the (unused) extra trace hypothesis carried along. -/
theorem interpFamOfTrace {C : ℝ} (hC : 0 < C)
    (hopen : InterpOpenTraceStmt C) (k : ℕ) : Work.FTS.EllSol.PkgK5.InterpFam k := by
  refine ⟨((k : ℝ) + 1) * C, by positivity, ?_⟩
  intro α V hα hα14 hsm h0 hpi htrace hdd htt hd
  set R : ℝ := α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
      + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
      + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) with hR
  have hRnn : 0 ≤ R := by
    rw [hR]
    have h1 := Work.Spaces.HkSq_nonneg α k (Work.Spaces.DzIter 2 V)
    have h2 := Work.Spaces.HkSq_nonneg α k (Work.Spaces.pthIter 2 V)
    have h3 := Work.Spaces.HkSq_nonneg α k (Work.Spaces.Dz V)
    have hα4 : (0 : ℝ) ≤ α ^ 4 := by positivity
    have hα2 : (0 : ℝ) ≤ α ^ 2 := by positivity
    nlinarith [mul_nonneg hα4 h1, mul_nonneg hα2 h3]
  have key : ∀ r ∈ Finset.range (k + 1),
      α ^ 2 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z) ≤ C * R := by
    intro r hr
    have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    by_cases hhon : MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        Work.Spaces.Iz
    · have hc := hopen α (Work.Spaces.DzIter r V) hα hα14 (hsm.DzIter r)
        (Work.EllipticEst.Core.i0Aux.DzIter_zero_theta h0 r)
        (Work.EllipticEst.Core.i0Aux.DzIter_pi_theta hpi r)
        (fun z hz => (htrace r (by omega) z hz).1)
        (fun z hz => (htrace r (by omega) z hz).2)
        (fun z hz => (htrace (r + 1) (by omega) z hz).1)
        (fun z hz => (htrace (r + 1) (by omega) z hz).2)
        (Work.EllipticEst.Core.i0Aux.sliceHonestOpen_dzIter hsm hdd htt hd hrk) hhon
        (Work.EllipticEst.Core.i0Aux.ddIntS_integrableOn hsm hdd hrk)
        (Work.EllipticEst.Core.i0Aux.ttIntS_integrableOn hsm htt hrk)
        (Work.EllipticEst.Core.i0Aux.dIntS_integrableOn hsm hd hrk)
      refine le_trans hc (mul_le_mul_of_nonneg_left ?_ hC.le)
      have h1 := Work.EllipticEst.Core.i0Aux.ddIntS_integral_le_HkSq (V := V) hdd hrk
      have h2 := Work.EllipticEst.Core.i0Aux.ttIntS_integral_le_HkSq (V := V) hsm htt hrk
      have h3 := Work.EllipticEst.Core.i0Aux.dIntS_integral_le_HkSq (V := V) hd hrk
      rw [hR]
      have hα4 : (0 : ℝ) ≤ α ^ 4 := by positivity
      have hα2 : (0 : ℝ) ≤ α ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 hα4, h2, mul_le_mul_of_nonneg_left h3 hα2]
    · rw [MeasureTheory.integral_undef hhon, mul_zero]
      exact mul_nonneg hC.le hRnn
  have hsum : (∑ r ∈ Finset.range (k + 1),
        α ^ 2 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
      ≤ ((k : ℝ) + 1) * (C * R) := by
    calc (∑ r ∈ Finset.range (k + 1),
          α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
        ≤ ∑ _r ∈ Finset.range (k + 1), C * R := Finset.sum_le_sum key
      _ = ((k : ℝ) + 1) * (C * R) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  calc α ^ 2 * (∑ r ∈ Finset.range (k + 1),
        ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      = ∑ r ∈ Finset.range (k + 1),
          α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z) := by
        rw [Finset.mul_sum]
    _ ≤ ((k : ℝ) + 1) * (C * R) := hsum
    _ = ((k : ℝ) + 1) * C * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
        rw [hR]
        ring

/-- **`InterpFam k` from the existential trace-class estimate.** -/
theorem interpFamOfTrace_exists
    (h : ∃ C : ℝ, 0 < C ∧ InterpOpenTraceStmt C) (k : ℕ) :
    Work.FTS.EllSol.PkgK5.InterpFam k := by
  obtain ⟨C, hC, hstmt⟩ := h
  exact interpFamOfTrace hC hstmt k

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.CexK5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.CexK5

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. The angular moment of the radial `sin 2θ` mode -/


/-! ## 2. The `sin 2θ`-direction of the quotient `U/sin 2θ` -/


/-! ## 3. The first-order relation of `Gbar` -/

/-- `HasDerivAt (Gbar α F) (DGbar α F z) z` from the primitive facts on `F_*`. -/
theorem hasDerivAt_Gbar_DGbar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hJ : HasDerivAt (Work.Elliptic.Jfun α F)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z) :
    HasDerivAt (Work.Elliptic.Gbar α F) (Work.Elliptic.DGbar α F z) z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hA : HasDerivAt (Work.Elliptic.Abar α) (Work.Elliptic.DAbar α z) z := by
    have hp : HasDerivAt (fun y : ℝ => y ^ (-(5 / α))) ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
      Real.hasDerivAt_rpow_const (Or.inl hz0)
    have h := hp.const_mul (-(3 / (4 * α)))
    convert h using 1
    · ext y; rfl
    · show (-(3 / (4 * α)) * (-(5 / α))) * z ^ (-(5 / α) - 1)
          = -(3 / (4 * α)) * (-(5 / α) * z ^ (-(5 / α) - 1))
      ring
  have h := hA.mul hJ
  have hfun : (Work.Elliptic.Abar α * Work.Elliptic.Jfun α F) = Work.Elliptic.Gbar α F := rfl
  rw [hfun] at h
  simpa only [Work.Elliptic.DGbar] using h

/-- **The first-order relation of `Ḡ`**:  `α·D_z(Ḡ α F) = -5·Ḡ α F - (3/4)·F_*(F)`, i.e.
`α·z·∂_z(Gbar α F) z = -5·Gbar α F z - (3/4)·Fstar F z` on `z > 0`.

This is `Gsing_deriv_rel` (`α z ∂_z Gsing = -5 Ḡ`, proved in
`Submission/Work/FTS/EllipticEst/Gsing_deriv_rel.lean`) together with
`α z ∂_z Gstar = (3/4)F_*`. -/
theorem Gbar_deriv_rel (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z)
    (hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z)
    (hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α * (z * Work.Elliptic.DGbar α F z)
        = -5 * Work.Elliptic.Gbar α F z - (3 / 4) * Work.Elliptic.Fstar F z := by
  intro z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hJz : HasDerivAt (Work.Elliptic.Jfun α F)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    have h := hJ z hz
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        = Work.Elliptic.Jfun α F := rfl
    rw [hfun] at h
    exact h
  have hGstar : HasDerivAt (Work.Elliptic.Gstar α F) (Work.Elliptic.DGstar α F z) z := by
    have h := (hL12 z hz).const_mul (-(1 / (4 * α)))
    have hfun : (fun z' => -(1 / (4 * α)) * Work.Elliptic.L12 F z') = Work.Elliptic.Gstar α F := rfl
    rw [hfun] at h
    simpa only [Work.Elliptic.DGstar] using h
  have hGbar : HasDerivAt (Work.Elliptic.Gbar α F) (Work.Elliptic.DGbar α F z) z :=
    hasDerivAt_Gbar_DGbar α F hz hJz
  -- the split of `deriv (Gsing α F)` and the proved relation for `Gsing`
  have hsum : deriv (Work.Elliptic.Gsing α F) z
      = Work.Elliptic.DGstar α F z + Work.Elliptic.DGbar α F z := by
    have hfun : Work.Elliptic.Gsing α F = Work.Elliptic.Gstar α F + Work.Elliptic.Gbar α F := rfl
    rw [hfun, deriv_add hGstar.differentiableAt hGbar.differentiableAt,
      hGstar.deriv, hGbar.deriv]
  have hrel := Work.FTS.EllipticEst.Gsing_deriv_rel α F hα hL12 hFc hJ z hz
  rw [hsum] at hrel
  -- `hrel : α * z * (DGstar + DGbar) = -5 * Gbar`
  have hdst : Work.Elliptic.DGstar α F z
      = 3 * Work.Elliptic.Fstar F z / (4 * α * z) := by
    rw [Work.Elliptic.DGstar]
    field_simp
  rw [hdst] at hrel
  have h3 : α * z * (3 * Work.Elliptic.Fstar F z / (4 * α * z) + Work.Elliptic.DGbar α F z)
      = α * z * (3 * Work.Elliptic.Fstar F z / (4 * α * z))
        + α * z * Work.Elliptic.DGbar α F z := by ring
  rw [h3] at hrel
  have h2 : α * z * (3 * Work.Elliptic.Fstar F z / (4 * α * z))
      = (3 / 4) * Work.Elliptic.Fstar F z := by
    field_simp
  rw [h2] at hrel
  linarith [hrel]

/-! ## 4. The quotient of the witness -/



/-! ## 5. The witness with the explicit profile -/


end Work.FTS.EllSol.PkgK5.CexK5
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.wall_of_interp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The wall: `α D_z∂_θV ∈ ℋ^k` from the `i = 0` family of the interpolation estimate

This module proves `Work.FTS.EllSol.PkgK5.wall_of_interp`: **conditional on the `i = 0` family
`InterpFam k` of the paper's §7 mixed-derivative interpolation** (`Submission/Work/FTS/EllSol/
PkgK5/i0Family_le_openTrace.lean`, whose statement is recorded as the `abbrev` `InterpFam` in
`WallDefs.lean`), the open-class `ℋ^k`-estimate for the mixed radial-angular derivative holds:

  `HkMem α k (D_z∂_θV)  ∧  α |D_z∂_θV|_{ℋ^k} ≤ C (α² |D_z²V|_{ℋ^k} + |∂_θ²V|_{ℋ^k}
      + α |D_zV|_{ℋ^k})`.

The assembly is a verbatim adaptation of the *strip*-class proof
`Work.Blocks.alphaDz_pth_core_strip`, with two changes forced by the open-class setting:

* the strip interpolation `ADZW.i0Family_le_strip` is replaced by the hypothesis `InterpFam k`
  (same statement, open class, with the `D_z^jV`-traces at the two angular endpoints);
* the fourth membership `HkMem α k (D_z∂_θV)` — which the strip statement takes as a hypothesis,
  and which is what makes the majorant of the interpolation family integrable — is here
  *derived* from `HkMem α k (D_z∂_θ²V)` by the angular Hardy descent
  `Work.FTS.EllSol.PkgK5.HkMem_Dz_pth_of_diag`, and then used both for the majorant integrability
  (`Work.Blocks.StripMajorantAux.mixIntS_dzIter_integrable`) and as the first conjunct of the
  conclusion.

Everything else is the proven decomposition of `HkSq α k (α · D_z∂_θV)` into the two families
(`Work.EllipticEst.Core.HkSqLHS_le_summands_v2`), the mixed-family bound
(`Work.EllipticEst.Core.mixedFamily_le`), the scalar homogeneity of the norm
(`Work.FTS.EllipticEst.HkNorm_const_mul`) and the square-root arithmetic.
-/

namespace Work.FTS.EllSol.PkgK5

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Elementary facts -/

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
private theorem sqrt_add_le_aux {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h0 : 0 ≤ Real.sqrt a + Real.sqrt b := by positivity
  have hle : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq h0

/-! ## Integrability of the majorant of the interpolation estimate -/

/-- **Integrability of a mixed-family summand** (`Work.EllipticEst.Core.mixedIntS_integrableOn`,
inlined here so that this module's import cone stays free of `sorry`): for `1 ≤ i`, `i+j ≤ k`
the slice functional `mixedIntS α i j V` is integrable in `z`.

The proof is the domination of `mixedIntS_le_slice` by the `θ`-integral of
`HkIntegrand α k (∂_θ²V)` (integrable in `z` by `HkMem α k (∂_θ²V)`) together with the
a.e. measurability of the slice functional as a function of `z`. -/
private theorem mixedIntS_integrable_aux {k : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixedIntS α i j V z)
      Work.Spaces.Iz := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.sd_lop_iter_sin_bound k
  have hV' : ContDiffOn ℝ ∞ (Function.uncurry V) Work.EllipticEst.Core.sliceU := hV
  set Cc : ℝ := ((i : ℝ) * 4 ^ (i - 1) * K ^ 2) * ((i : ℝ) + 1) with hCc
  have hCcnn : 0 ≤ Cc := by rw [hCc]; positivity
  -- the pointwise (in `z`) bound
  have hle : ∀ z ∈ Work.Spaces.Iz,
      Work.EllipticEst.Core.mixedIntS α i j V z ≤ Cc * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ) := by
    intro z hz
    rw [hCc]
    exact Work.EllipticEst.Core.mixedIntS_le_slice hKpos.le hK hα hα1 hV' hmem hi hij z hz
  -- measurability
  have haesm : AEStronglyMeasurable (fun z : ℝ => Work.EllipticEst.Core.mixedIntS α i j V z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := Work.EllipticEst.Core.v2_aesm_integral ((hV.pth).mixed (j + 1) i)
      (-(Work.Spaces.gam α))
    simpa only [Work.EllipticEst.Core.mixedIntS, Work.FTS.EllipticEst.thGam]
      using h.aestronglyMeasurable
  -- the domination by an integrable function
  have hmono : MeasureTheory.IntegrableOn (fun z : ℝ => Cc * (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ)) Work.Spaces.Iz :=
    hmem.2.const_mul Cc
  refine MeasureTheory.Integrable.mono' hmono haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  have hnn : 0 ≤ Work.EllipticEst.Core.mixedIntS α i j V z := by
    rw [Work.EllipticEst.Core.mixedIntS]
    exact mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))))
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle z hz

/-- **Integrability of the majorant of the interpolation estimate.**

For `0 < α ≤ 1/4` and `V` smooth on the open quadrant with the four memberships
`D_zV, D_z²V, ∂_θ²V, D_z∂_θV ∈ ℋ^k`, the function

`z ↦ α² Σ_{r≤k} mixIntS (D_z^rV) z + α² Σ_{1≤i, i+j≤k} mixedIntS α i j V z`

is integrable on `[0,∞)`.

This is `Work.Blocks.alphaDz_pth_core_strip`'s private `majorant_integrable_strip_aux` with the
public (and open-class) radial integrability `StripMajorantAux.mixIntS_dzIter_integrable`; the
mixed family is `Work.EllipticEst.Core.mixedIntS_integrableOn`. -/
private theorem majorant_integrable_open (k : ℕ) :
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)) →
      MeasureTheory.IntegrableOn (fun z : ℝ =>
          α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                Work.EllipticEst.Core.mixedIntS α i j V z
              else 0)) Work.Spaces.Iz := by
  intro α V hα hα4 hV h0 hpi hmd hmdd hmtt hmix
  have hα1 : α ≤ 1 := by linarith
  -- the radial family
  have hA : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ r ∈ Finset.range (k + 1),
      Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z) Work.Spaces.Iz := by
    refine MeasureTheory.integrable_finsetSum _ (fun r hr => ?_)
    exact Work.Blocks.StripMajorantAux.mixIntS_dzIter_integrable hV hmix
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
  -- the mixed family
  have hB : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0))
      Work.Spaces.Iz := by
    refine MeasureTheory.integrable_finsetSum _ (fun i hi => ?_)
    refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact mixedIntS_integrable_aux hα hα1 hV hmtt hc.1 hc.2
    · simp only [if_neg hc]
      exact MeasureTheory.integrableOn_zero
  have h1 : MeasureTheory.IntegrableOn (fun z : ℝ => α ^ 2 *
      (∑ r ∈ Finset.range (k + 1), Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
      Work.Spaces.Iz :=
    MeasureTheory.Integrable.const_mul hA _
  have h2 : MeasureTheory.IntegrableOn (fun z : ℝ => α ^ 2 *
      (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0)))
      Work.Spaces.Iz :=
    MeasureTheory.Integrable.const_mul hB _
  refine (h1.add h2).congr_fun ?_ measurableSet_Ici
  intro z _
  simp only [Pi.add_apply]

/-! ## The wall -/

theorem wall_of_interp (k : ℕ) (hk : 2 ≤ k) (hI : InterpFam k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      (∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j V z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pthIter 2 V)) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)) ∧
      α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (Work.Spaces.pth V))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
            + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V)) := by
  obtain ⟨C2, hC2pos, h2⟩ := hI
  obtain ⟨C1, hC1pos, h1⟩ := Work.EllipticEst.Core.HkSqLHS_le_summands_v2 k
  obtain ⟨C3, hC3pos, h3⟩ := Work.EllipticEst.Core.mixedFamily_le k
  refine ⟨Real.sqrt (C1 * (C2 + C3) + C2), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α V hα hα4 hV h0 hpi htr hmd hmdd hmtt hmix
  have hk1 : 1 ≤ k := by omega
  -- the missing membership, by the angular Hardy descent from `D_z∂_θ²V`
  have hmixpth : Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)) :=
    Work.FTS.EllSol.PkgK5.HkMem_Dz_pth_of_diag k hk1 α V hα hα4 hV h0 hpi htr hmix
  refine ⟨hmixpth, ?_⟩
  -- the two families of the decomposition and the right-hand side
  set A : ℝ := ∑ r ∈ Finset.range (k + 1),
      ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z with hAdef
  set B : ℝ := ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then
        ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z else 0 with hBdef
  set R : ℝ := α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
      + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
      + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    have hdd := Work.Spaces.HkSq_nonneg α k (Work.Spaces.DzIter 2 V)
    have htt := Work.Spaces.HkSq_nonneg α k (Work.Spaces.pthIter 2 V)
    have hd := Work.Spaces.HkSq_nonneg α k (Work.Spaces.Dz V)
    have hα4' : 0 ≤ α ^ 4 := by positivity
    have hα2' : 0 ≤ α ^ 2 := by positivity
    linarith [mul_nonneg hα4' hdd, mul_nonneg hα2' hd]
  -- the `i = 0` family: this is the hypothesis `InterpFam k`
  have h2' : α ^ 2 * A ≤ C2 * R := by
    rw [hAdef, hRdef]
    exact h2 α V hα hα4 hV h0 hpi htr hmdd hmtt hmd
  -- the mixed (`D_θ`) family
  have h3' : α ^ 2 * B ≤ C3 * R := by
    rw [hBdef, hRdef]
    exact h3 α V hα hα4 hV h0 hpi hmdd hmtt hmd
  -- the decomposition of the left-hand side
  have key : Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ (C1 * (C2 + C3) + C2) * R := by
    have hmaj := majorant_integrable_open k α V hα hα4 hV h0 hpi hmd hmdd hmtt hmixpth
    have hSq1 : Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C1 * (α ^ 2 * A + α ^ 2 * B) := by
      rw [hAdef, hBdef]
      exact h1 α V hα hV hmaj
    have hsum : α ^ 2 * A + α ^ 2 * B ≤ (C2 + C3) * R := by linarith [h2', h3']
    calc Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C1 * (α ^ 2 * A + α ^ 2 * B) := hSq1
      _ ≤ C1 * ((C2 + C3) * R) := mul_le_mul_of_nonneg_left hsum hC1pos.le
      _ ≤ (C1 * (C2 + C3) + C2) * R := by
          calc C1 * ((C2 + C3) * R) = (C1 * (C2 + C3)) * R := by ring
            _ ≤ (C1 * (C2 + C3) + C2) * R :=
                mul_le_mul_of_nonneg_right (by linarith [hC2pos.le]) hR0
  -- the square-root step
  have hDpos : 0 ≤ C1 * (C2 + C3) + C2 := by
    linarith [hC2pos.le, mul_nonneg hC1pos.le (add_nonneg hC2pos.le hC3pos.le)]
  have hNorm : Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ Real.sqrt (C1 * (C2 + C3) + C2) * Real.sqrt R := by
    rw [Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α k _)
        ≤ Real.sqrt ((C1 * (C2 + C3) + C2) * R) := Real.sqrt_le_sqrt key
      _ = Real.sqrt (C1 * (C2 + C3) + C2) * Real.sqrt R := Real.sqrt_mul hDpos R
  have h1' : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V))
      = α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V) := by
    rw [Work.Spaces.HkNorm]
    rw [show α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
        = (α ^ 2) ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h3'' : Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V))
      = α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V) := by
    rw [Work.Spaces.HkNorm]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hα.le]
  have hsqrtR : Real.sqrt R
      ≤ α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V)
        + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
        + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V) := by
    have hb1 : 0 ≤ α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) :=
      mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α k (Work.Spaces.DzIter 2 V))
    have hb2 : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) :=
      Work.Spaces.HkSq_nonneg α k (Work.Spaces.pthIter 2 V)
    have hb3 : 0 ≤ α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) :=
      mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α k (Work.Spaces.Dz V))
    have hs2 : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
          + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
          + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V))
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V))
          + Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) :=
      sqrt_add_le_aux (add_nonneg hb1 hb2) hb3
    have hs1 : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
          + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V))
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V))
          + Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)) :=
      sqrt_add_le_aux hb1 hb2
    rw [hRdef]
    calc Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V))
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V))
          + Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := hs2
      _ ≤ (Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V))
            + Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)))
          + Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by linarith [hs1]
      _ = α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V)
          + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
          + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V) := by
        rw [h1', h3'']
        simp only [Work.Spaces.HkNorm]
  -- the left-hand side, as a scalar multiple
  have hsmul : Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      = α * Work.Spaces.HkNorm α k (Work.Spaces.Dz (Work.Spaces.pth V)) := by
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α k α (f := Work.Spaces.Dz (Work.Spaces.pth V))
      (fun n => (hV.pth).Dz.forall n)]
    rw [abs_of_pos hα]
  rw [← hsmul]
  calc Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ Real.sqrt (C1 * (C2 + C3) + C2) * Real.sqrt R := hNorm
    _ ≤ Real.sqrt (C1 * (C2 + C3) + C2) *
          (α ^ 2 * Work.Spaces.HkNorm α k (Work.Spaces.DzIter 2 V)
          + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
          + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V)) :=
        mul_le_mul_of_nonneg_left hsqrtR (Real.sqrt_nonneg _)

end

end Work.FTS.EllSol.PkgK5
end
-- ===== merged: Submission.Work.FTS.EpsEngine.AK2_sections_restrict =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory

/-- Restriction form of `EpsLocalPStar.AK2_sections`: if the uncurried family
`(s, z, θ) ↦ Φ s z θ` is a.e.-strongly-measurable with respect to
`(volume ↾ A) ⊗ volume`, then for a.e. `s ∈ A` the profile `Φ s` is `AK2`. -/
theorem AK2_sections_restrict {α : ℝ} {A : Set ℝ} {Φ : ℝ → Work.FTS.Galerkin.Fn}
    (h : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod MeasureTheory.volume)) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict A),
      Work.FTS.StrongEps.EpsLocalPStar.AK2 α (Φ s) := by
  have h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict A),
      MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Φ s p.1 p.2) (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
    h.prodMk_left (ν := (MeasureTheory.volume : Measure (ℝ × ℝ)))
  filter_upwards [h2] with s hs
  unfold Work.FTS.StrongEps.EpsLocalPStar.AK2
  have hs' : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Φ s p.1 p.2)
      Work.FTS.StrongEps.EpsLocalPStar.DomM :=
    hs.mono_measure Work.FTS.StrongEps.EpsLocalPStar.DomM_le_volume
  refine (hs'.mul (Work.FTS.StrongEps.EpsLocalPStar.measurable_epsW α).aestronglyMeasurable).congr ?_
  filter_upwards with p
  simp only [Pi.mul_apply]

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.EpsMem_and_EpsSq_le_of_ae_tendsto_mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

set_option autoImplicit false

theorem EpsMem_and_EpsSq_le_of_ae_tendsto_mem {α B : ℝ} (hB : 0 ≤ B)
    {A : ℕ → Work.FTS.Galerkin.Fn} {Alim : Work.FTS.Galerkin.Fn}
    (hmem : ∀ m : ℕ, Work.FTS.StrongEps.EpsMem α (A m))
    (hbd : ∀ m : ℕ, Work.FTS.StrongEps.EpsSq α (A m) ≤ B)
    (hlim : Filter.Eventually (fun p : ℝ × ℝ =>
        Filter.Tendsto (fun m : ℕ => A m p.1 p.2) Filter.atTop (nhds (Alim p.1 p.2)))
      (MeasureTheory.ae Work.FTS.StrongEps.EpsLocalPStar.DomM)) :
    Work.FTS.StrongEps.EpsMem α Alim ∧ Work.FTS.StrongEps.EpsSq α Alim ≤ B := by
  -- ### the weighted sequence converges a.e. to the weighted limit
  have hlimW : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
      Filter.Tendsto (fun m : ℕ => A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
        Filter.atTop (nhds (Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)) :=
    hlim.mono fun p hp => hp.mul_const _
  -- ### the squared weighted profiles are a.e. strongly measurable
  have haesm : ∀ m : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      Work.FTS.StrongEps.EpsLocalPStar.DomM := fun m =>
    (Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2.mp (hmem m)).aestronglyMeasurable
  have haesmLim : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      Work.FTS.StrongEps.EpsLocalPStar.DomM :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop haesm
      (hlimW.mono fun p hp => hp.pow 2)
  -- ### Fatou for the `ℝ≥0∞`-valued size
  have hmeas : ∀ m : ℕ, AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
      Work.FTS.StrongEps.EpsLocalPStar.DomM := fun m =>
    ((haesm m).aemeasurable).ennreal_ofReal
  have hpt : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
      ENNReal.ofReal ((Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ≤ Filter.liminf (fun m : ℕ =>
            ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
          Filter.atTop := by
    filter_upwards [hlimW] with p hp
    have h1 : Filter.Tendsto (fun m : ℕ =>
        ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
        Filter.atTop
        (nhds (ENNReal.ofReal ((Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto
        ((Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)).comp (hp.pow 2)
    rw [h1.liminf_eq]
  have hfatou : Work.FTS.StrongEps.EpsLocalPStar.epsL2 α Alim
      ≤ Filter.liminf (fun m : ℕ => Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (A m))
          Filter.atTop := by
    unfold Work.FTS.StrongEps.EpsLocalPStar.epsL2
    exact (MeasureTheory.lintegral_mono_ae hpt).trans
      (MeasureTheory.lintegral_liminf_le' hmeas)
  have hbound : ∀ m : ℕ, Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (A m) ≤ ENNReal.ofReal B :=
    fun m => Work.FTS.StrongEps.EpsLocalPStar.epsL2_le_ofReal_of_mem (hmem m) (hbd m)
  have hb : Filter.liminf (fun m : ℕ => Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (A m))
      Filter.atTop ≤ ENNReal.ofReal B :=
    Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun m => hbound m)
  have hL2 : Work.FTS.StrongEps.EpsLocalPStar.epsL2 α Alim ≤ ENNReal.ofReal B :=
    hfatou.trans hb
  -- ### membership and the bound
  have hmemLim : Work.FTS.StrongEps.EpsMem α Alim := by
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2]
    refine ⟨haesmLim, ?_⟩
    exact (MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun p => sq_nonneg _)).mpr
        (lt_of_le_of_lt hL2 ENNReal.ofReal_lt_top)
  exact ⟨hmemLim,
    Work.FTS.StrongEps.EpsLocalPStar.EpsSq_le_of_epsL2_le_of_mem hB hmemLim hL2⟩

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.EpsSq_intervalIntegral_le_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

theorem EpsSq_intervalIntegral_le_gen {α a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    {G : ℝ → Work.FTS.Galerkin.Fn}
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2 * Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM))
    (hbd : Filter.Eventually (fun s : ℝ =>
        Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (G s) ≤ ENNReal.ofReal B)
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.uIoc a b)))) :
    Work.FTS.StrongEps.EpsMem α (fun z θ => ∫ s in a..b, G s z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ => ∫ s in a..b, G s z θ) ≤ (b - a) * ((b - a) * B) := by
  classical
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  -- the uncurried weighted curve, in the shape in which `hmeas` is stated
  set X : ℝ × (ℝ × ℝ) → ℝ :=
    fun q => G q.1 q.2.1 q.2.2 * Work.FTS.StrongEps.epsW α q.2.1 q.2.2 with hX
  have hmeas' : MeasureTheory.AEStronglyMeasurable X
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM) := hmeas
  -- the interval integral of a profile is the integral of its weighted slice against
  -- `volume.restrict (uIoc a b)`, the weight being constant in the parameter
  have hint_eq : ∀ p : ℝ × ℝ, (∫ s in a..b, G s p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2
      = ∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    intro p
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab, hX]
    exact (MeasureTheory.integral_mul_const (Work.FTS.StrongEps.epsW α p.1 p.2)
      (fun s => G s p.1 p.2)).symm
  -- the parameter measure is finite, of total mass `b - a`
  haveI hνfin : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc a b)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc,
      abs_of_nonneg hba]
    exact ENNReal.ofReal_lt_top⟩
  have hnu : (MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ = ENNReal.ofReal (b - a) := by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc,
      abs_of_nonneg hba]
  have hnu_ne : (MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ ≠ ⊤ := by
    rw [hnu]; exact ENNReal.ofReal_ne_top
  -- a.e. strong measurability of the weighted parametric integral
  have hAK : Work.FTS.StrongEps.EpsLocalPStar.AK2 α (fun z θ => ∫ s in a..b, G s z θ) := by
    unfold Work.FTS.StrongEps.EpsLocalPStar.AK2
    refine (hmeas'.prod_swap.integral_prod_right').congr ?_
    filter_upwards with p
    exact (hint_eq p).symm
  -- `epsL2` of the parametric integral, in terms of the `s`-integral of the curve
  have hstep1 : Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (fun z θ => ∫ s in a..b, G s z θ)
      = ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2)
          ∂Work.FTS.StrongEps.EpsLocalPStar.DomM := by
    unfold Work.FTS.StrongEps.EpsLocalPStar.epsL2
    exact lintegral_congr (fun p => by rw [hint_eq p])
  -- Cauchy–Schwarz in the parameter, pointwise in the profile variable
  have hpt : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
      ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2)
        ≤ (∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
          * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) := by
    filter_upwards [hmeas'.prodMk_right] with p hp
    have hen : ENNReal.ofReal |∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b))|
        ≤ ∫⁻ s, ENNReal.ofReal |X (s, p)| ∂(MeasureTheory.volume.restrict (Set.uIoc a b)) := by
      have h := enorm_integral_le_lintegral_enorm
        (μ := MeasureTheory.volume.restrict (Set.uIoc a b)) (fun s => X (s, p))
      simpa [Real.enorm_eq_ofReal_abs] using h
    have hcs := Work.FTS.StrongEps.EpsLocalPStar.l2_cs
      (ν := MeasureTheory.volume.restrict (Set.uIoc a b)) (b := fun _ => (1 : ℝ))
      aemeasurable_const (fun _ => one_pos) hp.aemeasurable
    calc ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2)
        = (ENNReal.ofReal |∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b))|)^2 :=
          Work.FTS.StrongEps.EpsLocalPStar.ofReal_sq_abs _
      _ ≤ (∫⁻ s, ENNReal.ofReal |X (s, p)| ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2 :=
          pow_le_pow_left₀ bot_le hen 2
      _ ≤ (∫⁻ s, ENNReal.ofReal (X (s, p)^2 / 1) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * (∫⁻ s, ENNReal.ofReal (1 : ℝ) ∂(MeasureTheory.volume.restrict (Set.uIoc a b))) := hcs
      _ = (∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) := by
          simp only [div_one, ENNReal.ofReal_one, lintegral_one]
  -- joint measurability for Tonelli
  have hjoint : AEMeasurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal ((X (q.2, q.1))^2))
      ((Work.FTS.StrongEps.EpsLocalPStar.DomM).prod
        (MeasureTheory.volume.restrict (Set.uIoc a b))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hmeas'.prod_swap.aemeasurable).pow_const 2)
  -- the arithmetic of the final constant (in `ℝ≥0∞`, via `ofReal_mul` on `ℝ`)
  have hBA : ENNReal.ofReal B * (ENNReal.ofReal (b - a) * ENNReal.ofReal (b - a))
      = ENNReal.ofReal ((b - a) * ((b - a) * B)) := by
    rw [← ENNReal.ofReal_mul hba]
    rw [← ENNReal.ofReal_mul hB]
    congr 1
    ring
  -- the chain: Cauchy–Schwarz, Tonelli, the a.e. bound, and the arithmetic
  have hchain : ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2)
      ∂Work.FTS.StrongEps.EpsLocalPStar.DomM ≤ ENNReal.ofReal ((b - a) * ((b - a) * B)) := by
    calc ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))^2)
        ∂Work.FTS.StrongEps.EpsLocalPStar.DomM
        ≤ ∫⁻ p, (∫⁻ s, ENNReal.ofReal ((X (s, p))^2)
              ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ)
            ∂Work.FTS.StrongEps.EpsLocalPStar.DomM := lintegral_mono_ae hpt
      _ = (∫⁻ p, ∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc a b))
            ∂Work.FTS.StrongEps.EpsLocalPStar.DomM)
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) := by
          rw [MeasureTheory.lintegral_mul_const' _ _ hnu_ne]
      _ = (∫⁻ s, ∫⁻ p, ENNReal.ofReal ((X (s, p))^2) ∂Work.FTS.StrongEps.EpsLocalPStar.DomM
            ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) := by
          rw [MeasureTheory.lintegral_lintegral_swap hjoint]
      _ = (∫⁻ s, Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (G s)
            ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) := by
          congr 1
      _ ≤ (∫⁻ s, ENNReal.ofReal B ∂(MeasureTheory.volume.restrict (Set.uIoc a b)))
            * ((MeasureTheory.volume.restrict (Set.uIoc a b)) Set.univ) :=
          mul_le_mul_of_nonneg_right (lintegral_mono_ae hbd) bot_le
      _ = ENNReal.ofReal ((b - a) * ((b - a) * B)) := by
          rw [MeasureTheory.lintegral_const, hnu, mul_assoc]
          exact hBA
  -- membership and the size bound out of the `epsL2`-bound
  refine Work.FTS.StrongEps.EpsLocalPStar.EpsMem_and_EpsSq_le_of_epsL2_le
    (mul_nonneg hba (mul_nonneg hba hB)) hAK ?_
  rw [hstep1]
  exact hchain

end

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.mixed_routed_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission/Work/FTS/EpsEngine/ThetaFromEpsLeafA/mixed_routed_sq_le.lean`

The **routed `L²`-slot bound** for the log-coordinate mollifier `J_ε`: every framed derivative
`D_z^b D_θ^a (J_ε g)` is bounded, pointwise in `(z,θ)`, by its *fully routed* kernel form

  `D_z^b D_θ^a (J_ε g)(z,θ) = 2^a ∫_p ∂₁^b∂₂^a(Jker ρ ε)(p) · g(z e^{-p₁}, arctan(tan θ e^{-p₂}))`

(`Work.FTS.StrongEps.mixed_Jeps_kernel_partial`), and Cauchy–Schwarz for the `p`-integral turns
this into

  `(D_z^b D_θ^a (J_ε g)(z,θ))² ≤ 4^a (∫ |∂₁^b∂₂^a Jker|) (∫ |∂₁^b∂₂^a Jker| · (g ∘ shift)²)`

— exactly the statement below.  All the `(z,θ)`-dependence that is *not* routed is carried by the
single weighted `L²`-profile `∫ |K| (g∘shift)²`, which is what the later `H^k`-gain estimates
consume.

The only analytic input is that `∂₁^b∂₂^a (Jker ρ ε)` is continuous with compact support
(`Work.FTS.StrongEps.EpsE4Thr.KdK_continuous`, `…KdK_hasCompactSupport`) and that the shifted
profile `p ↦ g (z e^{-p₁}) (arctan (tan θ e^{-p₂}))` is *continuous*: the shifts place every
argument strictly inside the open quadrant `Quad = (0,∞) × (0,π/2)`, where `g` is `C^∞`.
The Cauchy–Schwarz step is the real-integral Bunyakovsky inequality
`Work.RPFresh.integral_mul_sq_le_sq_mul_sq`, applied to the nonnegative functions
`√|K|` and `√|K|·|g∘shift|` (the sign of `K` being absorbed by `|∫ K·(g∘shift)| ≤ ∫ |K·(g∘shift)|`),
so that no hypothesis on the (possibly unbounded) profile `g` is needed beyond continuity on the
quadrant.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafA

set_option maxHeartbeats 1000000

/-! ## The abstract Cauchy–Schwarz core -/

/-- **Cauchy–Schwarz for a compactly supported weight.**  For a continuous compactly supported
`K` and an arbitrary continuous `G`,

  `(∫ K G)² ≤ (∫ |K|) · (∫ |K| G²)`.

Proof: `|∫ K G| ≤ ∫ |K G| = ∫ √|K| · (√|K| |G|)`, and Bunyakovsky applied to
`√|K|` and `√|K| |G|` bounds the square by `(∫ |K|)(∫ |K| G²)`.  Both square-integrable
functions of the Cauchy–Schwarz are continuous (hence measurable), and both squares
(`|K|` and `|K| G²`) are continuous with compact support, hence integrable. -/
theorem cs_sq_le_of_compact {K G : ℝ × ℝ → ℝ} (hKc : Continuous K)
    (hKcpt : HasCompactSupport K) (hGc : Continuous G) :
    (∫ p : ℝ × ℝ, K p * G p) ^ 2
      ≤ (∫ p : ℝ × ℝ, |K p|) * (∫ p : ℝ × ℝ, |K p| * G p ^ 2) := by
  have hKabsi : Integrable (fun p : ℝ × ℝ => |K p|) :=
    hKc.abs.integrable_of_hasCompactSupport hKcpt.abs
  have hprodi : Integrable (fun p : ℝ × ℝ => |K p| * G p ^ 2) := by
    have h1 : HasCompactSupport (fun p : ℝ × ℝ => |K p| * G p ^ 2) := by
      refine hKcpt.mono (fun p hp => ?_)
      simp only [Function.mem_support] at hp ⊢
      intro hK0
      exact hp (by rw [hK0, abs_zero, zero_mul])
    exact (hKc.abs.mul (hGc.pow 2)).integrable_of_hasCompactSupport h1
  have hFmeas : Measurable (fun p : ℝ × ℝ => Real.sqrt |K p|) :=
    Real.continuous_sqrt.measurable.comp hKc.abs.measurable
  have hHmeas : Measurable (fun p : ℝ × ℝ => Real.sqrt |K p| * |G p|) :=
    hFmeas.mul hGc.abs.measurable
  have hF2 : Integrable (fun p : ℝ × ℝ => (Real.sqrt |K p|) ^ 2) :=
    hKabsi.congr (Filter.Eventually.of_forall fun p => (Real.sq_sqrt (abs_nonneg (K p))).symm)
  have hH2 : Integrable (fun p : ℝ × ℝ => (Real.sqrt |K p| * |G p|) ^ 2) :=
    hprodi.congr (Filter.Eventually.of_forall fun p => by
      beta_reduce
      rw [mul_pow, Real.sq_sqrt (abs_nonneg (K p)), sq_abs])
  have hcs := Work.RPFresh.integral_mul_sq_le_sq_mul_sq (MeasureTheory.volume : Measure (ℝ × ℝ))
      (f := fun p : ℝ × ℝ => Real.sqrt |K p|) (h := fun p : ℝ × ℝ => Real.sqrt |K p| * |G p|)
      hFmeas.aestronglyMeasurable hHmeas.aestronglyMeasurable hF2 hH2
  have hkey : (∫ p : ℝ × ℝ, Real.sqrt |K p| * (Real.sqrt |K p| * |G p|))
      = ∫ p : ℝ × ℝ, |K p| * |G p| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [← mul_assoc,
      show Real.sqrt |K p| * Real.sqrt |K p| = |K p| from by
        rw [← sq, Real.sq_sqrt (abs_nonneg (K p))]]
  have hA : (∫ p : ℝ × ℝ, (Real.sqrt |K p|) ^ 2) = ∫ p : ℝ × ℝ, |K p| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [Real.sq_sqrt (abs_nonneg (K p))]
  have hB : (∫ p : ℝ × ℝ, (Real.sqrt |K p| * |G p|) ^ 2)
      = ∫ p : ℝ × ℝ, |K p| * G p ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [mul_pow, Real.sq_sqrt (abs_nonneg (K p)), sq_abs]
  rw [hkey, hA, hB] at hcs
  have habs : |∫ p : ℝ × ℝ, K p * G p| ≤ ∫ p : ℝ × ℝ, |K p| * |G p| := by
    refine (MeasureTheory.abs_integral_le_integral_abs
      (μ := (MeasureTheory.volume : Measure (ℝ × ℝ)))
      (f := fun p : ℝ × ℝ => K p * G p)).trans_eq ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [abs_mul]
  have hYnn : 0 ≤ ∫ p : ℝ × ℝ, |K p| * |G p| :=
    integral_nonneg fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsq : (|∫ p : ℝ × ℝ, K p * G p|) ^ 2 ≤ (∫ p : ℝ × ℝ, |K p| * |G p|) ^ 2 := by
    refine (sq_le_sq).mpr ?_
    simpa only [abs_of_nonneg hYnn, abs_abs] using habs
  calc (∫ p : ℝ × ℝ, K p * G p) ^ 2
      = (|∫ p : ℝ × ℝ, K p * G p|) ^ 2 := (sq_abs _).symm
    _ ≤ (∫ p : ℝ × ℝ, |K p| * |G p|) ^ 2 := hsq
    _ ≤ (∫ p : ℝ × ℝ, |K p|) * (∫ p : ℝ × ℝ, |K p| * G p ^ 2) := hcs

/-! ## The shifted profile is continuous -/

/-- The shifted profile `p ↦ g (z e^{-p₁}) (arctan (tan θ e^{-p₂}))` is continuous on `ℝ²`,
for `z > 0` and `θ ∈ (0,π/2)`: the shifts stay strictly inside the open quadrant
(`z e^{-p₁} > 0` and `arctan (tan θ e^{-p₂}) ∈ (0,π/2)`), and `g` is continuous there. -/
theorem continuous_shiftedProfile {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Continuous (fun p : ℝ × ℝ =>
      g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  have hcont : ContinuousOn (Function.uncurry g) Work.FTS.StrongEps.Quad :=
    (contDiffOn_zero).mp (hg 0)
  have hΦ : Continuous
      (fun p : ℝ × ℝ =>
        (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)) := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).comp continuous_fst
    · exact Real.continuous_arctan.comp
        ((continuous_const.mul (Real.continuous_exp.comp continuous_neg)).comp continuous_snd)
  have hmem : ∀ p : ℝ × ℝ,
      (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)
        ∈ Work.FTS.StrongEps.Quad := by
    intro p
    refine ⟨mul_pos hz (Real.exp_pos _), ?_, ?_⟩
    · exact Real.arctan_pos.mpr
        (mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2) (Real.exp_pos _))
    · exact Real.arctan_lt_pi_div_two _
  have h := hcont.comp_continuous hΦ hmem
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using h

/-- **Cauchy–Schwarz for the routed slot**, in exactly the shape the `H^k`-gain estimates
consume: with `K = ∂₁^b ∂₂^a (Jker ρ ε)`, the square of the routed slot integral
`∫_p K(p) · g(z e^{-p₁}, arctan(tan θ e^{-p₂}))` is bounded by
`(∫ |K|) · (∫ |K| · (g ∘ shift)²)`. -/
theorem cs_routed {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {g : Work.FTS.Galerkin.Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (a b : ℕ) :
    (∫ p : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
      ≤ (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|)
        * (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
            * (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
  cs_sq_le_of_compact (K := Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a)
    (G := fun p : ℝ × ℝ =>
      g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (Work.FTS.StrongEps.EpsE4Thr.KdK_continuous hρ ε b a)
    (Work.FTS.StrongEps.EpsE4Thr.KdK_hasCompactSupport hρ hε b a)
    (continuous_shiftedProfile hg hz hθ)

/-! ## The target -/

theorem mixed_routed_sq_le {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (a b : ℕ) :
    (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
      ≤ ((4 : ℝ) ^ a * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|)
        * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
            * (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
  -- route the framed derivative `D_z^b D_θ^a (J_ε g)` completely onto the kernel
  have hrepr : Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ
      = (2 : ℝ) ^ a * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p
          * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    have h := Work.FTS.StrongEps.mixed_Jeps_kernel_partial ρ hρ hε hg hz hθ b a 0 0
      (Nat.zero_le b) (Nat.zero_le a)
    rw [Nat.sub_zero, Nat.sub_zero] at h
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] at h
    simp only [Work.Spaces.mixed]
    rw [h]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [show Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p
        = iteratedDeriv b (fun s => iteratedDeriv a
            (fun t => Work.FTS.StrongEps.Jker ρ ε (s, t)) p.2) p.1
        from congrFun (Work.FTS.StrongEps.Kd_eq (Work.FTS.StrongEps.Jker ρ ε) b a) p]
  -- Cauchy–Schwarz for the `p`-integral
  have hcs := cs_routed hρ hε hg hz hθ a b
  have hpow : ((2 : ℝ) ^ a) ^ 2 = (4 : ℝ) ^ a := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 from by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm a 2]
  rw [hrepr]
  have h1 : ((2 : ℝ) ^ a * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
      = (4 : ℝ) ^ a * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
    rw [mul_pow, hpow]
  rw [h1]
  refine le_trans (mul_le_mul_of_nonneg_left hcs (by positivity))
    (le_of_eq (mul_assoc _ _ _).symm)

end Work.FTS.EpsEngine.ThetaFromEpsLeafA
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.aesm_weighted_prod_restricted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

theorem aesm_weighted_prod_restricted {α : ℝ} {Φ : ℝ → Work.FTS.Galerkin.Fn} {A : Set ℝ}
    (h : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod MeasureTheory.volume)) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2 * Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod Work.FTS.StrongEps.EpsLocalPStar.DomM) := by
  -- `DomM` is dominated by the planar Lebesgue measure, hence so is the product measure;
  -- a.e. strong measurability is preserved when the measure is made smaller.
  have hle : (MeasureTheory.volume.restrict A).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM
      ≤ (MeasureTheory.volume.restrict A).prod
          (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) :=
    MeasureTheory.Measure.prod_mono le_rfl
      Work.FTS.StrongEps.EpsLocalPStar.DomM_le_volume
  have hΦ : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Φ p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod Work.FTS.StrongEps.EpsLocalPStar.DomM) :=
    h.mono_measure hle
  -- the weight `epsW α` is (everywhere) measurable, so a.e. strongly measurable for any measure.
  have hw : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict A).prod Work.FTS.StrongEps.EpsLocalPStar.DomM) :=
    ((Work.FTS.StrongEps.EpsLocalPStar.measurable_epsW α).comp measurable_snd).aestronglyMeasurable
  exact hΦ.mul hw

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.Open2.Top2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Open2

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.VocabO2
open Work.FTS.OpenPkg
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  DenseSpan WeakDetermines IsDynWeakOn ProfileBdd EquicontSpace EquicontTau profileFam RegPkg prof
  galFam GlobalODEExistence IsDynGSolWith)

set_option autoImplicit false
set_option linter.unusedVariables false



end Work.FTS.Open2
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.EstFinal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `ℋᵏ`-norm of the error of the approximation tends to `0`.** -/
theorem tendsto_HkSq_err_final (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (htr : Work.FTS.PhiStar.ThetaTraces α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    Filter.Tendsto (fun n : ℕ => Work.Spaces.HkSq α k (err n F)) Filter.atTop (nhds 0) := by
  obtain ⟨Cm, hCm, hmom⟩ :=
    Work.FTS.PhiStar.Honesty.CptApp.Est.lintegral_momentFactor_le (k := k) hsm hF hFs
  obtain ⟨RPb, hRPb, hRPbd⟩ := Work.FTS.PhiStar.Honesty.CptApp.Est.rhoProf_ae_le k α
  have hvolI : (volume : Measure ℝ) Work.Spaces.Iθ = ENNReal.ofReal (Real.pi / 2) := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    norm_num
  have hRP : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))
      ≤ ENNReal.ofReal (RPb * (Real.pi / 2)) := by
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal RPb :=
          lintegral_mono_ae (hRPbd.mono fun θ h => ENNReal.ofReal_le_ofReal h)
      _ = ENNReal.ofReal RPb * volume Work.Spaces.Iθ := by
          rw [lintegral_const]
          congr 1
          exact Measure.restrict_apply_univ Work.Spaces.Iθ
      _ = ENNReal.ofReal RPb * ENNReal.ofReal (Real.pi / 2) := by rw [hvolI]
      _ = ENNReal.ofReal (RPb * (Real.pi / 2)) := (ENNReal.ofReal_mul hRPb).symm
  refine tendsto_HkSq_err k α hα hα1 hsm hF htr hFs hCm
    (mul_nonneg hRPb (by positivity)) hmom ?_ hRP
  intro n hn
  exact Work.FTS.PhiStar.Honesty.CptApp.EstAlt.hkMem_err k α hα hα1 F n hn hsm hF hFs htr

end Work.FTS.PhiStar.Honesty.CptApp
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.N4bRow23.rowN4ssHon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.rows.N4bRow23

theorem rowN4ssHon (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α Ce : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α) ≤ K * α ^ 3 := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.StrongPersist.L3Rhs.N4ssPriced
  exact ⟨K, hKpos, fun hctx => (hK _ ⟨hctx.hα, hctx.hα1⟩).2⟩

end Work.FTS.StrongEps.E4R3.N4C.rows.N4bRow23
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowN1gs =====
section

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

/-- **Row 9 of the honest §8 table (the `N₁^{g*}` norm bound)**:
`Xn α (N₁^{gs} α g Φg) ≤ K·√α·Xn α g`, uniformly over the honest context `CtxT`. -/
theorem rowN1gs (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gs α g Φg)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨CF, hCF, hF⟩ := Work.FTS.Nonlin.Fstar_W
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * (Ci * (CF + 1)) * max Ce 1 + 1, by positivity, ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hαα₂ : α ≤ α₂ := hctx.hαα₂
  have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
  -- positivity of the pieces
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  -- `F_*` is `SmoothOpen` and in `𝒲^{4,∞}` with norm `≤ Cα`
  have hFsmooth : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  obtain ⟨hFmem, hFle⟩ := hF α hα hα1
  have hFle' : Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) ≤ (CF + 1) * α :=
    le_trans hFle (mul_le_mul_of_nonneg_right (by linarith) hα.le)
  have hFnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 _ hFmem)
      (Work.Spaces.wlThSum_nonneg α 4 _ hFmem)
  -- the coefficient `R = ℛ(Φ̃_g)` of `EllPkgGo`
  have hRreg : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := hell.R.1
  have hRB : Work.FTS.Nonlin.Xn α
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
      ≤ Ce * Work.FTS.Nonlin.Xn α g := hell.R.2
  have hRB' : Work.FTS.Nonlin.Xn α
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
      ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
    le_trans hRB (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg)
  have hRnn : 0 ≤ Work.FTS.Nonlin.Xn α
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) :=
    Work.Spaces.HkNorm_nonneg α 4 _
  -- the `𝒲^{4,∞}`-form of the product rule
  have hprod := hN.wprod α hαIoc (Work.Construction.Fstar α)
    (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) hFsmooth hFmem hRreg
  -- `N₁^{gs}` is `2` times the product `F_* · R`
  have heq : Work.FTS.Nonlin.N1gs α g Φg = fun z θ =>
      2 * (Work.Construction.Fstar α z θ
        * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N1gs]
    ring
  rw [heq, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  -- the chain of bounds
  have hstep1 : Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Construction.Fstar α z θ
          * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ)
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
        * (max Ce 1 * Work.FTS.Nonlin.Xn α g) := by
    refine le_trans hprod.2 ?_
    refine mul_le_mul ?_ hRB' hRnn ?_
    · exact mul_le_mul_of_nonneg_left hFle' (mul_nonneg hCi.le hA)
    · exact mul_nonneg (mul_nonneg hCi.le hA) (mul_nonneg (by linarith) hα.le)
  have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
    rw [Real.sqrt_eq_rpow]
    have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
    rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
    exact h.symm
  have hkey : Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
        * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
      = (Ci * (CF + 1)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) * max Ce 1 := by
    rw [show Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
          * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
        = (Ci * (CF + 1)) * (α ^ (-(1 / 2 : ℝ)) * α)
          * Work.FTS.Nonlin.Xn α g * max Ce 1 from by ring, hsqrt]
    ring
  have hS : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.sqrt_nonneg α) hXg
  have hfin : 2 * ((Ci * (CF + 1)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) * max Ce 1)
      ≤ (2 * (Ci * (CF + 1)) * max Ce 1 + 1)
          * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
    have hle : 2 * ((Ci * (CF + 1)) * max Ce 1)
        ≤ 2 * (Ci * (CF + 1)) * max Ce 1 + 1 := by linarith
    calc 2 * ((Ci * (CF + 1)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) * max Ce 1)
        = (2 * ((Ci * (CF + 1)) * max Ce 1))
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ (2 * (Ci * (CF + 1)) * max Ce 1 + 1)
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right hle hS
  calc 2 * Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Construction.Fstar α z θ
          * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ)
      ≤ 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
          * (max Ce 1 * Work.FTS.Nonlin.Xn α g)) :=
        mul_le_mul_of_nonneg_left hstep1 (by norm_num)
    _ = 2 * ((Ci * (CF + 1)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) * max Ce 1) := by
        rw [hkey]
    _ ≤ (2 * (Ci * (CF + 1)) * max Ce 1 + 1)
          * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := hfin

end Work.FTS.StrongEps.E4R3.N4C.rows
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowN1sg =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN2a =====
section

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
-- row 13 does not use the clause bundle `hE`; the hypothesis is kept for uniformity with row 12
-- (and with the frozen `NonlinRows.NRow13`).
set_option linter.unusedVariables false

/-! ## Two closure lemmas for `SmoothOpen` -/

private theorem smoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.mul hg

private theorem smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact contDiffOn_const.mul hf

/-! ## Row 12 — the pairing bound for `N₂^{gg}` -/

private theorem rowsN2aRow12 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N2gg α g Φg) g|
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
  obtain ⟨hCt, _hα₂⟩ := hE.pos
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ct * max Ce 1 + 1, ?_, ?_⟩
  · have : 0 < 2 * Ct * max Ce 1 := mul_pos (mul_pos (by norm_num) hCt) hmax
    linarith
  · intro α g Φs Φg hctx
    have hα : 0 < α := hctx.hα
    have hαα₂ : α ≤ α₂ := hctx.hαα₂
    have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
    have hsoG : Work.FTS.EllipticEst.SmoothOpen g := hctx.hSmoothOpen
    have hmem4G : Work.Spaces.HkMem α 4 g := hctx.hkMem4
    have hdecG : Work.Spaces.DecayAll 4 g := hctx.hdecay
    have hqoDth : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth g) := hctx.hqoDth
    have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
    -- the coefficient `coef = -2·(𝒰(Φ̃_g)/sin 2θ)` of the transport clause `t1`
    set coef : Fn := fun z θ => -2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg)
      z θ / Work.Construction.s2 θ) with hcoef
    have hcoefSm : Work.FTS.EllipticEst.SmoothOpen coef := by
      rw [hcoef]; exact smoothOpen_const_mul (-2) hell.U.1.1
    have hcoefHQo : Work.FTS.VocabO.HQo α 4 coef := by
      refine ⟨hcoefSm, ?_⟩
      rw [hcoef]
      exact Work.FTS.LocData.HkMem_const_mul α 4 (-2) hell.U.1.2
    -- the honest product `coef · D_θ g`, by the `ℋ⁴`-product rule
    have hprod := hN.prod α hIoc coef (Work.Spaces.Dth g) hcoefHQo hqoDth
    have hprodSm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => coef z θ * Work.Spaces.Dth g z θ) :=
      smoothOpen_mul hcoefSm hsoG.Dth
    -- the two functions agree on `(0,∞) × [0,π/2]`
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        (fun z θ => coef z θ * Work.Spaces.Dth g z θ) z θ
          = Work.FTS.Nonlin.N2gg α g Φg z θ := by
      intro z _hz θ hθ
      have hv1 : Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z 0 = 0 :=
        hell.vanishU.1 z
      have hv2 : Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z (π / 2) = 0 :=
        hell.vanishU.2 z
      have hsin : Real.sin (2 * (π / 2)) = 0 := by
        rw [show 2 * (π / 2) = Real.pi by ring, Real.sin_pi]
      simp only [hcoef, Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
        Work.Spaces.pth, Work.Construction.s2_eq]
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · -- `θ = 0`: both sides are `0`
        subst h0
        simp [hv1]
      · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
        · -- `θ = π/2`: both sides are `0`
          subst hpi
          simp [hv2, hsin]
        · -- interior: cancel `sin 2θ`
          have hs : Real.sin (2 * θ) ≠ 0 :=
            ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
          field_simp
    -- the `ℋ⁴`-honesty of `N₂^{gg}`, transferred from the honest product
    have hmemN2 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2gg α g Φg) :=
      Work.Coercivity.HkMem_congr_Ioi α 4 hprod.1 hpt
    -- and the `SmoothOpen`-honesty, likewise
    have hsoN2 : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2gg α g Φg) :=
      Work.FTS.EllipticEst.SmoothOpen.congr hprodSm
        (fun z θ hz hθ0 hθ1 =>
          hpt z (Set.mem_Ioi.mpr hz) θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩)
    -- `IP` only depends on the values on the open quadrant
    have hIPeq : IP α (Work.FTS.Nonlin.N2gg α g Φg) g
        = IP α (fun z θ => coef z θ * Work.Spaces.Dth g z θ) g := by
      refine hE.congr α hIoc _ _ g ⟨hsoN2, hmemN2⟩ ⟨hprodSm, hprod.1⟩ ⟨hsoG, hmem4G⟩ ?_
      intro z θ hQd
      exact (hpt z hQd.1 θ ⟨le_of_lt hQd.2.1, le_of_lt hQd.2.2⟩).symm
    rw [hIPeq]
    -- the transport clause `t1`
    have ht1 := hE.t1 α hIoc coef g hcoefHQo hsoG hmem4G hdecG
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hrp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    -- the norm of the coefficient
    have hXnCoef : Work.FTS.Nonlin.Xn α coef
        = 2 * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α
            (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ) := by
      rw [hcoef, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul]
      norm_num
    have hXc : Work.FTS.Nonlin.Xn α coef ≤ 2 * (max Ce 1 * Work.FTS.Nonlin.Xn α g) := by
      rw [hXnCoef]
      have hU2 : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ)
          ≤ Ce * Work.FTS.Nonlin.Xn α g := hell.U.2
      have hmaxle : Ce * Work.FTS.Nonlin.Xn α g ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
        mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg
      linarith [hU2, hmaxle]
    have hXc0 : 0 ≤ Work.FTS.Nonlin.Xn α coef := Work.Spaces.HkNorm_nonneg α 4 coef
    have hCt0 : 0 ≤ Ct := hCt.le
    have hmax0 : 0 ≤ max Ce 1 := hmax.le
    calc |IP α (fun z θ => coef z θ * Work.Spaces.Dth g z θ) g|
        ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α coef
            * Work.FTS.Nonlin.Xn α g ^ 2 := ht1
      _ ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Ce 1 * Work.FTS.Nonlin.Xn α g))
            * Work.FTS.Nonlin.Xn α g ^ 2 := by
          have h1 : 0 ≤ Ct * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCt0 hrp
          have h2 : 0 ≤ Work.FTS.Nonlin.Xn α g ^ 2 := sq_nonneg _
          have h3 : 0 ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Ce 1 * Work.FTS.Nonlin.Xn α g)) :=
            mul_nonneg h1 (mul_nonneg (by norm_num) (mul_nonneg hmax0 hXg))
          exact mul_le_mul (mul_le_mul_of_nonneg_left hXc h1) le_rfl h2 h3
      _ = (2 * Ct * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
          ring
      _ ≤ (2 * Ct * max Ce 1 + 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
          exact mul_le_mul_of_nonneg_right (by linarith)
            (mul_nonneg hrp (by positivity))

/-! ## Row 13 — the `ℋ⁴`-norm bound for `N₂^{g*}` -/

private theorem rowsN2aRow13 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg)
          ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨CF, hCF, hF⟩ := Work.FTS.Nonlin.DthFstar_W
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ci * CF * max Ce 1 + 1, ?_, ?_⟩
  · have hpos : 0 < 2 * Ci * CF * max Ce 1 :=
      mul_pos (mul_pos (mul_pos (by norm_num) hCi) hCF) hmax
    linarith
  · intro α g Φs Φg hctx
    have hα : 0 < α := hctx.hα
    have hα1 : α ≤ 1 := hctx.hα1
    have hαα₂ : α ≤ α₂ := hctx.hαα₂
    have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
    have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
    -- the `ℋ⁴`-coefficient `c = U(Φ̃_g)/sin 2θ` of the elliptic package
    set c : Fn := fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
      / Work.Construction.s2 θ with hc
    have hcHQo : Work.FTS.VocabO.HQo α 4 c := by
      rw [hc]
      simpa only [Work.FTS.Nonlin.PhiTg] using hell.U.1
    have hcB : Work.FTS.Nonlin.Xn α c ≤ Ce * Work.FTS.Nonlin.Xn α g := by
      rw [hc]
      simpa only [Work.FTS.Nonlin.PhiTg] using hell.U.2
    -- `D_θF_*` is smooth on the open quadrant and in `𝒲^{4,∞}` with norm `≤ CF·α²`
    have hFsmooth : Work.FTS.EllipticEst.SmoothOpen
        (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)).Dth
    obtain ⟨hFWmem, hFWle⟩ := hF α hα hα1
    -- the `𝒲^{4,∞}`-priced product rule
    have hprod := hN.wprod α hIoc (Work.Spaces.Dth (Work.Construction.Fstar α)) c
      hFsmooth hFWmem hcHQo
    -- the honest representative `P = D_θF_* · c`
    set P : Fn := fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ * c z θ with hP
    have hPmem : Work.Spaces.HkMem α 4 P := by
      rw [hP]
      exact hprod.1
    -- `N₂^{g*} = -2·P` on `(0,∞) × [0,π/2]`
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        Work.FTS.Nonlin.N2gs α g Φg z θ = -2 * P z θ := by
      intro z _hz θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · -- `θ = 0`: both sides vanish, `U(Φ̃_g)(·,0) = 0`
        subst h0
        simp only [hP, hc, Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
          Work.Construction.s2_eq]
        simp [hell.vanishU.1 z]
      · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
        · -- `θ = π/2`: both sides vanish, `U(Φ̃_g)(·,π/2) = 0`
          subst hpi
          simp only [hP, hc, Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
            Work.Construction.s2_eq]
          simp [hell.vanishU.2 z]
        · -- interior: cancel `sin 2θ`
          have hsin2 : Real.sin (2 * θ) ≠ 0 := by
            intro hzero
            have hsinpos : 0 < Real.sin θ :=
              Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_pos])
            have hcospos : 0 < Real.cos θ :=
              Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩
            rw [Real.sin_two_mul] at hzero
            nlinarith [mul_pos hsinpos hcospos]
          simp only [hP, hc, Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
            Work.Construction.s2_eq]
          field_simp
    -- the `ℋ⁴`-honesty of `N₂^{g*}`, transferred from the honest representative
    have hmem : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2gs α g Φg) :=
      Work.Coercivity.HkMem_congr_Ioi α 4
        (Work.FTS.LocData.HkMem_const_mul α 4 (-2) hPmem)
        (fun z hz θ hθ => (hpt z hz θ hθ).symm)
    -- the norm only sees the open quadrant, so `|N₂^{g*}| = 2·|P|`
    have hXn_eq : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg)
        = 2 * Work.FTS.Nonlin.Xn α P := by
      have hcong : Work.FTS.Nonlin.Xn α (fun z θ => -2 * P z θ)
          = Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg) := by
        change Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => -2 * P z θ))
          = Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N2gs α g Φg))
        rw [Work.FTS.EllipticEst.HkSq_congr_open α 4
            (fun z θ hz hθ hlt =>
              (hpt z (Set.mem_Ioi.mpr hz) θ ⟨le_of_lt hθ, le_of_lt hlt⟩).symm)]
      have htwo : Work.FTS.Nonlin.Xn α (fun z θ => -2 * P z θ)
          = 2 * Work.FTS.Nonlin.Xn α P := by
        rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-2) P,
          abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
        norm_num
      exact hcong.symm.trans htwo
    rw [hXn_eq]
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hXc : 0 ≤ Work.FTS.Nonlin.Xn α c := Work.Spaces.HkNorm_nonneg α 4 c
    have hrp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have hCnn : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCi.le hrp
    have hcB' : Work.FTS.Nonlin.Xn α c ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
      le_trans hcB (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg)
    have hXnP : Work.FTS.Nonlin.Xn α P
        ≤ Ci * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
          * Work.FTS.Nonlin.Xn α c := by
      rw [hP]
      exact hprod.2
    have hstep : Work.FTS.Nonlin.Xn α P
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
          * (max Ce 1 * Work.FTS.Nonlin.Xn α g) := by
      refine le_trans hXnP (mul_le_mul ?_ hcB' hXc ?_)
      · exact mul_le_mul_of_nonneg_left hFWle hCnn
      · exact mul_nonneg hCnn (mul_nonneg hCF.le (sq_nonneg α))
    have hrpow : α ^ (-(1 / 2 : ℝ)) * α ^ 2 = α ^ (3 / 2 : ℝ) := by
      rw [show α ^ 2 = α ^ (2 : ℝ) by norm_num]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (2 : ℝ)
      rw [show -(1 / 2 : ℝ) + 2 = 3 / 2 by norm_num] at h
      exact h.symm
    calc 2 * Work.FTS.Nonlin.Xn α P
        ≤ 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
            * (max Ce 1 * Work.FTS.Nonlin.Xn α g)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = (2 * Ci * CF * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * α ^ 2)
            * Work.FTS.Nonlin.Xn α g := by ring
      _ = (2 * Ci * CF * max Ce 1)
            * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
          rw [hrpow]
          ring
      _ ≤ (2 * Ci * CF * max Ce 1 + 1)
            * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
          refine mul_le_mul_of_nonneg_right (by linarith) ?_
          exact mul_nonneg (Real.rpow_nonneg hα.le _) hXg

/-! ## The two rows, with a single constant -/

theorem rowsN2a (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N2gg α g Φg) g|
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg)
          ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨K1, hK1, h1⟩ := rowsN2aRow12 IP hN hE
  obtain ⟨K2, hK2, h2⟩ := rowsN2aRow13 IP hN hE
  refine ⟨K1 + K2 + 1, by linarith, ?_⟩
  intro α g Φs Φg hctx
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA1 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hctx.hα.le _) (by positivity)
  have hA2 : 0 ≤ α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.rpow_nonneg hctx.hα.le _) hX
  exact ⟨(h1 hctx).trans (mul_le_mul_of_nonneg_right (by linarith) hA1),
    (h2 hctx).trans (mul_le_mul_of_nonneg_right (by linarith) hA2)⟩

end Work.FTS.StrongEps.E4R3.N4C.rows
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN3a =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `SmoothOpen` is closed under products (interior `C^∞` on the open quadrant). -/
theorem so_mul_rowsN3a {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  convert hf.mul hg using 1
  ext p
  rfl

/-- **Rows 16 and 17 of the honest §8 table.**

Constant `K = max (8·Ct·max Ce 1 + 1) (2·Ci·(CF + 1)·max Ce 1 + 1)`, where `CF` is the constant
of `Nonlin.DzFstar_W`; the two summands are the constants of the two rows. -/
theorem rowsN3a (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N3gg α g Φg) g| ≤ K * Work.FTS.Nonlin.Xn α g ^ 3 ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3gs α g Φg)
          ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  have hCt : 0 < Ct := hE.pos.1
  obtain ⟨hCi, _hα₂pos⟩ := hN.pos
  obtain ⟨CF, _hCF, hDzF⟩ := Work.FTS.Nonlin.DzFstar_W
  have hCmax : 0 ≤ max Ce 1 := le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right Ce 1))
  refine ⟨max (8 * Ct * max Ce 1 + 1) (2 * Ci * (CF + 1) * max Ce 1 + 1),
    lt_max_of_lt_left (by positivity), ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hαα₂ : α ≤ α₂ := hctx.hαα₂
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  constructor
  · -- ---------- row 16 : `|(N₃^{gg}, g)| ≤ K X³` ----------
    have hVnorm : Work.FTS.Nonlin.Xn α
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) ≤ Ce * Work.FTS.Nonlin.Xn α g :=
      hctx.hell.V.2
    have hVthb : Work.FTS.VocabO.CoefTh 1
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g := hctx.hell.Vth.2
    -- the `g`-side slot `D_z g ∈ ℋ⁴`
    have hDzMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) := hctx.hkMemDz
    have hDzSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hctx.hSmoothOpen.Dz
    -- the product `V(Φ̃_g)·D_z g` is in `ℋ⁴`
    have hprod := (hN.prod α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
      (Work.Spaces.Dz g) hctx.hell.V.1 ⟨hDzSm, hDzMem⟩).1
    have hprodQ : Work.FTS.VocabO.HQo α 4 (fun z θ =>
        Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ * Work.Spaces.Dz g z θ) :=
      ⟨so_mul_rowsN3a hctx.hell.V.1.1 hDzSm, hprod⟩
    -- `N₃^{gg}` is `-2α` times that product
    have hN3 : Work.FTS.Nonlin.N3gg α g Φg
        = fun z θ => (-2 * α) * (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
            * Work.Spaces.Dz g z θ) := by
      funext z θ
      simp only [Work.FTS.Nonlin.N3gg]
      ring
    have hIPeq : IP α (Work.FTS.Nonlin.N3gg α g Φg) g
        = (-2 * α) * IP α (fun z θ =>
            Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
              * Work.Spaces.Dz g z θ) g := by
      rw [hN3]
      exact hE.smul α hIoc (-2 * α) _ g hprodQ hctx.hqo4
    rw [hIPeq]
    have habs : |(-2 : ℝ) * α| = 2 * α := by
      rw [abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]
      ring
    rw [abs_mul, habs]
    -- the `D_z`-transport estimate for the coefficient `V(Φ̃_g)`
    have ht2 := hE.t2 α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) g
      hctx.hell.V.1.1 hctx.hell.V.1.2 hctx.hell.Vth.1
      hctx.hSmoothOpen hctx.hkMem4 hctx.hkMem5 hctx.hdecay
    refine (mul_le_mul_of_nonneg_left ht2 (by linarith : (0 : ℝ) ≤ 2 * α)).trans ?_
    -- the two coefficient norms, in terms of `X = |g|_{ℋ⁴}`
    have h1 : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
      hVnorm.trans (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hX0)
    have h2 : Work.FTS.VocabO.CoefTh 1
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ max Ce 1 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g :=
      hVthb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hA0) hX0)
    -- `α·α^{-1/2} ≤ 1` and `α·α^{-1/2}·α^{-1/2} = 1`
    have hαhalf : α * α ^ (-(1 / 2 : ℝ)) = α ^ (1 / 2 : ℝ) := by
      calc α * α ^ (-(1 / 2 : ℝ)) = α ^ (1 : ℝ) * α ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ = α ^ ((1 : ℝ) + -(1 / 2)) := (Real.rpow_add hα 1 (-(1 / 2))).symm
        _ = α ^ (1 / 2 : ℝ) := by norm_num
    have hhalf_le : α ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
    have hA1 : α ^ (1 / 2 : ℝ) * α ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hα (1 / 2) (-(1 / 2)),
        show (1 / 2 : ℝ) + -(1 / 2) = 0 by norm_num, Real.rpow_zero]
    have hAA : α * α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [hαhalf, hA1]
    -- the weighted sum of the two coefficient norms
    have hsum_bound : α * α ^ (-(1 / 2 : ℝ))
        * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
          + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)))
        ≤ 2 * (max Ce 1) * Work.FTS.Nonlin.Xn α g := by
      have e1 : α * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
          ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g := by
        calc α * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
            ≤ α * α ^ (-(1 / 2 : ℝ)) * (max Ce 1 * Work.FTS.Nonlin.Xn α g) :=
              mul_le_mul_of_nonneg_left h1 (mul_nonneg hα.le hA0)
          _ = max Ce 1 * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by
              rw [hαhalf]
              ring
          _ ≤ max Ce 1 * 1 * Work.FTS.Nonlin.Xn α g := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf_le hCmax) hX0
          _ = max Ce 1 * Work.FTS.Nonlin.Xn α g := by ring
      have e2 : α * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
          ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g := by
        calc α * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
            ≤ α * α ^ (-(1 / 2 : ℝ))
              * (max Ce 1 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g) :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg hα.le hA0)
          _ = max Ce 1 * (α * α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 / 2 : ℝ)))
              * Work.FTS.Nonlin.Xn α g := by ring
          _ = max Ce 1 * 1 * Work.FTS.Nonlin.Xn α g := by rw [hAA]
          _ = max Ce 1 * Work.FTS.Nonlin.Xn α g := by ring
      linarith [add_le_add e1 e2]
    -- the final arithmetic
    have hkey : 2 * α * (Ct * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
            + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)))
          * Work.FTS.Nonlin.Xn α g ^ 2)
        ≤ (8 * Ct * max Ce 1 + 1) * Work.FTS.Nonlin.Xn α g ^ 3 := by
      have hre : 2 * α * (Ct * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
              + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)))
            * Work.FTS.Nonlin.Xn α g ^ 2)
          = 2 * Ct * (α * α ^ (-(1 / 2 : ℝ))
              * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
                + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))))
            * Work.FTS.Nonlin.Xn α g ^ 2 := by ring
      rw [hre]
      calc 2 * Ct * (α * α ^ (-(1 / 2 : ℝ))
              * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
                + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))))
            * Work.FTS.Nonlin.Xn α g ^ 2
          ≤ 2 * Ct * (2 * (max Ce 1) * Work.FTS.Nonlin.Xn α g) * Work.FTS.Nonlin.Xn α g ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hX0 2)
            exact mul_le_mul_of_nonneg_left hsum_bound (mul_nonneg (by norm_num) hCt.le)
        _ = 4 * Ct * max Ce 1 * Work.FTS.Nonlin.Xn α g ^ 3 := by ring
        _ ≤ (8 * Ct * max Ce 1 + 1) * Work.FTS.Nonlin.Xn α g ^ 3 := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hX0 3)
            linarith [mul_nonneg hCt.le hCmax]
    exact hkey.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hX0 3))
  · -- ---------- row 17 : `|N₃^{gs}|_{ℋ⁴} ≤ K α^{3/2} X` ----------
    -- the `𝒲^{4,∞}`-factor `D_z F_*`, with norm `≤ C α`
    obtain ⟨hDzWmem, hDzWle⟩ := hDzF α hα hα1
    have hDzsmooth : Work.FTS.EllipticEst.SmoothOpen
        (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
      Work.FTS.OpenPkg.smoothOpen_of_smoothQuad
        (Work.FTS.LocData.SmoothQuad.DzIter (Work.FTS.LocData.SmoothQuad_Fstar α) 1)
    have hW' : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
        ≤ (CF + 1) * α :=
      le_trans hDzWle (mul_le_mul_of_nonneg_right (by linarith) hα.le)
    -- the `ℋ⁴`-factor `V(Φ̃_g)`, with norm `≤ Ce X`
    have hVreg : Work.FTS.VocabO.HQo α 4
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) := hctx.hell.V.1
    have hVB : Work.FTS.Nonlin.Xn α
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) ≤ Ce * Work.FTS.Nonlin.Xn α g :=
      hctx.hell.V.2
    have hV' : Work.FTS.Nonlin.Xn α
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
      le_trans hVB (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hX0)
    -- the mixed product rule
    have hprod := (hN.wprod α hIoc (Work.Spaces.Dz (Work.Construction.Fstar α))
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) hDzsmooth hDzWmem hVreg).2
    have hbound : Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Spaces.Dz (Work.Construction.Fstar α) z θ
            * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
          * (max Ce 1 * Work.FTS.Nonlin.Xn α g) := by
      refine hprod.trans ?_
      refine mul_le_mul ?_ hV' (Work.Spaces.HkNorm_nonneg α 4 _) ?_
      · exact mul_le_mul_of_nonneg_left hW' (mul_nonneg hCi.le hA0)
      · exact mul_nonneg (mul_nonneg hCi.le hA0) (mul_nonneg (by linarith) hα.le)
    -- `N₃^{gs}` is `(-2α)` times that product
    have hN3 : Work.FTS.Nonlin.N3gs α g Φg = fun z θ => (-2 * α) *
        (Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ) := by
      funext z θ
      simp only [Work.FTS.Nonlin.N3gs]
      ring
    have hXeq : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3gs α g Φg)
        = 2 * α * Work.FTS.Nonlin.Xn α (fun z θ =>
            Work.Spaces.Dz (Work.Construction.Fstar α) z θ
              * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ) := by
      rw [hN3, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-2 * α)
        (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ),
        abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]
      ring
    rw [hXeq]
    refine le_trans (mul_le_mul_of_nonneg_left hbound (by linarith)) ?_
    -- `α · α^{-1/2} · α = α^{3/2}`
    have hpow : α * α ^ (-(1 / 2 : ℝ)) * α = α ^ (3 / 2 : ℝ) := by
      have hz : α * α ^ (-(1 / 2 : ℝ)) = Real.sqrt α := by
        rw [Real.sqrt_eq_rpow]
        have h := Real.rpow_add hα (1 : ℝ) (-(1 / 2))
        rw [Real.rpow_one, show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num] at h
        exact h.symm
      have h32 : α ^ (3 / 2 : ℝ) = α * Real.sqrt α := by
        rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num, Real.rpow_add hα 1 (1 / 2),
          Real.rpow_one, Real.sqrt_eq_rpow]
      rw [h32, hz]; ring
    have harith : 2 * α * (Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
          * (max Ce 1 * Work.FTS.Nonlin.Xn α g))
        = 2 * Ci * (CF + 1) * max Ce 1 * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
      rw [← hpow]
      ring
    rw [harith]
    refine le_trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (mul_nonneg (Real.rpow_nonneg hα.le _) hX0)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (mul_nonneg (Real.rpow_nonneg hα.le _) hX0)

end Work.FTS.StrongEps.E4R3.N4C.rows
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.mixed_Jeps_tendstoUniformlyOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

noncomputable section

open scoped Real Topology
open Filter MeasureTheory Set

/-- **The slots of `J_ε G_ε` converge uniformly to the slots of the limit.**

The proof is the standard mollifier argument, in three pieces:

* `mixed_Jeps` (E1) turns the slot of the mollified profile into the mollified slot:
  `D_z^jD_θ^i (J_ε G_n) = J_ε (D_z^jD_θ^i G_n)` on the open quadrant;
* the slot error `D_z^jD_θ^i G_n - D_z^jD_θ^i f` is estimated by its supremum on a compact
  neighbourhood `S` of `K` which contains all points at which the mollifier samples the profile
  (`abs_Jeps_sub_Jeps_le_of_bound`);
* the remaining error `J_ε (D_z^jD_θ^i f) - D_z^jD_θ^i f` is the peak estimate for the *fixed*
  continuous profile `D_z^jD_θ^i f` (`jeps_tendstoUniformlyOn_of_continuousOn_of_shift`), whose
  uniform version needs the uniform continuity of the shift `sPhi` on `K`
  (`exists_dist_sPhi_le`) and the local uniformity of `K` inside the open quadrant.

The neighbourhood `S` is the closed thickening `cthickening δ₀ K`, with `δ₀` chosen so small that
`S` stays inside the open quadrant: for `ε n ≤ δ₁` (where `δ₁` is the modulus of `sPhi` on `K`
for the tolerance `δ₀`) every sampled point `sPhi p q` lies in `S`, where the slots of the
sequence converge uniformly by `hconv`. -/
theorem mixed_Jeps_tendstoUniformlyOn {ρ : ℝ × ℝ → ℝ}
    (hmoll : Work.FTS.StrongEps.IsMollKernel ρ)
    {α B : ℝ} {G : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ} {ε : ℕ → ℝ}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n)) Work.FTS.EllipticEst.Q0)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B G f)
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ 4) :
    TendstoUniformlyOn
      (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed j i
        (Work.FTS.StrongEps.Jeps ρ (ε n) (G n)) p.1 p.2)
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K := by
  classical
  -- the slots `D_z^jD_θ^i G_n`, as functions on `ℝ × ℝ`, are continuous on the open quadrant
  have hcontG : ∀ n : ℕ,
      ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i (G n) q.1 q.2)
        Work.FTS.StrongEps.Quad := fun n =>
    contDiffOn_zero.mp (contDiffOn_zero_mixed_le (G := G n) (n := j + i) (j := j) (i := i)
      (hsm n (j + i)) le_rfl)
  have hcontf : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2)
      Work.FTS.StrongEps.Quad :=
    contDiffOn_zero.mp (contDiffOn_zero_mixed_le (G := f) (n := 4) (j := j) (i := i)
      hconv.contDiffOn hji)
  -- a compact neighbourhood `S` of `K` inside the open quadrant
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ :=
    hK.exists_cthickening_subset_open Work.FTS.EllipticEst.isOpen_Q0 hKQ
  set S : Set (ℝ × ℝ) := Metric.cthickening δ₀ K with hS
  have hSc : IsCompact S := by
    rw [hS]
    exact hK.cthickening
  have hSQ : S ⊆ Work.FTS.EllipticEst.Q0 := by
    rw [hS]
    exact hδ₀sub
  -- the uniform convergence of the slots on the larger compact set
  have hslot := hconv.conv S hSc hSQ j i hji
  -- the uniform continuity of the shift on `K`
  have hshift : ∀ η > 0, ∃ δ > 0, ∀ p ∈ K, ∀ q : ℝ × ℝ, ‖q‖ ≤ δ →
      dist (Work.FTS.StrongEps.sPhi p.1 p.2 q) p ≤ η :=
    fun η hη => exists_dist_sPhi_le hK hKQ hη
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hshift δ₀ hδ₀pos
  -- the peak estimate for the fixed profile `D_z^jD_θ^i f`
  have hpeak := jeps_tendstoUniformlyOn_of_continuousOn_of_shift hmoll hεpos hε0 hcontf hK hKQ hshift
  rw [Metric.tendstoUniformlyOn_iff] at hslot hpeak ⊢
  intro η hη
  have h2 : 0 < η / 2 := by linarith
  have hA := hslot (η / 2) h2
  have hB := hpeak (η / 2) h2
  have hε1 : ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ δ₁ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hε0 δ₁ hδ₁pos
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    have h' := abs_lt.mp h
    linarith [h'.2]
  filter_upwards [hA, hB, hε1] with n hnA hnB hnε1
  intro p hpK
  have hpQ : (p.1, p.2) ∈ Work.FTS.StrongEps.Quad := hKQ hpK
  have hz : 0 < p.1 := hpQ.1
  have hth : p.2 ∈ Set.Ioo 0 (π / 2) := hpQ.2
  -- (E1): the slot of the mollified profile is the mollified slot
  have hcomm : Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ (ε n) (G n)) p.1 p.2
      = Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i (G n)) p.1 p.2 :=
    Work.FTS.StrongEps.mixed_Jeps ρ hmoll (hεpos n) (hsm n) hz hth j i
  -- the slot error, estimated on the compact neighbourhood `S`
  have hA' : |Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i (G n)) p.1 p.2
      - Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i f) p.1 p.2| ≤ η / 2 := by
    refine abs_Jeps_sub_Jeps_le_of_bound hmoll hz hth (hεpos n) (hcontG n) hcontf ?_
    intro q hq
    have hxS : Work.FTS.StrongEps.sPhi p.1 p.2 q ∈ S := by
      rw [hS]
      exact Metric.mem_cthickening_of_dist_le _ p δ₀ K hpK
        (hδ₁ p hpK q (le_trans hq hnε1))
    have h := hnA _ hxS
    rw [dist_comm, Real.dist_eq] at h
    exact le_of_lt (by simpa only [Work.FTS.StrongEps.sPhi] using h)
  -- the peak estimate for the limit slot
  have hB' : dist (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i f) p.1 p.2)
      (Work.Spaces.mixed j i f p.1 p.2) < η / 2 := by
    rw [dist_comm]
    exact hnB p hpK
  -- assemble
  rw [dist_comm]
  calc dist (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ (ε n) (G n)) p.1 p.2)
        (Work.Spaces.mixed j i f p.1 p.2)
      = dist (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i (G n)) p.1 p.2)
          (Work.Spaces.mixed j i f p.1 p.2) := by rw [hcomm]
    _ ≤ dist (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i (G n)) p.1 p.2)
          (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i f) p.1 p.2)
        + dist (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i f) p.1 p.2)
          (Work.Spaces.mixed j i f p.1 p.2) := dist_triangle _ _ _
    _ < η / 2 + η / 2 := add_lt_add_of_le_of_lt (by rw [Real.dist_eq]; exact hA') hB'
    _ = η := by ring

end

end Work.FTS.StrongEps.E5Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.Jker_shift_logsubst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open MeasureTheory

/-- The reflection `x ↦ c - x` does not change the Lebesgue `lintegral` on `ℝ`: it is the
composition of the translation `x ↦ x + c` (invariance: `lintegral_add_right_eq_self`) with the
negation `x ↦ -x` (invariance: `lintegral_neg_eq_self`). -/
private lemma lintegral_add_neg_eq_self (F : ℝ → ENNReal) (c : ℝ) :
    (∫⁻ s, F (c + -s)) = ∫⁻ s, F s := by
  rw [MeasureTheory.lintegral_neg_eq_self (fun y => F (c + y))]
  rw [show (∫⁻ s, F (c + s)) = ∫⁻ s, F (s + c) from
    MeasureTheory.lintegral_congr (fun s => by rw [add_comm])]
  exact MeasureTheory.lintegral_add_right_eq_self F c

/-- The two-dimensional form of the previous lemma. -/
private lemma lintegral_prod_neg_sub (F : ℝ → ℝ → ENNReal) (c d : ℝ) :
    (∫⁻ s, ∫⁻ ζ, F (c - s) (d - ζ)) = ∫⁻ s, ∫⁻ ζ, F s ζ := by
  have hinner : ∀ s, (∫⁻ ζ, F (c - s) (d - ζ)) = ∫⁻ ζ, F (c - s) ζ := by
    intro s
    simpa only [sub_eq_add_neg] using lintegral_add_neg_eq_self (fun ζ => F (c - s) ζ) d
  rw [MeasureTheory.lintegral_congr hinner]
  simpa only [sub_eq_add_neg] using lintegral_add_neg_eq_self (fun s => ∫⁻ ζ, F s ζ) c

/-- The angular Jacobian identity behind the log-coordinate substitution: the derivative of
`θ ↦ log tan θ` is `2 / sin (2θ)`, and in the coordinate `ζ = log tan θ` (`θ = arctan (e^ζ)`)
this reads `sin (2 · arctan (e^ζ)) = 2 · kappa ζ`, where `kappa ζ = e^ζ/(1 + e^{2ζ})` is the
derivative of `ζ ↦ arctan (e^ζ)`. -/
private lemma sin_two_arctan_exp (ζ : ℝ) :
    Real.sin (2 * Real.arctan (Real.exp ζ)) = 2 * Work.FTS.StrongEps.HkSqAux.kappa ζ := by
  have hpos : 0 < 1 + (Real.exp ζ) ^ 2 := by positivity
  have hsq : (Real.sqrt (1 + (Real.exp ζ) ^ 2)) ^ 2 = 1 + Real.exp (2 * ζ) := by
    rw [Real.sq_sqrt hpos.le]
    congr 1
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan, Work.FTS.StrongEps.HkSqAux.kappa,
    div_eq_mul_inv, div_eq_mul_inv, ← hsq]
  have hne : Real.sqrt (1 + (Real.exp ζ) ^ 2) ≠ 0 := by positivity
  field_simp

/-- The Jacobian of the log-coordinate substitution `(z, θ) ↦ (log z, log tan θ)` cancels the
weight `2 / (z sin 2θ)` of the quadrant integral. -/
private lemma logJac_mul_weight (s ζ : ℝ) :
    Work.FTS.StrongEps.HkSqAux.logJac s ζ
      * (2 / (Real.exp s * Real.sin (2 * Real.arctan (Real.exp ζ)))) = 1 := by
  rw [Work.FTS.StrongEps.HkSqAux.logJac, sin_two_arctan_exp, div_eq_mul_inv]
  have hk0 : Work.FTS.StrongEps.HkSqAux.kappa ζ ≠ 0 :=
    ne_of_gt (Work.FTS.StrongEps.HkSqAux.kappa_pos ζ)
  have he : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  field_simp


end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option linter.style.haveILetI false

namespace Work.FTS.StrongEps.EpsLocalPStar.VolterraAux

set_option maxHeartbeats 1000000

theorem EpsMem_and_EpsSq_intervalIntegral_le {α τ B : ℝ} (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    {G : ℝ → Work.FTS.Galerkin.Fn}
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2 * Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM))
    (hbd : Filter.Eventually (fun s : ℝ =>
        Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (G s) ≤ ENNReal.ofReal B)
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.uIoc 0 τ)))) :
    Work.FTS.StrongEps.EpsMem α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ) ≤ τ * (τ * B) := by
  classical
  -- the uncurried weighted curve, in the shape in which `hmeas` is stated
  set X : ℝ × (ℝ × ℝ) → ℝ :=
    fun q => G q.1 q.2.1 q.2.2 * Work.FTS.StrongEps.epsW α q.2.1 q.2.2 with hX
  have hmeas' : MeasureTheory.AEStronglyMeasurable X
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM) := hmeas
  -- the interval integral of a profile is the integral of its weighted slice against
  -- `volume.restrict (uIoc 0 τ)`, the weight being constant in the parameter
  have hint_eq : ∀ p : ℝ × ℝ, (∫ s in (0 : ℝ)..τ, G s p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2
      = ∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)) := by
    intro p
    rw [intervalIntegral.integral_of_le hτ, Set.uIoc_of_le hτ, hX]
    exact (MeasureTheory.integral_mul_const (Work.FTS.StrongEps.epsW α p.1 p.2)
      (fun s => G s p.1 p.2)).symm
  -- the parameter measure is finite, of total mass `τ`
  haveI hνfin : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc,
      sub_zero, abs_of_nonneg hτ]
    exact ENNReal.ofReal_lt_top⟩
  have hnu : (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ = ENNReal.ofReal τ := by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc,
      sub_zero, abs_of_nonneg hτ]
  have hnu_ne : (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ ≠ ⊤ := by
    rw [hnu]; exact ENNReal.ofReal_ne_top
  -- a.e. strong measurability of the weighted parametric integral
  have hAK : AK2 α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ) := by
    unfold AK2
    refine (hmeas'.prod_swap.integral_prod_right').congr ?_
    filter_upwards with p
    exact (hint_eq p).symm
  -- `epsL2` of the parametric integral, in terms of the `s`-integral of the curve
  have hstep1 : epsL2 α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ)
      = ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2)
          ∂Work.FTS.StrongEps.EpsLocalPStar.DomM := by
    unfold epsL2
    exact lintegral_congr (fun p => by rw [hint_eq p])
  -- Cauchy–Schwarz in the parameter, pointwise in the profile variable
  have hpt : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
      ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2)
        ≤ (∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
          * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) := by
    filter_upwards [hmeas'.prodMk_right] with p hp
    have hen : ENNReal.ofReal |∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ))|
        ≤ ∫⁻ s, ENNReal.ofReal |X (s, p)| ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)) := by
      have h := enorm_integral_le_lintegral_enorm
        (μ := MeasureTheory.volume.restrict (Set.uIoc 0 τ)) (fun s => X (s, p))
      simpa [Real.enorm_eq_ofReal_abs] using h
    have hcs := l2_cs (ν := MeasureTheory.volume.restrict (Set.uIoc 0 τ)) (b := fun _ => (1 : ℝ))
      aemeasurable_const (fun _ => one_pos) hp.aemeasurable
    calc ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2)
        = (ENNReal.ofReal |∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ))|)^2 :=
          ofReal_sq_abs _
      _ ≤ (∫⁻ s, ENNReal.ofReal |X (s, p)| ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2 :=
          pow_le_pow_left₀ bot_le hen 2
      _ ≤ (∫⁻ s, ENNReal.ofReal (X (s, p)^2 / 1) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * (∫⁻ s, ENNReal.ofReal (1 : ℝ) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ))) := hcs
      _ = (∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) := by
          simp only [div_one, ENNReal.ofReal_one, lintegral_one]
  -- joint measurability for Tonelli
  have hjoint : AEMeasurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal ((X (q.2, q.1))^2))
      ((Work.FTS.StrongEps.EpsLocalPStar.DomM).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 τ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hmeas'.prod_swap.aemeasurable).pow_const 2)
  -- the chain: Cauchy–Schwarz, Tonelli, the a.e. bound, and the arithmetic
  have hchain : ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2)
      ∂Work.FTS.StrongEps.EpsLocalPStar.DomM ≤ ENNReal.ofReal (τ * (τ * B)) := by
    calc ∫⁻ p, ENNReal.ofReal ((∫ s, X (s, p) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))^2)
        ∂Work.FTS.StrongEps.EpsLocalPStar.DomM
        ≤ ∫⁻ p, (∫⁻ s, ENNReal.ofReal ((X (s, p))^2)
              ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ)
            ∂Work.FTS.StrongEps.EpsLocalPStar.DomM := lintegral_mono_ae hpt
      _ = (∫⁻ p, ∫⁻ s, ENNReal.ofReal ((X (s, p))^2) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ))
            ∂Work.FTS.StrongEps.EpsLocalPStar.DomM)
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) := by
          rw [MeasureTheory.lintegral_mul_const' _ _ hnu_ne]
      _ = (∫⁻ s, ∫⁻ p, ENNReal.ofReal ((X (s, p))^2) ∂Work.FTS.StrongEps.EpsLocalPStar.DomM
            ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) := by
          rw [MeasureTheory.lintegral_lintegral_swap hjoint]
      _ = (∫⁻ s, epsL2 α (G s) ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) := by
          congr 1
      _ ≤ (∫⁻ s, ENNReal.ofReal B ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)))
            * ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)) Set.univ) :=
          mul_le_mul_of_nonneg_right (lintegral_mono_ae hbd) bot_le
      _ = ENNReal.ofReal (τ * (τ * B)) := by
          rw [MeasureTheory.lintegral_const, hnu, ← ENNReal.ofReal_mul hB,
            ← ENNReal.ofReal_mul (mul_nonneg hB hτ)]
          congr 1
          ring
  -- membership and the size bound out of the `epsL2`-bound
  refine EpsMem_and_EpsSq_le_of_epsL2_le (mul_nonneg hτ (mul_nonneg hτ hB)) hAK ?_
  rw [hstep1]
  exact hchain

end Work.FTS.StrongEps.EpsLocalPStar.VolterraAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_le_of_tendsto_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar.VolterraAux

theorem EpsMem_and_EpsSq_le_of_tendsto_ae {α B : ℝ} (hB : 0 ≤ B)
    {A : ℕ → Work.FTS.Galerkin.Fn} {Alim : Work.FTS.Galerkin.Fn}
    (hAK : ∀ m : ℕ, Work.FTS.StrongEps.EpsLocalPStar.AK2 α (A m))
    (hbd : ∀ m : ℕ, Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (A m) ≤ ENNReal.ofReal B)
    (hlim : Filter.Eventually (fun p : ℝ × ℝ =>
        Filter.Tendsto (fun m : ℕ => A m p.1 p.2) Filter.atTop (nhds (Alim p.1 p.2)))
      (MeasureTheory.ae Work.FTS.StrongEps.EpsLocalPStar.DomM)) :
    Work.FTS.StrongEps.EpsMem α Alim ∧ Work.FTS.StrongEps.EpsSq α Alim ≤ B := by
  -- the weighted sequence converges a.e. to the weighted limit
  have hlimW : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
      Filter.Tendsto (fun m : ℕ => A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
        Filter.atTop (nhds (Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)) :=
    hlim.mono fun p hp => hp.mul_const _
  -- hence the limit is a.e. strongly measurable as well
  have hAKlim : Work.FTS.StrongEps.EpsLocalPStar.AK2 α Alim :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop hAK hlimW
  refine Work.FTS.StrongEps.EpsLocalPStar.EpsMem_and_EpsSq_le_of_epsL2_le hB hAKlim ?_
  -- Fatou: `epsL2` of the limit is at most the `liminf` of the `epsL2`'s of the sequence
  have hmeas : ∀ m : ℕ, AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
      Work.FTS.StrongEps.EpsLocalPStar.DomM := fun m =>
    (((hAK m).pow 2).aemeasurable).ennreal_ofReal
  have hpt : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
      ENNReal.ofReal ((Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ≤ Filter.liminf (fun m : ℕ =>
            ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
          Filter.atTop := by
    filter_upwards [hlimW] with p hp
    have h1 : Filter.Tendsto (fun m : ℕ =>
        ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))
        Filter.atTop
        (nhds (ENNReal.ofReal ((Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto
        ((Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)).comp (hp.pow 2)
    rw [h1.liminf_eq]
  have hfatou : (∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal ((Alim p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ∂Work.FTS.StrongEps.EpsLocalPStar.DomM)
      ≤ Filter.liminf (fun m : ℕ => ∫⁻ p : ℝ × ℝ,
            ENNReal.ofReal ((A m p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
            ∂Work.FTS.StrongEps.EpsLocalPStar.DomM) Filter.atTop :=
    (MeasureTheory.lintegral_mono_ae hpt).trans (MeasureTheory.lintegral_liminf_le' hmeas)
  have hb : Filter.liminf (fun m : ℕ => Work.FTS.StrongEps.EpsLocalPStar.epsL2 α (A m))
      Filter.atTop ≤ ENNReal.ofReal B :=
    Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hbd)
  exact hfatou.trans hb

end Work.FTS.StrongEps.EpsLocalPStar.VolterraAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Iter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The Picard iteration and its limit -/

/-- The Picard iterates of the Volterra map `u ↦ h₀ + ∫₀^· F(u s) ds`. -/
def iter (F : Fn → Fn) (h₀ : Fn) : ℕ → Fam
  | 0 => fun z θ _ => h₀ z θ
  | n + 1 => fun z θ τ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ

@[simp] theorem iter_zero (F : Fn → Fn) (h₀ : Fn) :
    iter F h₀ 0 = fun z θ _ => h₀ z θ := rfl

theorem iter_succ (F : Fn → Fn) (h₀ : Fn) (n : ℕ) :
    iter F h₀ (n + 1)
      = fun z θ τ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ := rfl

/-- The `n`-th increment of the Picard iteration. -/
def wseq (F : Fn → Fn) (h₀ : Fn) (n : ℕ) (τ : ℝ) : Fn :=
  fun z θ => slice (iter F h₀ (n + 1)) τ z θ - slice (iter F h₀ n) τ z θ

/-- The limit family: the sum of the increments, starting from the *first* increment (the
`0`-th increment needs no size bound and is added separately). -/
def limFam (F : Fn → Fn) (h₀ : Fn) : Fam :=
  fun z θ τ => h₀ z θ + wseq F h₀ 0 τ z θ + ∑' n, wseq F h₀ (n + 1) τ z θ

theorem slice_iter_zero (F : Fn → Fn) (h₀ : Fn) (n : ℕ) (z θ : ℝ) :
    slice (iter F h₀ n) 0 z θ = h₀ z θ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show h₀ z θ + (∫ s in (0 : ℝ)..0, F (slice (iter F h₀ n) s) z θ) = h₀ z θ
    rw [intervalIntegral.integral_same, add_zero]

theorem wseq_zero (F : Fn → Fn) (h₀ : Fn) (n : ℕ) (z θ : ℝ) :
    wseq F h₀ n 0 z θ = 0 := by
  simp only [wseq, slice_iter_zero, sub_self]

theorem limFam_zero (F : Fn → Fn) (h₀ : Fn) (z θ : ℝ) : limFam F h₀ z θ 0 = h₀ z θ := by
  simp only [limFam, tsum_zero, add_zero, wseq_zero]

/-- The increments telescope to the difference of the iterates. -/
theorem sum_wseq (F : Fn → Fn) (h₀ : Fn) (N : ℕ) (τ z θ : ℝ) :
    ∑ n ∈ Finset.range N, wseq F h₀ n τ z θ
      = slice (iter F h₀ N) τ z θ - h₀ z θ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [wseq, iter_zero]
    ring


/-- The shifted telescoping of the increments. -/
theorem sum_wseq_shift (F : Fn → Fn) (h₀ : Fn) (N : ℕ) (τ z θ : ℝ) :
    ∑ n ∈ Finset.range N, wseq F h₀ (n + 1) τ z θ
      = slice (iter F h₀ (N + 1)) τ z θ - h₀ z θ - wseq F h₀ 0 τ z θ := by
  have h := sum_wseq F h₀ (N + 1) τ z θ
  rw [Finset.sum_range_succ'] at h
  linarith [h]

/-- The limit of `F` along the Picard iterates. -/
def FlimM (F : Fn → Fn) (h₀ : Fn) (z θ τ : ℝ) : ℝ :=
  F h₀ z θ
    + ∑' n, (F (slice (iter F h₀ (n + 1)) τ) z θ - F (slice (iter F h₀ n) τ) z θ)

theorem sum_FlimM (F : Fn → Fn) (h₀ : Fn) (N : ℕ) (τ z θ : ℝ) :
    ∑ n ∈ Finset.range N,
        (F (slice (iter F h₀ (n + 1)) τ) z θ - F (slice (iter F h₀ n) τ) z θ)
      = F (slice (iter F h₀ N) τ) z θ - F h₀ z θ := by
  induction N with
  | zero =>
    have h : slice (iter F h₀ 0) τ = h₀ := rfl
    rw [h, sub_self]
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring


end Work.FTS.StrongEps.EpsLocalPStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_sub_smul_bump_refute =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The refutation of the `EpsMem` conjunct of `EpsSq_sub_smul_bump`

The obstruction is purely measure-theoretic.  `EpsMem α f` is (by definition)
`IntegrableOn (fun p ↦ (f p₁ p₂ · epsW α p₁ p₂)²) (Iz ×ˢ Iθ)`, and Mathlib's `Integrable` **by
definition** contains `AEStronglyMeasurable`.  So any datum whose *weighted square* is a fixed
measurable function `G > 0` on a box `B` but whose value distribution is that of an arbitrary
subset `E ⊆ B`, inherits the a.e. measurability of the indicator `1_E` from `EpsMem` — and a
non-`NullMeasurableSet` `E` therefore produces a datum with `EpsMem α h` but `¬ EpsMem α (h - 1·bump)`.

The datum used below is the `±bump` sign flip
`h z θ = bump z θ · (1 - 2·1_E(z,θ))`, whose weighted square is literally `(bump · epsW 1)²`
(so `EpsMem 1 h` follows from `EpsMem 1 bump`), while
`(h - 1·bump) · epsW 1 = -2·bump·1_E·epsW 1`, i.e. its weighted square is
`4 · (bump · epsW 1)² · 1_E`, which is a.e. strongly measurable only if `E` is null measurable.
-/










end

end Work.FTS.StrongEps.EpsSqTools
end
-- ===== merged: Submission.Work.FTS.StrongEps.exists_locUnif_subseq_of_uniform_H6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps

/-- A subsequence of a uniformly convergent sequence converges uniformly on the same set. -/
theorem tendstoUniformlyOn_comp_strictMono {ι β : Type*} [UniformSpace β] {F : ℕ → ι → β}
    {g : ι → β} {K : Set ι} {ψ : ℕ → ℕ} (h : TendstoUniformlyOn F g Filter.atTop K)
    (hψ : StrictMono ψ) :
    TendstoUniformlyOn (fun n => F (ψ n)) g Filter.atTop K := by
  intro u hu
  exact hψ.tendsto_atTop.eventually (h u hu)


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.NZaux.FstarSlotsFa =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.NZaux

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-!
# The three `F_*`-slots of the `r⁻¹`-density, with their `α`-rates

The singular part `F_*(z,θ) = α (Γ(θ)/c(α)) · 2z/(1+z)²` of the modulation profile is
`O(α z/(1+z)²)`, its angular derivative is `O(α² z/(1+z)²)` *because*
`D_θ Γ = α q(θ) Γ` carries an extra factor `α`, and its radial derivative is again
`O(α z/(1+z)²)` since `|z ∂_z F_*| ≤ F_*`.  Integrating against the angular measure
(measure `dθ`, so `∫_{Iθ} dθ = π/2`) and then against the `L₁₂`-weight `r⁻¹` — which is
absorbed by `r⁻¹·hKer r = 1/(1+r)²`, integrable on `(0,∞)` with integral `≤ 2` — gives the
three rates `α`, `α²`, `α`, uniformly in `0 < α ≤ 1`.

The proof is a single template (`slot_le`): a pointwise bound `|f r θ| ≤ c·hKer r` on
`r > 0`, `θ ∈ Iθ` yields
`∫⁻_r r⁻¹ ∫⁻_θ |f r θ| ≤ ofReal (π c)`.
The three pointwise bounds are the existing profile estimates of `rl¹`
(`Pss_Fstar_le`, `DthFstar_pt`, `DzFstar_pt`); `DthFstar_pt` is stated on the *open*
angular interval, so the two endpoints (where `sin 2θ = 0` and hence `D_θF_* = 0`) are
handled separately.
-/

/-- `hKer r = r/(1+r)²` is nonnegative on `r ≥ 0`. -/
private theorem hker_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Work.Spaces.hKer r := by
  rw [Work.Spaces.hKer_apply]; exact div_nonneg hr (by positivity)

/-- The `1/r` weight of `L₁₂` eats the numerator of `hKer r`. -/
private theorem inv_mul_hKer_eq {r : ℝ} (hr : 0 < r) :
    r⁻¹ * Work.Spaces.hKer r = (1 / (1 + r)) ^ 2 := by
  rw [Work.Spaces.hKer_apply]
  field_simp

/-- `r ↦ r⁻¹ hKer r` is integrable on `(0,∞)` (it equals `(1/(1+r))²` there). -/
private theorem integrableOn_inv_hKer :
    IntegrableOn (fun r : ℝ => r⁻¹ * Work.Spaces.hKer r) (Set.Ioi (0 : ℝ)) :=
  (Work.FTS.NonlinRows.Rl1.integrableOn_inv_one_add_sq').1 |>.congr_fun
    (fun _ hr => (inv_mul_hKer_eq hr).symm) measurableSet_Ioi

/-- **The slot template.**  A pointwise bound `|f r θ| ≤ c·hKer r` on the quadrant
(`r > 0`, `θ ∈ Iθ`) gives `∫⁻_r r⁻¹ ∫⁻_θ |f| ≤ ofReal (π c)`: the angular measure is `π/2`
and `∫_0^∞ r⁻¹ hKer r = ∫_0^∞ (1/(1+r))² ≤ 2`. -/
private theorem slot_le {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ → ℝ}
    (hbd : ∀ r, 0 < r → ∀ θ ∈ Work.Spaces.Iθ, |f r θ| ≤ c * Work.Spaces.hKer r) :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |f r θ|)
      ≤ ENNReal.ofReal (Real.pi * c) := by
  have hinnerae : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0:ℝ))),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |f r θ|)
        ≤ ENNReal.ofReal (c * Work.Spaces.hKer r * (Real.pi/2)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have h1 : ∀ θ ∈ Work.Spaces.Iθ,
        ENNReal.ofReal |f r θ| ≤ ENNReal.ofReal (c * Work.Spaces.hKer r) :=
      fun θ hθ => ENNReal.ofReal_le_ofReal (hbd r hr θ hθ)
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |f r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * Work.Spaces.hKer r) :=
          setLIntegral_mono measurable_const h1
      _ = ENNReal.ofReal (c * Work.Spaces.hKer r) * volume Work.Spaces.Iθ :=
          setLIntegral_const _ _
      _ = ENNReal.ofReal (c * Work.Spaces.hKer r) * ENNReal.ofReal (Real.pi / 2) := by
          rw [Work.Spaces.Iθ, Real.volume_Icc, sub_zero]
      _ = ENNReal.ofReal (c * Work.Spaces.hKer r * (Real.pi / 2)) :=
          (ENNReal.ofReal_mul (mul_nonneg hc (hker_nonneg hr.le))).symm
  have hInt : IntegrableOn (fun r : ℝ => r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi / 2)))
      (Set.Ioi (0:ℝ)) := by
    have hbase := integrableOn_inv_hKer
    have h2 : IntegrableOn (fun r : ℝ => (c * (Real.pi/2)) * (r⁻¹ * Work.Spaces.hKer r))
        (Set.Ioi 0) :=
      hbase.const_mul _
    refine h2.congr_fun (fun r _ => ?_) measurableSet_Ioi
    ring
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
      fun r : ℝ => r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi / 2)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr =>
      mul_nonneg (inv_nonneg.mpr hr.le)
        (mul_nonneg (mul_nonneg hc (hker_nonneg hr.le)) (by positivity)))
  have hval : ∫ r in Set.Ioi (0:ℝ), r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi/2))
      ≤ Real.pi * c := by
    have hpull : (c * (Real.pi/2)) * ∫ r in Set.Ioi (0:ℝ), r⁻¹ * Work.Spaces.hKer r
        = ∫ r in Set.Ioi (0:ℝ), r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi/2)) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
      ring
    rw [← hpull]
    have h2 : ∫ r in Set.Ioi (0:ℝ), r⁻¹ * Work.Spaces.hKer r ≤ 2 := by
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r hr => inv_mul_hKer_eq hr)]
      exact (Work.FTS.NonlinRows.Rl1.integrableOn_inv_one_add_sq').2
    calc (c * (Real.pi/2)) * ∫ r in Set.Ioi (0:ℝ), r⁻¹ * Work.Spaces.hKer r
        ≤ (c * (Real.pi/2)) * 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.pi * c := by ring
  calc ∫⁻ r in Set.Ioi 0, ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |f r θ|)
      ≤ ∫⁻ r in Set.Ioi 0,
          ENNReal.ofReal r⁻¹ * ENNReal.ofReal (c * Work.Spaces.hKer r * (Real.pi/2)) :=
        MeasureTheory.lintegral_mono_ae (hinnerae.mono (fun r hr => mul_le_mul_right hr _))
    _ = ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi/2))) := by
        rw [MeasureTheory.lintegral_congr_ae]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
        exact (ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)).symm
    _ = ENNReal.ofReal (∫ r in Set.Ioi 0, r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi/2))) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
    _ ≤ ENNReal.ofReal (Real.pi * c) := ENNReal.ofReal_le_ofReal hval

/-- The angular-derivative slot: `|D_θF_*| ≤ (80/3)α² hKer r` on the closed angular
interval.  The estimate `DthFstar_pt` is on the open interval; at `θ = 0, π/2` one has
`sin 2θ = 0`, so `D_θF_* = 0` there. -/
private theorem DthFstar_slot {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dth (Work.Construction.Fstar α) r θ| ≤ (80/3) * α^2 * Work.Spaces.hKer r := by
  intro r hr θ hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases eq_or_lt_of_le hθ0 with h0 | h0
  · have hz : Real.sin (2 * θ) = 0 := by rw [← h0]; simp
    rw [Work.Spaces.Dth, hz, zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α)) (hker_nonneg hr.le)
  rcases lt_or_eq_of_le hθ1 with h1 | h1
  · exact Work.FTS.NonlinRows.Rl1.DthFstar_pt hα hα1 hr h0 h1
  · have hz : Real.sin (2 * θ) = 0 := by
      rw [h1, show 2 * (Real.pi/2) = Real.pi by ring, Real.sin_pi]
    rw [Work.Spaces.Dth, hz, zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α)) (hker_nonneg hr.le)

/-- **The three `F_*`-slots.**  There is a universal `C` with, for every `0 < α ≤ 1`,
`∫⁻_r r⁻¹ (∫⁻_θ |F_*|) ≤ Cα`, `∫⁻_r r⁻¹ (∫⁻_θ |D_θF_*|) ≤ Cα²` and
`∫⁻_r r⁻¹ (∫⁻_θ |D_zF_*|) ≤ Cα`. -/
theorem FstarSlotsFa : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Construction.Fstar α r θ|))
      ≤ ENNReal.ofReal (C * α) ∧
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.Spaces.Dth (Work.Construction.Fstar α) r θ|))
      ≤ ENNReal.ofReal (C * α ^ 2) ∧
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.Spaces.Dz (Work.Construction.Fstar α) r θ|))
      ≤ ENNReal.ofReal (C * α) := by
  refine ⟨200, by norm_num, fun α hα hα1 => ⟨?_, ?_, ?_⟩⟩
  · have h := slot_le (c := 20 * α) (by positivity) (f := Work.Construction.Fstar α)
      (fun r hr θ hθ => Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_Fstar_le α r θ hα hα1 hr.le hθ)
    refine le_trans h (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [Real.pi_lt_four, hα]
  · have h := slot_le (c := (80/3) * α^2) (by positivity)
      (f := Work.Spaces.Dth (Work.Construction.Fstar α)) (DthFstar_slot hα hα1)
    refine le_trans h (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Real.pi * ((80/3) * α^2) ≤ 4 * ((80/3) * α^2) :=
      mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (by positivity)
    have h2 : (4:ℝ) * ((80/3) * α^2) ≤ 200 * α^2 := by nlinarith [sq_nonneg α]
    linarith
  · have h := slot_le (c := 20 * α) (by positivity)
      (f := Work.Spaces.Dz (Work.Construction.Fstar α))
      (fun r hr θ hθ => Work.FTS.NonlinRows.Rl1.DzFstar_pt hα hα1 hr hθ)
    refine le_trans h (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [Real.pi_lt_four, hα]

end Work.FTS.StrongPersist.H6Rows.NZaux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.IP6UnfoldCd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Cd6Unfold

open Work.FTS.TransportS

/-- **The `D_z`-shift of a slot pairing at finite order.**  Moving one `D_z` off a slot onto
the next slot costs the commutation `D_z^b D_θ^a (D_z u) = D_z^{b+1} D_θ^a u` on the open
quadrant, which is Clairaut up to order `a + 1`: `ContDiffOn ℝ (a+1)` of `u` is exactly the
hypothesis of the transfer chapter's `mixed_Dz_shift_Q0Sm`.  The two integrands then agree on
the quadrant, whose complement in `Iz × Iθ` is null. -/
theorem slotPairing_dz_fin {a b : ℕ} {u v : ℝ → ℝ → ℝ} (ρ : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ (((a + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry u)
      Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ (((a + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry v)
      Work.FTS.EllipticEst.Q0) :
    slotPairing ρ a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)
      = slotPairing ρ a (b + 1) u v := by
  have hXu := Work.FTS.CoercivityFix.Transfer.mixed_Dz_shift_Q0Sm (u := u) (N := a + 1)
    (hu : Work.FTS.CoercivityFix.Transfer.Q0Sm (a + 1) u) (le_refl (a + 1)) b
  have hXv := Work.FTS.CoercivityFix.Transfer.mixed_Dz_shift_Q0Sm (u := v) (N := a + 1)
    (hv : Work.FTS.CoercivityFix.Transfer.Q0Sm (a + 1) v) (le_refl (a + 1)) b
  unfold slotPairing
  refine Work.FTS.TransportS.setIntegral2_congr_Q0 (fun p hp => ?_)
  simp only [Function.uncurry]
  rw [hXu p.1 p.2 hp, hXv p.1 p.2 hp]

/-- **The `D_z`-shift of a slot term at finite order.** -/
theorem slotTerm_dz_le_fin (α : ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ (((a + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry u)
      Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ (((a + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry v)
      Work.FTS.EllipticEst.Q0) :
    SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v) ≤ SlotTerm α a (b + 1) u v := by
  have h1 : |slotPairing leafEta a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      = |slotPairing leafEta a (b + 1) u v| := by
    rw [slotPairing_dz_fin (a := a) (b := b) leafEta hu hv]
  have h2 : |slotPairing leafOne a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      = |slotPairing leafOne a (b + 1) u v| := by
    rw [slotPairing_dz_fin (a := a) (b := b) leafOne hu hv]
  have h3 : (if 1 ≤ a then
        |slotPairing (leafGam α) a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)| else 0)
      = (if 1 ≤ a then |slotPairing (leafGam α) a (b + 1) u v| else 0) := by
    by_cases ha : 1 ≤ a
    · rw [if_pos ha, if_pos ha]
      rw [slotPairing_dz_fin (a := a) (b := b) (leafGam α) hu hv]
    · rw [if_neg ha, if_neg ha]
  unfold SlotTerm
  linarith [h1, h2, h3]

/-- **The `D_θ`-shift of a slot term** (pure bookkeeping of the iterates, no smoothness). -/
theorem slotTerm_dth_le_fin (α : ℝ) (a b : ℕ) (u v : ℝ → ℝ → ℝ) :
    SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v) ≤ SlotTerm α (a + 1) b u v := by
  have h1 : |slotPairing leafEta a b (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
      = |slotPairing leafEta (a + 1) b u v| := by
    rw [slotPairing_dth leafEta a b u v]
  have h2 : |slotPairing leafOne a b (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
      = |slotPairing leafOne (a + 1) b u v| := by
    rw [slotPairing_dth leafOne a b u v]
  have h3 : (if 1 ≤ a then
        |slotPairing (leafGam α) a b (Work.Spaces.Dth u) (Work.Spaces.Dth v)| else 0)
      ≤ (if 1 ≤ a + 1 then |slotPairing (leafGam α) (a + 1) b u v| else 0) := by
    rw [if_pos (by omega : 1 ≤ a + 1)]
    by_cases ha : 1 ≤ a
    · rw [if_pos ha]
      rw [slotPairing_dth (leafGam α) a b u v]
    · rw [if_neg ha]
      exact abs_nonneg _
  unfold SlotTerm
  linarith [h1, h2, h3]

/-- **The `D_θ`-shift of the slot sums** (pure bookkeeping). -/
theorem slotSum_dth_le_fin (α : ℝ) (n : ℕ) (u v : ℝ → ℝ → ℝ) :
    SlotSum α n (Work.Spaces.Dth u) (Work.Spaces.Dth v) ≤ SlotSum α (n + 1) u v := by
  rw [SlotSum_eq_sum_SlotTerm, SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a b (Work.Spaces.Dth u) (Work.Spaces.Dth v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α (a + 1) b u v :=
        Finset.sum_le_sum (fun a _ =>
          Finset.sum_le_sum (fun b _ => slotTerm_dth_le_fin α a b u v))
    _ = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2 - (a + 1)),
          SlotTerm α (a + 1) b u v := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [show n + 2 - (a + 1) = n + 1 - a from Nat.succ_sub_succ (n := n + 1) (m := a)]
    _ ≤ ∑ a' ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2 - a'),
          SlotTerm α a' b u v := by
        conv_rhs => rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right
          (show (0 : ℝ) ≤ ∑ b ∈ Finset.range (n + 2 - 0), SlotTerm α 0 b u v from
            Finset.sum_nonneg (fun b _ => SlotTerm_nonneg α 0 b u v))

/-- **The `D_z`-shift of the slot sums, at the sharp finite order `C^{n+1}`.**  (The sibling
`N0pair6bWork.slotSum_Dz_le_fin` states the same with the coarser hypothesis `C^{n+2}`.) -/
theorem slotSum_dz_le_fin (α : ℝ) (n : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry u)
      Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry v)
      Work.FTS.EllipticEst.Q0) :
    SlotSum α n (Work.Spaces.Dz u) (Work.Spaces.Dz v) ≤ SlotSum α (n + 1) u v := by
  rw [SlotSum_eq_sum_SlotTerm, SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          SlotTerm α a (b + 1) u v :=
        Finset.sum_le_sum (fun a ha =>
          Finset.sum_le_sum (fun b _ =>
            slotTerm_dz_le_fin α a b
              (hu.of_le (m := (((a + 1 : ℕ)) : WithTop ℕ∞))
                (by exact_mod_cast (show a + 1 ≤ n + 1 from by
                  have := Finset.mem_range.mp ha; omega)))
              (hv.of_le (m := (((a + 1 : ℕ)) : WithTop ℕ∞))
                (by exact_mod_cast (show a + 1 ≤ n + 1 from by
                  have := Finset.mem_range.mp ha; omega)))))
    _ ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2 - a),
          SlotTerm α a b u v := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        by_cases ha : a ≤ n + 1
        · rw [show n + 2 - a = (n + 1 - a) + 1 from by omega]
          conv_rhs => rw [Finset.sum_range_succ']
          exact le_add_of_nonneg_right
            (show (0 : ℝ) ≤ SlotTerm α a 0 u v from SlotTerm_nonneg α a 0 u v)
        · rw [show n + 1 - a = 0 from by omega]
          simp only [Finset.range_zero, Finset.sum_empty]
          exact Finset.sum_nonneg (fun b _ => SlotTerm_nonneg α a b u v)
    _ ≤ ∑ a' ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2 - a'),
          SlotTerm α a' b u v := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => ?_)
          (fun a _ _ => Finset.sum_nonneg (fun b _ => SlotTerm_nonneg α a b u v))
        simp only [Finset.mem_range] at ha ⊢
        omega

/-- **The unfolding induction at finite order.**  For every level `m`, profiles that are
`C^{m+1}` on the open quadrant satisfy
`|IPn α m u v| ≤ 3^m · 10^22 · SlotSum α (m+1) u v`.

The two analytic inputs are `slotSum_dth_le_fin` (free) and `slotSum_dz_le_fin`, whose
hypothesis `C^{(m+1)+1}` is exactly the induction hypothesis at level `m + 1`; the children
`D_θ u`, `D_z u` are `C^{m+1}`, one order below, as supplied by `contDiffOn_Dth_nat` /
`contDiffOn_Dz_nat`. -/
theorem IPn_le_SlotSum_cd6 :
    ∀ (m : ℕ) (α : ℝ) (u v : ℝ → ℝ → ℝ),
      ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry u)
        Work.FTS.EllipticEst.Q0 →
      ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry v)
        Work.FTS.EllipticEst.Q0 →
      |IPn α m u v| ≤ (3 : ℝ) ^ m * (10 : ℝ) ^ 22 * SlotSum α (m + 1) u v := by
  intro m
  induction m with
  | zero =>
      intro α u v _ _
      rw [show IPn α 0 = Work.Coercivity.H1IP α from rfl]
      simpa using H1IP_le_SlotSum_one α u v
  | succ m ih =>
      intro α u v hu hv
      have hu2 : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry u)
          Work.FTS.EllipticEst.Q0 :=
        hu.of_le (m := (((m + 1 : ℕ)) : WithTop ℕ∞))
          (by exact_mod_cast (show m + 1 ≤ (m + 1) + 1 from by omega))
      have hv2 : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry v)
          Work.FTS.EllipticEst.Q0 :=
        hv.of_le (m := (((m + 1 : ℕ)) : WithTop ℕ∞))
          (by exact_mod_cast (show m + 1 ≤ (m + 1) + 1 from by omega))
      have hDthu : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.Dth u)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.contDiffOn_Dth_nat
          Work.FTS.EllipticEst.isOpen_Q0 (N := m + 1) hu
      have hDthv : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.Dth v)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.contDiffOn_Dth_nat
          Work.FTS.EllipticEst.isOpen_Q0 (N := m + 1) hv
      have hDzu : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.Dz u)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.contDiffOn_Dz_nat
          Work.FTS.EllipticEst.isOpen_Q0 (N := m + 1) hu
      have hDzv : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.Dz v)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.contDiffOn_Dz_nat
          Work.FTS.EllipticEst.isOpen_Q0 (N := m + 1) hv
      have hIHu := ih α u v hu2 hv2
      have hIHd := ih α (Work.Spaces.Dth u) (Work.Spaces.Dth v) hDthu hDthv
      have hIHz := ih α (Work.Spaces.Dz u) (Work.Spaces.Dz v) hDzu hDzv
      have hd := slotSum_dth_le_fin α (m + 1) u v
      have hz := slotSum_dz_le_fin α (m + 1) hu hv
      have hmono := SlotSum_mono (α := α) (u := u) (v := v)
        (n := m + 1) (m := m + 2) (by omega)
      have hsum : SlotSum α (m + 1) u v
            + SlotSum α (m + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + SlotSum α (m + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v)
          ≤ 3 * SlotSum α (m + 2) u v := by
        linarith
      have hstep : IPn α (m + 1) u v
          = IPn α m u v + IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + IPn α m (Work.Spaces.Dz u) (Work.Spaces.Dz v) := by
        rw [show IPn α (m + 1)
              = Work.Coercivity.HkIPStep 1 1 (IPn α m) from rfl]
        simp only [Work.Coercivity.HkIPStep, one_mul]
      rw [hstep]
      have htri : |IPn α m u v + IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + IPn α m (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ |IPn α m u v| + |IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |IPn α m (Work.Spaces.Dz u) (Work.Spaces.Dz v)| := by
        have h1 := abs_add_le
          (IPn α m u v + IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v))
          (IPn α m (Work.Spaces.Dz u) (Work.Spaces.Dz v))
        have h2 := abs_add_le (IPn α m u v)
          (IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v))
        linarith
      have hscale : |IPn α m u v|
            + |IPn α m (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
            + |IPn α m (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
          ≤ (3 : ℝ) ^ m * (10 : ℝ) ^ 22 * SlotSum α (m + 1) u v
            + (3 : ℝ) ^ m * (10 : ℝ) ^ 22
              * SlotSum α (m + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + (3 : ℝ) ^ m * (10 : ℝ) ^ 22
              * SlotSum α (m + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v) := by
        linarith
      have hfac : (3 : ℝ) ^ m * (10 : ℝ) ^ 22 * SlotSum α (m + 1) u v
            + (3 : ℝ) ^ m * (10 : ℝ) ^ 22
              * SlotSum α (m + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
            + (3 : ℝ) ^ m * (10 : ℝ) ^ 22
              * SlotSum α (m + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v)
          = (3 : ℝ) ^ m * (10 : ℝ) ^ 22
            * (SlotSum α (m + 1) u v
              + SlotSum α (m + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
              + SlotSum α (m + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v)) := by
        ring
      have hnonneg : (0 : ℝ) ≤ (3 : ℝ) ^ m * (10 : ℝ) ^ 22 := by positivity
      have hfinal : (3 : ℝ) ^ m * (10 : ℝ) ^ 22
            * (SlotSum α (m + 1) u v
              + SlotSum α (m + 1) (Work.Spaces.Dth u) (Work.Spaces.Dth v)
              + SlotSum α (m + 1) (Work.Spaces.Dz u) (Work.Spaces.Dz v))
          ≤ (3 : ℝ) ^ (m + 1) * (10 : ℝ) ^ 22 * SlotSum α (m + 2) u v := by
        have h3 : (3 : ℝ) ^ m * (10 : ℝ) ^ 22 * (3 * SlotSum α (m + 2) u v)
            = (3 : ℝ) ^ (m + 1) * (10 : ℝ) ^ 22 * SlotSum α (m + 2) u v := by
          rw [pow_succ]; ring
        rw [← h3]
        exact mul_le_mul_of_nonneg_left hsum hnonneg
      linarith [htri, hscale, hfac, hfinal]

end Cd6Unfold

theorem IP6UnfoldCd6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u v : ℝ → ℝ → ℝ),
    ContDiffOn ℝ 6 (Function.uncurry u) Work.FTS.EllipticEst.Q0 →
    ContDiffOn ℝ 6 (Function.uncurry v) Work.FTS.EllipticEst.Q0 →
    |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u v|
      ≤ C * Work.FTS.TransportS.SlotSum α 6 u v := by
  refine ⟨(3 : ℝ) ^ 5 * (10 : ℝ) ^ 22, by norm_num, ?_⟩
  intro α u v hu hv
  have hIP6 : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
      = Work.FTS.TransportS.IPn α 5 := rfl
  rw [hIP6]
  exact Cd6Unfold.IPn_le_SlotSum_cd6 5 α u v hu hv

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_of_WlInf6_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The norm half of the `𝒲^{6,∞}`-priced product rule, from the pointwise majorant.**
Given the two `C^6` slot bounds (the seven radial slots against `HkIntegrand α 6 g`, the mixed
slots against `GmajW6 α g`), the `ℋ⁶`-norm of `f·g` is bounded by
`√(42701 (7 Cz + 49 Cm)) · α^{-1/2} · |f|_{𝒲^{6,∞}} · |g|_{ℋ⁶}`. -/
theorem hknorm_mul_aux6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hfs : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hfw : Work.Spaces.WlInfMem α 6 f)
    (hgs : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hgm : Work.Spaces.HkMem α 6 g)
    {Cz Cm : ℝ} (hCz0 : 0 < Cz) (hCm0 : 0 < Cm)
    (hzslot : ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Cz * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
    (hmslot : ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Cm * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :
    Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ Real.sqrt ((7 * Cz + 49 * Cm) * 42701) * α ^ (-(1 / 2 : ℝ))
            * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g := by
  have hmaj := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.prod_majorant_cd6 hα hα1 hfs hfw
    hgs hgm hCz0 hCm0 hzslot hmslot
  set K : ℝ := 7 * Cz + 49 * Cm with hKdef
  set Kg : ℝ := 1 + 700 * (1 + 6 * (Work.Spaces.gam α - 1)⁻¹) with hKgdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKgpos : 0 < Kg := by
    rw [hKgdef]
    have h1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
      rw [Work.Spaces.gam_sub_one]; linarith
    have h2 : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr h1.le
    linarith
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfw
  -- the pointwise majorant, in terms of the local constant `K`
  have hmajor : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ K * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
    intro z hz θ hθ
    rw [hKdef]
    exact hmaj z hz θ hθ
  -- the angular integral of the product's integrand
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (Work.Spaces.WlInf α 6 f) ^ 2
            * (Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K * (Work.Spaces.WlInf α 6 f) ^ 2)
        * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) Work.Spaces.Iθ :=
      (Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul _
    have h1 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
        ≤ Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
      simpa only [hKgdef] using
        Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_theta_integral_le (α := α) (g := g)
          hα hα1 hgm hz
    calc (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := h1
      _ ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * (Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hKpos.le (sq_nonneg _))
  have hbdd : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
    intro z hz
    have h1 := hinner z hz
    calc (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (Work.Spaces.WlInf α 6 f) ^ 2
            * (Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) := h1
      _ = (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by ring
  have hdom : IntegrableOn (fun z => (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
      * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) Work.Spaces.Iz :=
    hgm.2.const_mul _
  -- the squared bound
  have hSq : Work.Spaces.HkSq α 6 (fun z θ => f z θ * g z θ)
      ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg) * Work.Spaces.HkSq α 6 g := by
    have h1 : Work.Spaces.HkSq α 6 (fun z θ => f z θ * g z θ)
        ≤ ∫ z in Work.Spaces.Iz, (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
      rw [Work.Spaces.HkSq]
      exact setIntegral_mono_of_nonneg
        (fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
        (fun z hz => hbdd z hz) hdom
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul,
      Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6_z_integral]
  -- the passage to the `ℋ⁶`-norm
  have hXn : Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
      ≤ Real.sqrt (K * Kg) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g := by
    have h1 : Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ Real.sqrt ((K * Kg) * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.Spaces.HkSq α 6 g) := by
      rw [show Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
            = Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => f z θ * g z θ)) from rfl]
      refine Real.sqrt_le_sqrt ?_
      calc Work.Spaces.HkSq α 6 (fun z θ => f z θ * g z θ)
          ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg) * Work.Spaces.HkSq α 6 g := hSq
        _ = (K * Kg) * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkSq α 6 g := by ring
    refine le_trans h1 (le_of_eq ?_)
    rw [show Work.Spaces.HkNorm α 6 g = Real.sqrt (Work.Spaces.HkSq α 6 g) from rfl,
      Real.sqrt_mul (show (0 : ℝ) ≤ (K * Kg) * (Work.Spaces.WlInf α 6 f) ^ 2 by positivity),
      Real.sqrt_mul (show (0 : ℝ) ≤ K * Kg by positivity),
      Real.sqrt_sq hWnn]
  refine ⟨Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6 hα hα1 hfs hfw
      hgs hgm, ?_⟩
  refine le_trans hXn ?_
  -- `√(K Kg) ≤ √(42701 K) α^{-1/2}`
  have hKg_le : Kg ≤ 42701 * α⁻¹ := by
    have h1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
      rw [Work.Spaces.gam_sub_one]; linarith
    have hginv : (Work.Spaces.gam α - 1)⁻¹ = 10 / α := by
      rw [Work.Spaces.gam_sub_one, inv_div]
    have hαinv : (1 : ℝ) ≤ α⁻¹ := by rw [one_le_inv₀ hα]; exact hα1
    rw [hKgdef, hginv, div_eq_mul_inv]
    ring_nf
    nlinarith [hαinv]
  have hsqrt : Real.sqrt (K * Kg) ≤ Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) := by
    have h1 : K * Kg ≤ 42701 * K * α⁻¹ := by
      calc K * Kg ≤ K * (42701 * α⁻¹) := mul_le_mul_of_nonneg_left hKg_le hKpos.le
        _ = 42701 * K * α⁻¹ := by ring
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [show (42701 : ℝ) * K * α⁻¹ = (42701 * K) * α⁻¹ from by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ 42701 * K by positivity),
      Work.FTS.StrongPersist.H6Rows.WProd6.sqrt_inv_eq_rpow_neg_half6 hα]
  have hmain : Real.sqrt (K * Kg) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g
      ≤ Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f
        * Work.Spaces.HkNorm α 6 g := by
    calc Real.sqrt (K * Kg) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g
        = Real.sqrt (K * Kg) * (Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g) := by
          ring
      _ ≤ (Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)))
            * (Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g) :=
          mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hWnn (Real.sqrt_nonneg _))
      _ = Real.sqrt (42701 * K) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f
            * Work.Spaces.HkNorm α 6 g := by ring
  refine le_trans hmain ?_
  rw [show K * 42701 = 42701 * K from by ring]


end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.ip6_cs_cd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false





end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## Elementary auxiliary facts -/

/-- `gam α = 1 + α/10` does not vanish for `α > 0`. -/
private theorem gam_ne_zero_of_pos {α : ℝ} (hα : 0 < α) : Work.Spaces.gam α ≠ 0 := by
  rw [Work.Spaces.gam]; intro h; linarith

/-- The level-six `ℋ⁶`-integrand vanishes whenever `sin(2θ) = 0` (assuming `gam α ≠ 0`). -/
private theorem HkIntegrand6_eq_zero_of_sin_two_eq_zero {α : ℝ}
    (hgam : Work.Spaces.gam α ≠ 0) {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α 6 F z θ = 0 := by
  have hη : (Work.Spaces.eta / 2 : ℝ) ≠ 0 := by norm_num [Work.Spaces.eta]
  have hg : -(Work.Spaces.gam α / 2) ≠ 0 := by
    intro hc; exact hgam (by linarith [neg_eq_zero.mp hc])
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [h, Real.zero_rpow hη, Real.zero_rpow hg]
  simp

/-- For a radial `C^6` datum `a`, the one-variable iterate `DzdIter b a` is `C^{6-b}` on the
open half-line `(0,∞)`, hence in particular continuous there. -/
private theorem contDiffOn_DzdIter_query {a : ℝ → ℝ}
    (hacd : ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => a z)) Work.FTS.EllipticEst.Q0)
    {b : ℕ} (hb : b ≤ 6) : ContDiffOn ℝ (6 - b) (Work.Elliptic.DzdIter b a) (Set.Ioi 0) := by
  have h2 : ContDiffOn ℝ (6 - b)
      (Function.uncurry (Work.Spaces.DzIter b (fun z (_ : ℝ) => a z)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.contDiffOn_uncurry_DzIter_aux
      (M := 6) hacd b (6 - b) (by omega)
  have hmaps : Set.MapsTo (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi 0) Work.FTS.EllipticEst.Q0 :=
    fun z hz => ⟨hz, by norm_num, by linarith [Real.pi_gt_three]⟩
  have hc : ContDiffOn ℝ (6 - b) (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi 0) :=
    contDiffOn_id.prodMk contDiffOn_const
  have h3 : ContDiffOn ℝ (6 - b)
      (fun z : ℝ => Work.Spaces.DzIter b (fun z (_ : ℝ) => a z) z 1) (Set.Ioi 0) :=
    (h2.comp hc hmaps).congr (fun z _ => rfl)
  exact h3.congr (fun z _ => (Work.Elliptic.DzIter_rad a b z 1).symm)

/-- **The a.e. `D_z`-bounds upgrade to pointwise bounds on `(0,∞)`.**  A function that is
continuous on the open half-line and bounded almost everywhere there is bounded everywhere:
the set where the bound fails is open and lies inside a null set, hence is empty. -/
private theorem dzdIter_bound_everywhere {a : ℝ → ℝ} {K : ℝ}
    (hacd : ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => a z)) Work.FTS.EllipticEst.Q0)
    (haeb : ∀ b : ℕ, b ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |Work.Elliptic.DzdIter b a z| ≤ K) :
    ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter b a z| ≤ K := by
  intro b hb z hzpos
  by_contra hle
  have hK : K < |Work.Elliptic.DzdIter b a z| := not_le.mp hle
  have hcont : ContinuousOn (Work.Elliptic.DzdIter b a) (Set.Ioi 0) :=
    (contDiffOn_DzdIter_query hacd hb).continuousOn
  have hae : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), y ∈ Work.Spaces.Iz →
      |Work.Elliptic.DzdIter b a y| ≤ K :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp (haeb b hb)
  have hca : ContinuousAt (fun y : ℝ => |Work.Elliptic.DzdIter b a y|) z :=
    (hcont.continuousAt (isOpen_Ioi.mem_nhds hzpos)).abs
  have hpre : {y : ℝ | K < |Work.Elliptic.DzdIter b a y|} ∈ 𝓝 z :=
    hca.preimage_mem_nhds (isOpen_Ioi.mem_nhds hK)
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem hpre (isOpen_Ioi.mem_nhds hzpos))
  have hnull : MeasureTheory.volume
      {y : ℝ | ¬ (y ∈ Work.Spaces.Iz → |Work.Elliptic.DzdIter b a y| ≤ K)} = 0 :=
    MeasureTheory.ae_iff.mp hae
  have hsub : Metric.ball z ε ⊆
      {y : ℝ | ¬ (y ∈ Work.Spaces.Iz → |Work.Elliptic.DzdIter b a y| ≤ K)} := by
    intro y hy
    have hyK : K < |Work.Elliptic.DzdIter b a y| := (hball hy).1
    have hy0 : (0 : ℝ) < y := (hball hy).2
    intro hcon
    exact absurd (hcon (le_of_lt hy0)) (not_le.mpr hyK)
  have hzero : MeasureTheory.volume (Metric.ball z ε) = 0 :=
    le_antisymm (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq hnull)) bot_le
  rw [Real.volume_ball] at hzero
  have hne : ENNReal.ofReal (2 * ε) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; positivity
  exact hne hzero

/-! ## The main theorem -/

theorem radialSupMul_cd6 : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {a : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {K : ℝ},
    0 < α → α ≤ 1 → 0 ≤ K →
    ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => a z)) Work.FTS.EllipticEst.Q0 →
    ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
    (∀ j : ℕ, j ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z (_ : ℝ) => a z) z θ| ≤ K) →
    Work.Spaces.HkMem α 6 g →
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => a z * g z θ)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 6 (fun z θ => a z * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => a z * g z θ) ≤ C * K * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.radialHkIntegrand_majorant_cd6
  refine ⟨Real.sqrt C₀ + 1, by linarith [Real.sqrt_nonneg C₀], ?_⟩
  intro α a g K hα hα1 hK hacd hgcd hKj hgm
  -- the a.e. slot bounds for the radial datum
  have haeb : ∀ b : ℕ, b ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |Work.Elliptic.DzdIter b a z| ≤ K := by
    intro b hb
    filter_upwards [hKj b hb] with z hz
    simpa [Work.Elliptic.DzIter_rad] using hz 0
  -- the same bounds at every `z > 0`
  have heverywhere := dzdIter_bound_everywhere hacd haeb
  -- the pointwise majorant of the child lemma, with the two Leibniz identities supplied
  have hmaj : ∀ {K' : ℝ} {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b a z| ≤ K') →
      Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ
        ≤ C₀ * K' ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro K' z θ hz hθ0 hθ1 hbnd
    exact hC₀ (α := α) (K := K') (r := a) (g := g)
      (fun z θ hz hθ0 hθ1 j hj =>
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
          hacd hgcd hj z θ hz hθ0 hθ1)
      (fun z θ hz hθ0 hθ1 j i hi hij =>
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
          hacd hgcd hi hij z θ hz hθ0 hθ1)
      hz hθ0 hθ1 hbnd
  -- the pointwise majorant on the whole closed quadrant
  have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ
        ≤ (C₀ * K ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      simp
    · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
      · exact hmaj hzpos hθi.1 hθi.2 (fun b hb => heverywhere b hb z hzpos)
      · have hθc : θ = 0 ∨ θ = Real.pi / 2 := by
          rcases lt_or_ge (0 : ℝ) θ with h | h
          · right; exact le_antisymm hθ.2 (le_of_not_gt fun h' => hθi ⟨h, h'⟩)
          · left; exact le_antisymm h hθ.1
        have hsin : Real.sin (2 * θ) = 0 := by
          rcases hθc with h0 | hπ
          · rw [h0]; simp
          · rw [hπ, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        rw [HkIntegrand6_eq_zero_of_sin_two_eq_zero (gam_ne_zero_of_pos hα) hsin,
          HkIntegrand6_eq_zero_of_sin_two_eq_zero (F := g) (gam_ne_zero_of_pos hα) hsin]
        simp
  -- the product is `C^6` on the open quadrant
  have hfg : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => a z * g z θ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.contDiffOn_uncurry_mul_cd6 hacd hgcd
  -- continuity of the integrand of the product on the open quadrant
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.continuousOn_HkIntegrand_cd6
      (le_refl 6) hfg
  -- a.e. strong measurability of the angular slices
  have hslice : ∀ z ∈ Work.Spaces.Iz, AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => Work.Blocks.Half.HkIntegrand_zero_z α 6 _ θ
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos
  -- a.e. strong measurability of the `z`-slice integral
  have houter : AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) p.1 p.2)
      hcont).integral_prod_right'
    have hfun : (fun z => ∫ θ, Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 (fun z θ => a z * g z θ) z θ) := rfl
    rw [← hfun]
    exact h
  -- the honest membership
  have hHkMem : Work.Spaces.HkMem α 6 (fun z θ => a z * g z θ) :=
    Work.Blocks.HkMem_of_majorant_aesm α 6
      (M := fun z θ => (C₀ * K ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ)
      hslice houter
      (fun z hz => (hgm.1 z hz).const_mul _)
      (by
        have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
              (C₀ * K ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ)
            = fun z => (C₀ * K ^ 2) * ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 6 g z θ :=
          funext fun z => MeasureTheory.integral_const_mul _ _
        rw [hfun]
        exact hgm.2.const_mul _)
      hle
  -- the squared-norm bound
  have hSq : Work.Spaces.HkSq α 6 (fun z θ => a z * g z θ)
      ≤ (C₀ * K ^ 2) * Work.Spaces.HkSq α 6 g := by
    have h1 : Work.Spaces.HkSq α 6 (fun z θ => a z * g z θ)
        ≤ ∫ z in Work.Spaces.Iz,
            (C₀ * K ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := by
      rw [Work.Spaces.HkSq]
      refine MeasureTheory.setIntegral_mono_of_nonneg
        (fun z _ => MeasureTheory.integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
        (fun z hz => ?_)
        (hgm.2.const_mul _)
      have h3 := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
        ((hgm.1 z hz).const_mul (C₀ * K ^ 2))
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hle z hz θ hθ))
      rwa [MeasureTheory.integral_const_mul] at h3
    calc Work.Spaces.HkSq α 6 (fun z θ => a z * g z θ)
        ≤ ∫ z in Work.Spaces.Iz,
            (C₀ * K ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) := h1
      _ = (C₀ * K ^ 2) * Work.Spaces.HkSq α 6 g := by
          rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]
  -- the norm bound
  have hnorm : Work.Spaces.HkNorm α 6 (fun z θ => a z * g z θ)
      ≤ Real.sqrt C₀ * K * Work.Spaces.HkNorm α 6 g := by
    have h1 : Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => a z * g z θ))
        ≤ Real.sqrt ((C₀ * K ^ 2) * Work.Spaces.HkSq α 6 g) := Real.sqrt_le_sqrt hSq
    have h2 : Real.sqrt ((C₀ * K ^ 2) * Work.Spaces.HkSq α 6 g)
        = Real.sqrt C₀ * K * Real.sqrt (Work.Spaces.HkSq α 6 g) := by
      rw [Real.sqrt_mul (show (0 : ℝ) ≤ C₀ * K ^ 2 by positivity),
        Real.sqrt_mul (le_of_lt hC₀pos), Real.sqrt_sq hK]
    rw [h2] at h1
    simpa only [Work.Spaces.HkNorm] using h1
  refine ⟨hfg, hHkMem, ?_⟩
  calc Work.Spaces.HkNorm α 6 (fun z θ => a z * g z θ)
      ≤ Real.sqrt C₀ * K * Work.Spaces.HkNorm α 6 g := hnorm
    _ ≤ (Real.sqrt C₀ + 1) * K * Work.Spaces.HkNorm α 6 g := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg C₀]) hK

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
end
