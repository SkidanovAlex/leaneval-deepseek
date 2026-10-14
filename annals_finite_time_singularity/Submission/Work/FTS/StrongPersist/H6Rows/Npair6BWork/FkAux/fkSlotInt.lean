import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.StepFacts.HkMem_Jeps_step
import Submission.Work.FTS.StrongEps.StepFacts.StepPointwise
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbAux.SlotPriceAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkJets
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMassAux
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux
import Submission.Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.ExcPairBranches
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.ClassC.level0_psiSeries_concrete =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-- The paper's per-mode constant: `μ_0 = 1` and `μ_m = lamR m − 3α² − 3α(5+α)/2`. -/
def muSeq (α : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 1 else Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2

/-- `μ_m > 0` for `α ≤ 1/4`. -/
theorem muSeq_pos {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) : 0 < muSeq α m := by
  rcases eq_or_ne m 0 with h | h
  · rw [muSeq, if_pos h]; norm_num
  · rw [muSeq, if_neg h]
    have hm : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    rw [Work.FTS.PhiStar.Radial.lamR]
    nlinarith [hm, hα.le, hα4, sq_nonneg α]


end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.sharpN0_hkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000



end Work.FTS.GalFields.RHS
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.sharpN0_piecesA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


end Work.FTS.GalFields.RHS
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.sharpN0_piecesB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


end Work.FTS.GalFields.RHS
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.sharpN0_sums =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The nine piece bounds assemble into the bound for the right-nested sum `Rsum`. -/
theorem sharpN0_sums {α Ci : ℝ} {g g' h : ℝ → ℝ → ℝ} (hα : 0 < α) (hCi : 0 < Ci)
    (CF Cdz Cw : ℝ) (hCF : 0 < CF) (hCdz : 0 < Cdz) (hCw : 0 < Cw)
    (h1 : Work.Spaces.HkMem α 4 (P1 α g h)
      ∧ Work.FTS.Nonlin.Xn α (P1 α g h) ≤ kA1 α Ci * TOf α g g' h)
    (h2 : Work.Spaces.HkMem α 4 (P2 α g' h)
      ∧ Work.FTS.Nonlin.Xn α (P2 α g' h) ≤ kA2 α Ci * TOf α g g' h)
    (h3 : Work.Spaces.HkMem α 4 (P3 α h)
      ∧ Work.FTS.Nonlin.Xn α (P3 α h) ≤ kA3 α Ci CF * TOf α g g' h)
    (h4 : Work.Spaces.HkMem α 4 (P4 α g h)
      ∧ Work.FTS.Nonlin.Xn α (P4 α g h) ≤ kA4 α Ci * TOf α g g' h)
    (h5 : Work.Spaces.HkMem α 4 (P5 α g' h)
      ∧ Work.FTS.Nonlin.Xn α (P5 α g' h) ≤ kA5 α Ci * TOf α g g' h)
    (h6 : Work.Spaces.HkMem α 4 (P6 α h)
      ∧ Work.FTS.Nonlin.Xn α (P6 α h) ≤ kA6 α Ci Cdz * TOf α g g' h)
    (h7 : Work.Spaces.HkMem α 4 (P7 α g h)
      ∧ Work.FTS.Nonlin.Xn α (P7 α g h) ≤ kA7 α Ci * TOf α g g' h)
    (h8 : Work.Spaces.HkMem α 4 (P8 α g' h)
      ∧ Work.FTS.Nonlin.Xn α (P8 α g' h) ≤ kA8 α Ci * TOf α g g' h)
    (h9 : Work.Spaces.HkMem α 4 (P9 α h)
      ∧ Work.FTS.Nonlin.Xn α (P9 α h) ≤ kA9 α Ci Cw * TOf α g g' h)
    (hs1 : Work.FTS.EllipticEst.SmoothOpen (P1 α g h))
    (hs2 : Work.FTS.EllipticEst.SmoothOpen (P2 α g' h))
    (hs3 : Work.FTS.EllipticEst.SmoothOpen (P3 α h))
    (hs4 : Work.FTS.EllipticEst.SmoothOpen (P4 α g h))
    (hs5 : Work.FTS.EllipticEst.SmoothOpen (P5 α g' h))
    (hs6 : Work.FTS.EllipticEst.SmoothOpen (P6 α h))
    (hs7 : Work.FTS.EllipticEst.SmoothOpen (P7 α g h))
    (hs8 : Work.FTS.EllipticEst.SmoothOpen (P8 α g' h))
    (hs9 : Work.FTS.EllipticEst.SmoothOpen (P9 α h))
    : Work.Spaces.HkMem α 4 (Rsum α g g' h) ∧ Work.FTS.EllipticEst.SmoothOpen (Rsum α g g' h)
      ∧ Work.FTS.Nonlin.Xn α (Rsum α g g' h) ≤ 1024 * ksum α Ci CF Cdz Cw * TOf α g g' h := by

  have hT : 0 ≤ TOf α g g' h := TOf_nonneg α g g' h
  have hK0 : 0 ≤ ksum α Ci CF Cdz Cw := ksum_nonneg hα hCi hCF hCdz hCw
  have h1' : Work.FTS.Nonlin.Xn α (P1 α g h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h1.2 (mul_le_mul_of_nonneg_right (kA1_le_ksum hα hCi hCF hCdz hCw) hT)
  have h2' : Work.FTS.Nonlin.Xn α (P2 α g' h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h2.2 (mul_le_mul_of_nonneg_right (kA2_le_ksum hα hCi hCF hCdz hCw) hT)
  have h3' : Work.FTS.Nonlin.Xn α (P3 α h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h3.2 (mul_le_mul_of_nonneg_right (kA3_le_ksum hα hCi hCF hCdz hCw) hT)
  have h4' : Work.FTS.Nonlin.Xn α (P4 α g h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h4.2 (mul_le_mul_of_nonneg_right (kA4_le_ksum hα hCi hCF hCdz hCw) hT)
  have h5' : Work.FTS.Nonlin.Xn α (P5 α g' h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h5.2 (mul_le_mul_of_nonneg_right (kA5_le_ksum hα hCi hCF hCdz hCw) hT)
  have h6' : Work.FTS.Nonlin.Xn α (P6 α h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h6.2 (mul_le_mul_of_nonneg_right (kA6_le_ksum hα hCi hCF hCdz hCw) hT)
  have h7' : Work.FTS.Nonlin.Xn α (P7 α g h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h7.2 (mul_le_mul_of_nonneg_right (kA7_le_ksum hα hCi hCF hCdz hCw) hT)
  have h8' : Work.FTS.Nonlin.Xn α (P8 α g' h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h8.2 (mul_le_mul_of_nonneg_right (kA8_le_ksum hα hCi hCF hCdz hCw) hT)
  have h9' : Work.FTS.Nonlin.Xn α (P9 α h) ≤ ksum α Ci CF Cdz Cw * TOf α g g' h :=
    le_trans h9.2 (mul_le_mul_of_nonneg_right (kA9_le_ksum hα hCi hCF hCdz hCw) hT)
  set R9 : ℝ → ℝ → ℝ := P9 α h with hR9
  set R8 : ℝ → ℝ → ℝ := P8 α g' h + R9 with hR8
  set R7 : ℝ → ℝ → ℝ := P7 α g h + R8 with hR7
  set R6 : ℝ → ℝ → ℝ := P6 α h + R7 with hR6
  set R5 : ℝ → ℝ → ℝ := P5 α g' h + R6 with hR5
  set R4 : ℝ → ℝ → ℝ := P4 α g h + R5 with hR4
  set R3 : ℝ → ℝ → ℝ := P3 α h + R4 with hR3
  set R2 : ℝ → ℝ → ℝ := P2 α g' h + R3 with hR2
  set R1 : ℝ → ℝ → ℝ := P1 α g h + R2 with hR1
  set B9 : ℝ := ksum α Ci CF Cdz Cw with hB9
  set B8 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B9) with hB8
  set B7 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B8) with hB7
  set B6 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B7) with hB6
  set B5 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B6) with hB5
  set B4 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B5) with hB4
  set B3 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B4) with hB3
  set B2 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B3) with hB2
  set B1 : ℝ := 2 * (ksum α Ci CF Cdz Cw + B2) with hB1
  have hR9sm : Work.FTS.EllipticEst.SmoothOpen R9 := by rw [hR9]; exact hs9
  have hR9mem : Work.Spaces.HkMem α 4 R9 := by rw [hR9]; exact h9.1
  have hR9x : Work.FTS.Nonlin.Xn α R9 ≤ B9 * TOf α g g' h := by
    rw [hR9, hB9]; exact h9'
  have hR8sm : Work.FTS.EllipticEst.SmoothOpen R8 := by
    rw [hR8]; exact Work.FTS.NonlinRows.smoothOpen_add hs8 hR9sm
  have hR8mem : Work.Spaces.HkMem α 4 R8 := by
    rw [hR8]; exact Work.FTS.EllipticEst.HkMem_add_open hs8 hR9sm h8.1 hR9mem
  have hR8x : Work.FTS.Nonlin.Xn α R8 ≤ B8 * TOf α g g' h := by
    rw [hR8, hB8]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs8 hR9sm h8.1 hR9mem
    calc Work.FTS.Nonlin.Xn α (P8 α g' h + R9)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P8 α g' h) + Work.FTS.Nonlin.Xn α R9) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B9 * TOf α g g' h) := by linarith [h8', hR9x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B9)) * TOf α g g' h := by ring
  have hR7sm : Work.FTS.EllipticEst.SmoothOpen R7 := by
    rw [hR7]; exact Work.FTS.NonlinRows.smoothOpen_add hs7 hR8sm
  have hR7mem : Work.Spaces.HkMem α 4 R7 := by
    rw [hR7]; exact Work.FTS.EllipticEst.HkMem_add_open hs7 hR8sm h7.1 hR8mem
  have hR7x : Work.FTS.Nonlin.Xn α R7 ≤ B7 * TOf α g g' h := by
    rw [hR7, hB7]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs7 hR8sm h7.1 hR8mem
    calc Work.FTS.Nonlin.Xn α (P7 α g h + R8)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P7 α g h) + Work.FTS.Nonlin.Xn α R8) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B8 * TOf α g g' h) := by linarith [h7', hR8x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B8)) * TOf α g g' h := by ring
  have hR6sm : Work.FTS.EllipticEst.SmoothOpen R6 := by
    rw [hR6]; exact Work.FTS.NonlinRows.smoothOpen_add hs6 hR7sm
  have hR6mem : Work.Spaces.HkMem α 4 R6 := by
    rw [hR6]; exact Work.FTS.EllipticEst.HkMem_add_open hs6 hR7sm h6.1 hR7mem
  have hR6x : Work.FTS.Nonlin.Xn α R6 ≤ B6 * TOf α g g' h := by
    rw [hR6, hB6]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs6 hR7sm h6.1 hR7mem
    calc Work.FTS.Nonlin.Xn α (P6 α h + R7)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P6 α h) + Work.FTS.Nonlin.Xn α R7) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B7 * TOf α g g' h) := by linarith [h6', hR7x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B7)) * TOf α g g' h := by ring
  have hR5sm : Work.FTS.EllipticEst.SmoothOpen R5 := by
    rw [hR5]; exact Work.FTS.NonlinRows.smoothOpen_add hs5 hR6sm
  have hR5mem : Work.Spaces.HkMem α 4 R5 := by
    rw [hR5]; exact Work.FTS.EllipticEst.HkMem_add_open hs5 hR6sm h5.1 hR6mem
  have hR5x : Work.FTS.Nonlin.Xn α R5 ≤ B5 * TOf α g g' h := by
    rw [hR5, hB5]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs5 hR6sm h5.1 hR6mem
    calc Work.FTS.Nonlin.Xn α (P5 α g' h + R6)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P5 α g' h) + Work.FTS.Nonlin.Xn α R6) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B6 * TOf α g g' h) := by linarith [h5', hR6x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B6)) * TOf α g g' h := by ring
  have hR4sm : Work.FTS.EllipticEst.SmoothOpen R4 := by
    rw [hR4]; exact Work.FTS.NonlinRows.smoothOpen_add hs4 hR5sm
  have hR4mem : Work.Spaces.HkMem α 4 R4 := by
    rw [hR4]; exact Work.FTS.EllipticEst.HkMem_add_open hs4 hR5sm h4.1 hR5mem
  have hR4x : Work.FTS.Nonlin.Xn α R4 ≤ B4 * TOf α g g' h := by
    rw [hR4, hB4]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs4 hR5sm h4.1 hR5mem
    calc Work.FTS.Nonlin.Xn α (P4 α g h + R5)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P4 α g h) + Work.FTS.Nonlin.Xn α R5) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B5 * TOf α g g' h) := by linarith [h4', hR5x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B5)) * TOf α g g' h := by ring
  have hR3sm : Work.FTS.EllipticEst.SmoothOpen R3 := by
    rw [hR3]; exact Work.FTS.NonlinRows.smoothOpen_add hs3 hR4sm
  have hR3mem : Work.Spaces.HkMem α 4 R3 := by
    rw [hR3]; exact Work.FTS.EllipticEst.HkMem_add_open hs3 hR4sm h3.1 hR4mem
  have hR3x : Work.FTS.Nonlin.Xn α R3 ≤ B3 * TOf α g g' h := by
    rw [hR3, hB3]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs3 hR4sm h3.1 hR4mem
    calc Work.FTS.Nonlin.Xn α (P3 α h + R4)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P3 α h) + Work.FTS.Nonlin.Xn α R4) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B4 * TOf α g g' h) := by linarith [h3', hR4x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B4)) * TOf α g g' h := by ring
  have hR2sm : Work.FTS.EllipticEst.SmoothOpen R2 := by
    rw [hR2]; exact Work.FTS.NonlinRows.smoothOpen_add hs2 hR3sm
  have hR2mem : Work.Spaces.HkMem α 4 R2 := by
    rw [hR2]; exact Work.FTS.EllipticEst.HkMem_add_open hs2 hR3sm h2.1 hR3mem
  have hR2x : Work.FTS.Nonlin.Xn α R2 ≤ B2 * TOf α g g' h := by
    rw [hR2, hB2]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs2 hR3sm h2.1 hR3mem
    calc Work.FTS.Nonlin.Xn α (P2 α g' h + R3)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P2 α g' h) + Work.FTS.Nonlin.Xn α R3) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B3 * TOf α g g' h) := by linarith [h2', hR3x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B3)) * TOf α g g' h := by ring
  have hR1sm : Work.FTS.EllipticEst.SmoothOpen R1 := by
    rw [hR1]; exact Work.FTS.NonlinRows.smoothOpen_add hs1 hR2sm
  have hR1mem : Work.Spaces.HkMem α 4 R1 := by
    rw [hR1]; exact Work.FTS.EllipticEst.HkMem_add_open hs1 hR2sm h1.1 hR2mem
  have hR1x : Work.FTS.Nonlin.Xn α R1 ≤ B1 * TOf α g g' h := by
    rw [hR1, hB1]
    have hstep := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα hs1 hR2sm h1.1 hR2mem
    calc Work.FTS.Nonlin.Xn α (P1 α g h + R2)
        ≤ 2 * (Work.FTS.Nonlin.Xn α (P1 α g h) + Work.FTS.Nonlin.Xn α R2) := hstep
      _ ≤ 2 * (ksum α Ci CF Cdz Cw * TOf α g g' h + B2 * TOf α g g' h) := by linarith [h1', hR2x]
      _ = (2 * (ksum α Ci CF Cdz Cw + B2)) * TOf α g g' h := by ring
  have hB1le : B1 ≤ 1024 * ksum α Ci CF Cdz Cw := by
    rw [hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hB9]
    nlinarith [hK0]
  have hR1eq : R1 = Rsum α g g' h := by
    rw [hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, Rsum]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hR1eq]; exact hR1mem
  · rw [← hR1eq]; exact hR1sm
  · rw [← hR1eq]
    exact le_trans hR1x (mul_le_mul_of_nonneg_right hB1le hT)

end Work.FTS.GalFields.RHS
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_pairIntegral_le_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/leaf_pairIntegral_le_HkSq`

The single-leaf pairing `∫_z ∫_θ ρ z θ · (D_z^b D_θ^a u z θ)²` of a leaf weight `ρ`
(`IsLeafW α a ρ`) at a slot of order `a + b ≤ 1` is dominated by the squared `ℋ¹`-norm
of `u` — with constant `1`.

The content is entirely pointwise.  On the *open* quadrant every leaf weight `ρ` of the
slot `a` is dominated by the slot weight `slotW α a` (`IsLeafW_le`), which in turn prices
the square of the slot derivative by the `ℋ¹`-integrand of `u`
(`H6Pair6Aux.slotW_dom`): together these give

  `ρ z θ · (D_z^bD_θ^a u z θ)² ≤ HkIntegrand α 1 u z θ`    (`θ ∈ (0, π/2)`),

which is `H6Pair6Aux.domLeaf_all`.  The two angular endpoints `θ = 0`, `θ = π/2` carry no
mass for `volume.restrict Iθ` (they form the null set on which the comparison can fail,
because there `sin(2θ) = 0` and the weights `w²σ^{-η}`, `w²σ^{-γ}` degenerate), so the
integral estimate follows by `integral_mono_of_nonneg`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open scoped Real Topology
open MeasureTheory

/-- For `volume.restrict Iθ` the two endpoints `0`, `π/2` are null, so `θ` lies in the open
interval almost everywhere.  (`Icc 0 (π/2)` and `Ioo 0 (π/2)` agree a.e.) -/
private theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- **The single-leaf pairing against the squared `ℋ^m`-norm.**  For a leaf weight `ρ` of
the slot `a`, a slot `(a,b)` of order at most `m` and an honest `ℋ^m`-datum `f`, the
leaf-weighted slot energy is dominated by `HkSq α m f` (with constant `1`). -/
private theorem leafSlot_le_HkSq {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {m a b : ℕ}
    (hmem : Work.Spaces.HkMem α m f) (hab : a + b ≤ m)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkSq α m f := by
  have hIoo := ae_mem_Ioo_Iθ
  -- the angular slice estimate, for every `z ∈ Iz`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z hz) ?_
    · filter_upwards [hIoo] with θ hθ
      exact mul_nonneg
        (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _)
    · filter_upwards [hIoo] with θ hθ
      exact Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hρ hθ hab
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hmem.2 ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    exact MeasureTheory.integral_nonneg_of_ae (hIoo.mono fun θ hθ =>
      mul_nonneg
        (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _))
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    exact hslice z hz

theorem leaf_pairIntegral_le_HkSq {α : ℝ} (hα : 0 < α) {u : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 1 u) {a b : ℕ} (hab : a + b ≤ 1)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2) ≤ Work.Spaces.HkSq α 1 u :=
  leafSlot_le_HkSq hα hmem hab hρ

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- **The pointwise majorant of the `ℋ⁴`-integrand of a radial product.** -/
theorem maj4_pt {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hB : 0 ≤ B) (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ B) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => X z * f z θ) z θ
      ≤ Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hBase : 0 ≤ 6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B)) hHk
  have hZ : (∑ i ∈ Finset.range (4 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 5 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
    calc (∑ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (4 + 1),
            (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) :=
          Finset.sum_le_sum fun i hi =>
            zslot4 hB hX hf hz hθ0 hθ1 hR i
              (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 5 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have hM : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0))
      ≤ 25 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
    calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1),
            (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 4
          · rw [if_pos hc]
            exact mslot4 hB hX hf hz hθ0 hθ1 hR i j hc.1 hc.2
          · rw [if_neg hc]
            exact hBase
      _ = 25 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
          ring
  rw [Work.Spaces.HkIntegrand]
  have h5 : (5 : ℝ) ≤ Maj4C := by norm_num [Maj4C]
  have h25 : (25 : ℝ) ≤ Maj4C := by norm_num [Maj4C]
  calc (∑ i ∈ Finset.range (4 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
      ≤ 5 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
        + 25 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := add_le_add hZ hM
    _ ≤ Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
        have hY : 0 ≤ B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
          mul_nonneg (sq_nonneg B) hHk
        have hM' : 6400 * 30 ≤ Maj4C := by norm_num [Maj4C]
        calc 5 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
              + 25 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
            = (6400 * 30) * (B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
          _ ≤ Maj4C * (B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) :=
              mul_le_mul_of_nonneg_right hM' hY
          _ = Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by ring

/-- **The level-`4` radial majorant**: `HkSq α 4 (X · f) ≤ C · B² · HkSq α 4 f`. -/
theorem radialMaj4 {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hB : 0 ≤ B) (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f)
    (hR : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Elliptic.DzdIter j X z| ≤ B) :
    Work.Spaces.HkSq α 4 (fun z θ => X z * f z θ)
      ≤ (Maj4C + 1) * B ^ 2 * Work.Spaces.HkSq α 4 f := by
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.HkIntegrand α 4 (fun z θ => X z * f z θ) z θ
        ≤ Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0, HkIntegrand_zero4]
      exact mul_nonneg (mul_nonneg Maj4C_pos.le (sq_nonneg B))
        (Work.Spaces.HkIntegrand_nonneg α 4 f 0 θ)
    · exact maj4_pt hB hX hf hzpos hθ.1 hθ.2
        (fun j hj => hR j hj z (Set.mem_Ioi.mpr hzpos))
  have hIoo : (volume.restrict Work.Spaces.Iθ) = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
      MeasureTheory.Ioo_ae_eq_Icc
    exact Measure.restrict_congr_set haeeq.symm
  have hmaj_slice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Maj4C * B ^ 2 *
      Work.Spaces.HkIntegrand α 4 f z θ) Work.Spaces.Iθ := by
    intro z hz
    simpa only [IntegrableOn] using (hm.1 z hz).const_mul (Maj4C * B ^ 2)
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => X z * f z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz
    refine integral_mono_of_nonneg ?_ (hmaj_slice z hz) ?_
    · exact Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 4 (fun z θ => X z * f z θ) z θ
    · rw [hIoo]
      exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hpt z hz θ hθ)
  have hmaj_z : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) Work.Spaces.Iz := by
    simpa only [IntegrableOn, MeasureTheory.integral_const_mul] using
      (hm.2.const_mul (Maj4C * B ^ 2))
  have houter : (∫ z in Work.Spaces.Iz,
      ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => X z * f z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    refine integral_mono_of_nonneg ?_ hmaj_z ?_
    · exact Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact hslice z hz
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
      = Maj4C * B ^ 2 * Work.Spaces.HkSq α 4 f := by
    rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
        = (Maj4C * B ^ 2) * ∫ z in Work.Spaces.Iz,
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) from by
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
        simp only [MeasureTheory.integral_const_mul])]
    unfold Work.Spaces.HkSq
    ring
  have h1 : Work.Spaces.HkSq α 4 (fun z θ => X z * f z θ)
      ≤ Maj4C * B ^ 2 * Work.Spaces.HkSq α 4 f := houter.trans (le_of_eq hval)
  have h0 : 0 ≤ B ^ 2 * Work.Spaces.HkSq α 4 f :=
    mul_nonneg (sq_nonneg B) (Work.Spaces.HkSq_nonneg α 4 f)
  calc Work.Spaces.HkSq α 4 (fun z θ => X z * f z θ)
      ≤ Maj4C * B ^ 2 * Work.Spaces.HkSq α 4 f := h1
    _ = Maj4C * (B ^ 2 * Work.Spaces.HkSq α 4 f) := by ring
    _ ≤ (Maj4C + 1) * (B ^ 2 * Work.Spaces.HkSq α 4 f) :=
        mul_le_mul_of_nonneg_right (by linarith) h0
    _ = (Maj4C + 1) * B ^ 2 * Work.Spaces.HkSq α 4 f := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj6Split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## The pointwise majorant of the whole integrand -/

theorem maj_pt {α Blo Bhi : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hBlo : 0 ≤ Blo) (hBhi : 0 ≤ Bhi)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hLo : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ Blo)
    (hHi : ∀ j : ℕ, j ≤ 6 → |Work.Elliptic.DzdIter j X z| ≤ Bhi) :
    Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ
      ≤ MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
  have hHk6 : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hHk2 : 0 ≤ Work.Spaces.HkIntegrand α 2 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 2 f z θ
  have hBase : 0 ≤ 200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
      + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    have h : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
      add_nonneg (mul_nonneg (sq_nonneg Blo) hHk6) (mul_nonneg (sq_nonneg Bhi) hHk2)
    linarith
  -- the pure `z`-part
  have hZ : (∑ i ∈ Finset.range (6 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 7 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
    calc (∑ i ∈ Finset.range (6 + 1),
          (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (6 + 1),
            (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) :=
          Finset.sum_le_sum fun i hi =>
            zslot6_split hBlo hBhi hX hf hz hθ0 hθ1 hLo hHi i
              (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 7 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- the mixed part
  have hM : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0))
      ≤ 49 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
    calc (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ ∑ _i ∈ Finset.range (6 + 1), ∑ _j ∈ Finset.range (6 + 1),
            (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 6
          · rw [if_pos hc]
            exact mslot6_split hBlo hBhi hX hf hz hθ0 hθ1 hLo hHi i j hc.1 hc.2
          · rw [if_neg hc]
            exact hBase
      _ = 49 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
          simp only [Finset.sum_const, Finset.card_range, Nat.cast_ofNat, nsmul_eq_mul]
          norm_num
          ring
  rw [Work.Spaces.HkIntegrand]
  have h7 : (7 : ℝ) ≤ MajC := by norm_num [MajC]
  have h49 : (49 : ℝ) ≤ MajC := by norm_num [MajC]
  calc (∑ i ∈ Finset.range (6 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      + ∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
      ≤ 7 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))
        + 49 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := add_le_add hZ hM
    _ ≤ MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
        have hY : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
          add_nonneg (mul_nonneg (sq_nonneg Blo) hHk6) (mul_nonneg (sq_nonneg Bhi) hHk2)
        have hM' : 200704 * 56 ≤ MajC := by norm_num [MajC]
        calc 7 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
                + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))
              + 49 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
                + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))
            = (200704 * 56) * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by ring
          _ ≤ MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) :=
              mul_le_mul_of_nonneg_right hM' hY

/-! ## The engine -/

/-- **The level-matched radial majorant at level `6`.**  If `X : ℝ → ℝ` is `C⁶` on `(0,∞)`
with `|D_z^j X| ≤ Blo` for `j ≤ 4` and `≤ Bhi` for `j ≤ 6`, and `f` is `C^∞` on the open
quadrant with `HkMem α 6 f`, then

  `HkSq α 6 (X · f) ≤ C · (Blo² · HkSq α 6 f + Bhi² · HkSq α 2 f)`,

with `C` universal (independent of `α`, `X`, `f`, `Blo`, `Bhi`). -/
theorem radialMaj6_split : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (X : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (Blo Bhi : ℝ),
    ContDiffOn ℝ 6 X (Set.Ioi 0) → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 f → 0 ≤ Blo → 0 ≤ Bhi →
    (∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Elliptic.DzdIter j X z| ≤ Blo) →
    (∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Elliptic.DzdIter j X z| ≤ Bhi) →
    Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ C * (Blo ^ 2 * Work.Spaces.HkSq α 6 f + Bhi ^ 2 * Work.Spaces.HkSq α 2 f) := by
  refine ⟨MajC + 1, by linarith [MajC_pos], ?_⟩
  intro α X f Blo Bhi hX hf hm6 hBlo hBhi hLo hHi
  have hm2 : Work.Spaces.HkMem α 2 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf 2 (by norm_num) hm6
  -- the pointwise majorant on the open quadrant
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ
        ≤ MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0, HkIntegrand_zero]
      have h : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f 0 θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f 0 θ :=
        add_nonneg (mul_nonneg (sq_nonneg Blo) (Work.Spaces.HkIntegrand_nonneg α 6 f 0 θ))
          (mul_nonneg (sq_nonneg Bhi) (Work.Spaces.HkIntegrand_nonneg α 2 f 0 θ))
      exact mul_nonneg MajC_pos.le h
    · exact maj_pt hBlo hBhi hX hf hzpos hθ.1 hθ.2
        (fun j hj => hLo j hj z (Set.mem_Ioi.mpr hzpos))
        (fun j hj => hHi j hj z (Set.mem_Ioi.mpr hzpos))
  -- the inner comparison
  have hIoo : (volume.restrict Work.Spaces.Iθ) = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
      MeasureTheory.Ioo_ae_eq_Icc
    exact Measure.restrict_congr_set haeeq.symm
  have hmaj_slice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => MajC *
      (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) Work.Spaces.Iθ := by
    intro z hz
    have h1 : IntegrableOn (fun θ => Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ)
        Work.Spaces.Iθ := (hm6.1 z hz).const_mul _
    have h2 : IntegrableOn (fun θ => Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)
        Work.Spaces.Iθ := (hm2.1 z hz).const_mul _
    simpa only [Pi.add_apply, IntegrableOn] using (h1.add h2).const_mul MajC
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    intro z hz
    refine integral_mono_of_nonneg ?_ (hmaj_slice z hz) ?_
    · exact Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 (fun z θ => X z * f z θ) z θ
    · rw [hIoo]
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact hpt z hz θ hθ
  -- integrability of the outer majorant and the evaluation of its integral
  have hA : IntegrableOn (fun z => Blo ^ 2 * (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 f z θ)) Work.Spaces.Iz := hm6.2.const_mul _
  have hB : IntegrableOn (fun z => Bhi ^ 2 * (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 2 f z θ)) Work.Spaces.Iz := hm2.2.const_mul _
  have hae : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))
        = MajC * (Blo ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
            + Bhi ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 f z θ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    · exact (hm6.1 z hz).const_mul _
    · exact (hm2.1 z hz).const_mul _
  have hmaj_z : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, MajC *
      (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) Work.Spaces.Iz := by
    refine ((hA.add hB).const_mul MajC).congr ?_
    filter_upwards [hae] with z hz
    simp only [Pi.add_apply]
    exact hz.symm
  -- the outer comparison
  have houter : (∫ z in Work.Spaces.Iz,
      ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, MajC *
          (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    refine integral_mono_of_nonneg ?_ hmaj_z ?_
    · exact Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact hslice z hz
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, MajC *
      (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))
      = MajC * (Blo ^ 2 * Work.Spaces.HkSq α 6 f + Bhi ^ 2 * Work.Spaces.HkSq α 2 f) := by
    rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hA hB, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    unfold Work.Spaces.HkSq
    ring
  have hHkSq := houter.trans_eq hval
  exact hHkSq.trans (by
    have h0 : 0 ≤ Blo ^ 2 * Work.Spaces.HkSq α 6 f + Bhi ^ 2 * Work.Spaces.HkSq α 2 f :=
      add_nonneg (mul_nonneg (sq_nonneg Blo) (Work.Spaces.HkSq_nonneg α 6 f))
        (mul_nonneg (sq_nonneg Bhi) (Work.Spaces.HkSq_nonneg α 2 f))
    have hle : MajC ≤ MajC + 1 := by linarith
    calc MajC * (Blo ^ 2 * Work.Spaces.HkSq α 6 f + Bhi ^ 2 * Work.Spaces.HkSq α 2 f)
        ≤ (MajC + 1) * (Blo ^ 2 * Work.Spaces.HkSq α 6 f
            + Bhi ^ 2 * Work.Spaces.HkSq α 2 f) :=
          mul_le_mul_of_nonneg_right hle h0)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.vfs4_A1_slot4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- The statement uses the notation `π` for `Real.pi`.  This file is compiled with
-- `autoImplicit = false`, so the locale has to be opened for `π` to resolve (as in the
-- sibling `vfs4_VfsA2_jet`).
open scoped Real

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open Work.FTS.StrongPersist.L3Rhs (VfsA1 VfsGc dthU_iter_VfsA1_of_mem)

/-- **The order-`4` `dthU`-jet of `VfsA1 α` against the weight `sin(2θ)^{-γ(α)}`.**

`VfsA1 α = (3/2)·dthU (Γ/c)`, hence `dthU^[4] (VfsA1 α) = (3/2)·dthU^[5] (Γ/c)`.  The angular
jet bound `|dthU^m Γ| ≤ 10⁵·Γ` for `m ≤ 6` (`LocData6.DthIter_Gam_abs_le6`, via
`LocData.DthIter_rad_eq`) and `1/c ≤ 10` (`Spaces.c_bounds`) give

`|dthU^[4] (VfsA1 α) θ| ≤ (3/2)·10·10⁵·Γ(θ) = 1.5·10⁶·Γ(θ)`.

Squaring, `Γ(θ)² ≤ sin(2θ)^{2α/3}` (`Coercivity.Gam_sq_le_sin_two`) and
`2α/3 - γ(α) = -(1 - 17α/30)` (with `γ(α) = 1 + α/10`) give the claim, the constant being
`(1.5·10⁶)² = 2.25·10¹² = 2250000000000`. -/
theorem vfs4_A1_slot4 :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.dthU^[4] (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
  intro α hα hα1 θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs_pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hGam : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
  -- ## 1. the fourth jet of `VfsA1 α` is the fifth jet of `Γ/c`
  have h1 : Work.Spaces.dthU^[4] (VfsA1 α) θ = (3 / 2) * Work.Spaces.dthU^[5] (VfsGc α) θ :=
    dthU_iter_VfsA1_of_mem hθ 4
  -- ## 2. the constant factor `1/c` comes out of the jet
  have h2 : Work.Spaces.dthU^[5] (VfsGc α) θ
      = (1 / Work.Spaces.c α) * Work.Spaces.dthU^[5] (fun t => Work.Spaces.Gam α t) θ := by
    have hfun : VfsGc α = fun t : ℝ => (1 / Work.Spaces.c α) * Work.Spaces.Gam α t := by
      funext t
      rw [VfsGc]
      ring
    rw [hfun]
    simpa using congrFun (Work.Spaces.dthU_iter_const_mul 5 (1 / Work.Spaces.c α)
      (fun t => Work.Spaces.Gam α t)) θ
  -- ## 3. the angular jet bound for `Γ`
  have h3 : |Work.Spaces.dthU^[5] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
    have hkey := Work.FTS.LocData6.DthIter_Gam_abs_le6 5 (by norm_num) α hα hα1 hθI
    rw [Work.FTS.LocData.DthIter_rad_eq 5 (fun t => Work.Spaces.Gam α t) 0 θ] at hkey
    exact hkey
  -- ## 4. `1/c ≤ 10`
  have hc_inv : 1 / Work.Spaces.c α ≤ 10 := by
    have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : (0 : ℝ) < Work.Spaces.c α := by linarith
    rw [div_le_iff₀ hcpos]
    linarith
  -- ## 5. the unweighted square bound, with the constant `(1.5·10⁶)²`
  have h4 : (Work.Spaces.dthU^[4] (VfsA1 α) θ) ^ 2
      ≤ 2250000000000 * (Work.Spaces.Gam α θ) ^ 2 := by
    have hcpos : (0 : ℝ) < 1 / Work.Spaces.c α := by
      have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
      exact one_div_pos.mpr (by linarith)
    have heq : |Work.Spaces.dthU^[4] (VfsA1 α) θ|
        = (3 / 2) * ((1 / Work.Spaces.c α)
            * |Work.Spaces.dthU^[5] (fun t => Work.Spaces.Gam α t) θ|) := by
      rw [h1, h2]
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2),
        abs_of_pos hcpos]
    have hb : |Work.Spaces.dthU^[4] (VfsA1 α) θ| ≤ 1500000 * Work.Spaces.Gam α θ := by
      rw [heq]
      calc (3 / 2) * ((1 / Work.Spaces.c α)
              * |Work.Spaces.dthU^[5] (fun t => Work.Spaces.Gam α t) θ|)
          ≤ (3 / 2) * ((1 / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hcpos.le) (by norm_num)
        _ ≤ (3 / 2) * (10 * (100000 * Work.Spaces.Gam α θ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hc_inv (mul_nonneg (by norm_num) hGam))
              (by norm_num)
        _ = 1500000 * Work.Spaces.Gam α θ := by ring
    calc (Work.Spaces.dthU^[4] (VfsA1 α) θ) ^ 2
        = |Work.Spaces.dthU^[4] (VfsA1 α) θ| ^ 2 := by rw [sq_abs]
      _ ≤ (1500000 * Work.Spaces.Gam α θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = 2250000000000 * (Work.Spaces.Gam α θ) ^ 2 := by ring
  -- ## 6. pass to the weighted estimate
  have hTγ : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs_pos.le _
  have hexp : 2 * α / 3 + -(Work.Spaces.gam α) = -(1 - 17 * α / 30) := by
    rw [Work.Spaces.gam]
    ring
  have hprod : (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
    rw [← Real.rpow_add hs_pos, hexp]
  calc (Work.Spaces.dthU^[4] (VfsA1 α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (2250000000000 * (Work.Spaces.Gam α θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right h4 hTγ
    _ = 2250000000000 * ((Work.Spaces.Gam α θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ ≤ 2250000000000 * ((Real.sin (2 * θ)) ^ (2 * α / 3)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (Work.Coercivity.Gam_sq_le_sin_two α hα θ hθI) hTγ)
          (by norm_num)
    _ = 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by rw [hprod]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux.summandM_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.StrongEps.E4R3.Nblock6.Tools

/-- **The mixed-slot summand of the level-`6` product bound.**  Every first-order slot
`D_z^bD_θ^a A · D_z^{j-b}D_θ^{i-a+1}f · W` of the Leibniz expansion of `D_z^jD_θ^i(A · D_θ f)`
(with `i ≥ 1`, `i + j ≤ 6`) is priced against the budget `ptdBud`.

The proof is a case analysis on the `θ`-order `a` of the `A`-slot and the total order
`a + b` of the `A`-slot.  Exactly one of the two factors carries the weight `W`:

* `a + b = 0`: the `A`-slot is `A` itself, so `|A| ≤ MA` and the `f`-slot
  `D_θ^{i+1}f` (order `≤ 7`) is absorbed by `MA²·HkIntegrand 7 f`;
* `1 ≤ a + b ≤ 4`: the `A`-slot is priced by the pointwise price `CP_price`
  (order `≤ 4`) and the `f`-slot (order `≤ 6`) carries `W`, giving `HkIntegrand 6 f`;
* `a + b ≥ 5`, `a = 0`: forced to be the exceptional slot `D_z⁵A · D_θ²f · W`
  (`i = 1`, `j = b = 5`), which is a summand of the budget;
* `a + b ≥ 5`, `a ≥ 1`: the `A`-slot (θ-order `≥ 1`, order `≤ 6`) carries `W` and
  the `f`-slot has order `≤ 7 - 5 = 2`, so it is priced by `CP_price`. -/
theorem summandM_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {A f : ℝ → ℝ → ℝ} {MA : ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmA : Work.Spaces.HkMem α 6 A) (hmf : Work.Spaces.HkMem α 6 f)
    (hMA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {i j a b : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 6) (ha : a ≤ i) (hb : b ≤ j) :
    (Work.Spaces.mixed b a A z θ * Work.Spaces.mixed (j - b) (i - a + 1) f z θ
        * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptdK2
          * Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptdBud α A f MA z θ := by
  have hγpos : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγnn : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγpos.le
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hbud : 0 ≤ ptdBud α A f MA z θ := ptdBud_nonneg hα A f MA z θ
  have hKpos : 0 < ptdK2 := ptdK2_pos
  have hK1 : 1 ≤ ptdK2 := one_le_ptdK2
  have hshape1 : (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2
      = (mixed b a A z θ) ^ 2 * (mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2 := by
    ring
  have hshape2 : (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2
      = (mixed b a A z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a + 1) f z θ) ^ 2 := by
    ring
  rcases Nat.eq_zero_or_pos (a + b) with hp0 | hppos
  · -- the `A`-slot is `A` itself
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0
    subst hb0
    have hY : (mixed j (i + 1) f z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 7 f z θ :=
      sq_le_HkIntegrand_mixed α 7 f z θ (i + 1) j (by omega) (by omega)
    have hA2 : (A z θ) ^ 2 ≤ MA ^ 2 := by
      have hh := abs_le.mp (hMA z θ hz hθ0 hθ1)
      nlinarith [hh.1, hh.2]
    rw [hshape1]
    calc (A z θ) ^ 2 * (mixed j (i + 1) f z θ * Wt α z θ) ^ 2
        ≤ MA ^ 2 * HkIntegrand α 7 f z θ :=
          mul_le_mul hA2 hY (sq_nonneg _) (sq_nonneg MA)
      _ ≤ ptdBud α A f MA z θ := MAsq_mul_Hk7_le_ptdBud hα A f MA z θ
      _ ≤ ptdK2 * ptdBud α A f MA z θ := le_mul_of_one_le_left hbud hK1
  · by_cases hp4 : a + b ≤ 4
    · -- the `A`-slot is priced pointwise, the `f`-slot carries the weight
      have hYq : (i - a + 1) + (j - b) ≤ 6 := by omega
      have hY : (mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2
          ≤ HkIntegrand α 6 f z θ :=
        sq_le_HkIntegrand_mixed α 6 f z θ (i - a + 1) (j - b) (by omega) hYq
      have hX : (mixed b a A z θ) ^ 2 ≤ CP / (gam α - 1) * HkSq α 6 A :=
        CP_price α A b a hα hα1 hA hmA (by omega) hz hθmem
      rw [hshape1]
      calc (mixed b a A z θ) ^ 2 * (mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2
          ≤ (CP / (gam α - 1) * HkSq α 6 A) * HkIntegrand α 6 f z θ :=
            mul_le_mul hX hY (sq_nonneg _)
              (mul_nonneg (div_nonneg CP_pos.le hγpos.le) (HkSq_nonneg α 6 A))
        _ = CP * ((gam α - 1)⁻¹ * HkSq α 6 A * HkIntegrand α 6 f z θ) := by
            rw [div_eq_mul_inv]; ring
        _ ≤ ptdK2 * ((gam α - 1)⁻¹ * HkSq α 6 A * HkIntegrand α 6 f z θ) :=
            mul_le_mul_of_nonneg_right CP_le_ptdK2
              (mul_nonneg (mul_nonneg hγnn (HkSq_nonneg α 6 A))
                (HkIntegrand_nonneg α 6 f z θ))
        _ ≤ ptdK2 * ptdBud α A f MA z θ :=
            mul_le_mul_of_nonneg_left (inv_hA_mul_Hk6f_le_ptdBud hα A f MA z θ) hKpos.le
    · by_cases ha0 : a = 0
      · -- the exceptional slot `D_z⁵A · D_θ²f · W`
        have hb5 : b = 5 := by omega
        have hi1 : i = 1 := by omega
        have hj5 : j = 5 := by omega
        subst ha0
        subst hb5
        subst hi1
        subst hj5
        have he : (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2
            ≤ ptdK2 * ptdBud α A f MA z θ :=
          le_trans (exc_le_ptdBud hα A f MA z θ) (le_mul_of_one_le_left hbud hK1)
        simpa using he
      · -- the `A`-slot carries the weight (θ-order `≥ 1`), the `f`-slot is priced
        have hX : (mixed b a A z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 6 A z θ :=
          sq_le_HkIntegrand_mixed α 6 A z θ a b (by omega) (by omega)
        have hYq : (i - a + 1) + (j - b) ≤ 4 := by omega
        have hY : (mixed (j - b) (i - a + 1) f z θ) ^ 2 ≤ CP / (gam α - 1) * HkSq α 6 f :=
          CP_price α f (j - b) (i - a + 1) hα hα1 hf hmf hYq hz hθmem
        rw [hshape2]
        calc (mixed b a A z θ * Wt α z θ) ^ 2 * (mixed (j - b) (i - a + 1) f z θ) ^ 2
            ≤ HkIntegrand α 6 A z θ * (CP / (gam α - 1) * HkSq α 6 f) :=
              mul_le_mul hX hY (sq_nonneg _) (HkIntegrand_nonneg α 6 A z θ)
          _ = CP * ((gam α - 1)⁻¹ * HkSq α 6 f * HkIntegrand α 6 A z θ) := by
              rw [div_eq_mul_inv]; ring
          _ ≤ ptdK2 * ((gam α - 1)⁻¹ * HkSq α 6 f * HkIntegrand α 6 A z θ) :=
              mul_le_mul_of_nonneg_right CP_le_ptdK2
                (mul_nonneg (mul_nonneg hγnn (HkSq_nonneg α 6 f))
                  (HkIntegrand_nonneg α 6 A z θ))
          _ ≤ ptdK2 * ptdBud α A f MA z θ :=
              mul_le_mul_of_nonneg_left (inv_hf_mul_Hk6A_le_ptdBud hα A f MA z θ) hKpos.le

end Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux.summandZ_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux

open Work.Spaces

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The two `(γ-1)⁻¹`-blocks of the budget -/

/-- The `(γ-1)⁻¹ · HkSq α 6 A · HkIntegrand α 6 f`-block is a summand of the budget. -/
private theorem inv_HkSqA_mul_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ) ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr (by rw [gam_sub_one]; linarith)
  have h1 : 0 ≤ MA ^ 2 * HkIntegrand α 7 f z θ :=
    mul_nonneg (sq_nonneg MA) (HkIntegrand_nonneg α 7 f z θ)
  have h2 : 0 ≤ (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ) :=
    mul_nonneg hγ (mul_nonneg (HkSq_nonneg α 6 f) (HkIntegrand_nonneg α 6 A z θ))
  have heq : ptdBud α A f MA z θ
      = ((gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ)
         + (gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ))
        + (MA ^ 2 * HkIntegrand α 7 f z θ
           + (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2) := by
    rw [ptdBud]; ring
  rw [heq]; linarith

/-- The `(γ-1)⁻¹ · HkSq α 6 f · HkIntegrand α 6 A`-block is a summand of the budget. -/
private theorem inv_HkSqf_mul_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ) ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr (by rw [gam_sub_one]; linarith)
  have h1 : 0 ≤ MA ^ 2 * HkIntegrand α 7 f z θ :=
    mul_nonneg (sq_nonneg MA) (HkIntegrand_nonneg α 7 f z θ)
  have h2 : 0 ≤ (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ) :=
    mul_nonneg hγ (mul_nonneg (HkSq_nonneg α 6 A) (HkIntegrand_nonneg α 6 f z θ))
  have heq : ptdBud α A f MA z θ
      = ((gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ)
         + (gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ))
        + (MA ^ 2 * HkIntegrand α 7 f z θ
           + (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2) := by
    rw [ptdBud]; ring
  rw [heq]; linarith

/-- The `A`-priced block, scaled by the universal constant `CP`, is dominated by the target
`ptdK2 · ptdBud`. -/
private theorem blockA_le {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    CP * ((gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ))
      ≤ ptdK2 * ptdBud α A f MA z θ := by
  have h1 := mul_le_mul_of_nonneg_left (inv_HkSqA_mul_le_ptdBud hα A f MA z θ) (le_of_lt CP_pos)
  have h2 := mul_le_mul_of_nonneg_right CP_le_ptdK2 (ptdBud_nonneg hα A f MA z θ)
  linarith

/-- The `f`-priced block, scaled by the universal constant `CP`, is dominated by the target
`ptdK2 · ptdBud`. -/
private theorem blockf_le {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    CP * ((gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ))
      ≤ ptdK2 * ptdBud α A f MA z θ := by
  have h1 := mul_le_mul_of_nonneg_left (inv_HkSqf_mul_le_ptdBud hα A f MA z θ) (le_of_lt CP_pos)
  have h2 := mul_le_mul_of_nonneg_right CP_le_ptdK2 (ptdBud_nonneg hα A f MA z θ)
  linarith

/-! The main estimate -/

theorem summandZ_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {A f : ℝ → ℝ → ℝ} {MA : ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmA : Work.Spaces.HkMem α 6 A) (hmf : Work.Spaces.HkMem α 6 f)
    (hMA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {j b : ℕ} (hj : j ≤ 6) (hb : b ≤ j) :
    (Work.Spaces.DzIter b A z θ * Work.Spaces.mixed (j - b) 1 f z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptdK2
          * Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptdBud α A f MA z θ := by
  have hγnn : 0 ≤ CP / (gam α - 1) :=
    div_nonneg (le_of_lt CP_pos) (by rw [gam_sub_one]; linarith)
  -- the first factor is a `HkIntegrand α 6 A`-slot whenever `b ≤ 6`
  have hzslot : (DzIter b A z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
      ≤ HkIntegrand α 6 A z θ := sq_le_HkIntegrand_z α 6 A z θ b (by omega)
  by_cases hB : j - b ≤ 3
  · -- ### Case B: the `f`-factor has order `≤ 4` and is priced by the norm
    have hprice : (mixed (j - b) 1 f z θ) ^ 2 ≤ CP / (gam α - 1) * HkSq α 6 f :=
      CP_price α f (j - b) 1 hα hα1 hf hmf (by omega) hz ⟨hθ0, hθ1⟩
    have hsplit : (DzIter b A z θ * mixed (j - b) 1 f z θ
          * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
        = (DzIter b A z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          * (mixed (j - b) 1 f z θ) ^ 2 := by ring
    rw [hsplit]
    calc (DzIter b A z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          * (mixed (j - b) 1 f z θ) ^ 2
        ≤ HkIntegrand α 6 A z θ * (CP / (gam α - 1) * HkSq α 6 f) :=
          mul_le_mul hzslot hprice (sq_nonneg _) (HkIntegrand_nonneg α 6 A z θ)
      _ = CP * ((gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 A z θ)) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ ptdK2 * ptdBud α A f MA z θ := blockf_le hα A f MA z θ
  · -- ### `j - b ≥ 4`, so `b ≤ 4`: the `A`-factor (order `≤ 4`) is the priced one
    have hb4 : b ≤ 4 := by omega
    by_cases h5 : j - b ≤ 5
    · -- the `f`-factor is a mixed slot of `HkIntegrand α 6 f` (order `1 + (j-b) ≤ 6`)
      have hprice : (DzIter b A z θ) ^ 2 ≤ CP / (gam α - 1) * HkSq α 6 A := by
        have h := CP_price α A b 0 hα hα1 hA hmA (by omega) hz ⟨hθ0, hθ1⟩
        simpa only [mixed_zero_right] using h
      have hfslot : (mixed (j - b) 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          ≤ HkIntegrand α 6 f z θ :=
        le_trans (sq_light_le_sq_Wt hα hα1 hz hθ0 hθ1 (mixed (j - b) 1 f z θ))
          (sq_le_HkIntegrand_mixed α 6 f z θ 1 (j - b) (by norm_num) (by omega))
      have hsplit : (DzIter b A z θ * mixed (j - b) 1 f z θ
            * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          = (DzIter b A z θ) ^ 2
            * (mixed (j - b) 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 := by ring
      rw [hsplit]
      calc (DzIter b A z θ) ^ 2
            * (mixed (j - b) 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          ≤ (CP / (gam α - 1) * HkSq α 6 A) * HkIntegrand α 6 f z θ :=
            mul_le_mul hprice hfslot (sq_nonneg _)
              (mul_nonneg hγnn (HkSq_nonneg α 6 A))
        _ = CP * ((gam α - 1)⁻¹ * (HkSq α 6 A * HkIntegrand α 6 f z θ)) := by
            rw [div_eq_mul_inv]; ring
        _ ≤ ptdK2 * ptdBud α A f MA z θ := blockA_le hα A f MA z θ
    · -- ### `j - b = 6`, hence `j = 6` and `b = 0`: the `MA²`-slot of the budget
      have hj6 : j = 6 := by omega
      have hb0 : b = 0 := by omega
      have hMA0 : 0 ≤ MA :=
        le_trans (abs_nonneg _)
          (hMA 1 (Real.pi / 4) (by norm_num) (by linarith [Real.pi_pos])
            (by linarith [Real.pi_pos]))
      have hAsq : (A z θ) ^ 2 ≤ MA ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg hMA0]
        exact hMA z θ hz hθ0 hθ1
      have hfslot : (mixed 6 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          ≤ HkIntegrand α 7 f z θ :=
        le_trans (sq_light_le_sq_Wt hα hα1 hz hθ0 hθ1 (mixed 6 1 f z θ))
          (sq_le_HkIntegrand_mixed α 7 f z θ 1 6 (by norm_num) (by norm_num))
      subst hb0
      subst hj6
      have hsplit : (DzIter 0 A z θ * mixed (6 - 0) 1 f z θ
            * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          = (A z θ) ^ 2
            * (mixed 6 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 := by
        simp only [DzIter_zero]
        ring
      rw [hsplit]
      calc (A z θ) ^ 2 * (mixed 6 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
          ≤ MA ^ 2 * HkIntegrand α 7 f z θ :=
            mul_le_mul hAsq hfslot (sq_nonneg _) (sq_nonneg MA)
        _ ≤ ptdBud α A f MA z θ := MAsq_mul_Hk7_le_ptdBud hα A f MA z θ
        _ ≤ ptdK2 * ptdBud α A f MA z θ :=
            le_mul_of_one_le_left (ptdBud_nonneg hα A f MA z θ) one_le_ptdK2

end Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtDthAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.HkMem_Jeps_succ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000


end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.hasDerivAt_integral_diag_var =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace Work.FTS.StrongEps.EpsE4Thr


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Work.Xn_le_sqrt_two_mul_of_Jeps_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Work

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Two elementary closure facts for the `ℋ^k`-machinery

The main theorem below compares the `ℋ⁴`-norms of `g₀` and of its mollification `J_ε g₀` by the
triangle inequality, for which the difference `g₀ - J_ε g₀` must be *in* `ℋ⁴`.  Since both
summands are `C^∞` on the open quadrant and in `ℋ⁴`, this follows from the closure of `ℋ^k`
under addition together with the (unconditional) invariance of the `ℋ^k`-integrand under
negation. -/

/-- `SmoothOpen` is closed under pointwise negation. -/
private theorem smoothOpen_neg_of {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  have hfun : Function.uncurry (fun z θ => -f z θ) = -(Function.uncurry f) := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact hf.neg

/-- `HkMem` is closed under pointwise negation: the `ℋ^k`-integrand of `-f` *equals* that of
`f` (`HkIntegrand_neg`), so no regularity hypothesis is needed. -/
private theorem hkMem_neg_of {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  have hI : ∀ z θ, Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ
      = Work.Spaces.HkIntegrand α k f z θ := by
    intro z θ
    exact congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ
  constructor
  · intro z hz
    refine IntegrableOn.congr_fun (hf.1 z hz) (fun θ _ => ?_) measurableSet_Icc
    exact (hI z θ).symm
  · have h : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ)
        = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hI z θ)
    rw [h]
    exact hf.2


/-- `HkSq` only sees the pointwise values of the profile. -/
private theorem hkSq_congr_pt {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, f z θ = g z θ) : Work.Spaces.HkSq α k f = Work.Spaces.HkSq α k g :=
  Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ _ _ _ => h z θ)

/-- `HkNorm` only sees the pointwise values of the profile. -/
private theorem hkNorm_congr_pt {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, f z θ = g z θ) : Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hkSq_congr_pt h]





end Work.FTS.StrongEps.EpsE4Work
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsGlue =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ModDiffAux.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ModDiffAux/Assembly` — the assembly of `ModDiffClassC` from the three `L₁₂`-differences

The two modulation constants are, by definition (`Construction/Defs.lean`,
`Construction/MufunS.lean`),

  `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)`,
  `μ  = (1/(2α))·(L₁₂(N₀)(0) + L₁₂(N)(0) + L₁₂(3 D_θ g/(1+z))(0))`,

so the difference of the two constants at `W₁`, `W₂` is the explicit linear combination of the
three `L₁₂`-zero-mode differences `ΔN₀`, `ΔN`, `ΔT`.  `modDiff_of_L12_bounds` is the assembly: it
takes the three *bounds* (linear in `|W₁−W₂|_{ℋ⁵}`, with constants `K₀, K_N, K_T`) and produces the
two clauses of `ModDiffClassC` with the constant
`K := max ((1/(2α))·(K₀+K_N+K_T)) (K₀+K_N) + 1`.

The three bounds themselves are supplied by `ModDiffAux.L12N0DiffClassC`,
`ModDiffAux.L12NDiffClassC` and `ModDiffAux.L12_transport_diff_classC`. -/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ModDiffAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The assembly of the two modulation-difference bounds from the three `L₁₂`-difference
bounds** (all three of the shape `K·(1 + |W₁|_{ℋ⁵} + |W₂|_{ℋ⁵})·|W₁−W₂|_{ℋ⁵}`). -/
theorem modDiff_of_L12_bounds {α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {Ce Cs : ℝ} {Φs : Fn} {E : Fn → Fn}
    {K0 KN KT : ℝ} (hK0 : 0 < K0) (hKN : 0 < KN) (hKT : 0 < KT)
    (h0 : ∀ {W₁ W₂ : Fn}, Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0|
        ≤ K0 * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))
    (hN : ∀ {W₁ W₂ : Fn}, Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) 0|
        ≤ KN * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))
    (hT : ∀ {W₁ W₂ : Fn}, Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
        - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0|
        ≤ KT * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁)
          (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ)) W₁
        - Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂)
          (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ)) W₂|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) ∧
      |Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁)
          (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ))
        - Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂)
          (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ))|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  have hα0 : 0 < α := hα.1
  have hfac : (0 : ℝ) < 1 / (2 * α) := by positivity
  refine ⟨max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1, by
    have h1 : 0 ≤ max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) := by
      refine le_max_of_le_left ?_
      exact mul_nonneg hfac.le (by linarith)
    linarith, ?_⟩
  intro W₁ W₂ h₁ h₂
  have hb0 := h0 h₁ h₂
  have hbN := hN h₁ h₂
  have hbT := hT h₁ h₂
  set T : ℝ := (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
      * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) with hTdef
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    refine mul_nonneg (by linarith [Work.Spaces.HkNorm_nonneg α 5 W₁,
      Work.Spaces.HkNorm_nonneg α 5 W₂]) ?_
    exact Work.Spaces.HkNorm_nonneg α 5 _
  have hb0' : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
      - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0|
      ≤ K0 * T := by
    have h : K0 * T = K0 * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by rw [hTdef]; ring
    rw [h]; exact hb0
  have hbN' : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) 0
      - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
        (fun z θ => Φs z θ + E W₂ z θ)) 0| ≤ KN * T := by
    have h : KN * T = KN * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by rw [hTdef]; ring
    rw [h]; exact hbN
  have hbT' : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
      - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0|
      ≤ KT * T := by
    have h : KT * T = KT * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by rw [hTdef]; ring
    rw [h]; exact hbT
  have hbarid : Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁)
        (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ))
      - Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂)
        (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ))
      = (Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
        + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ)) 0
          - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ)) 0) := by
    simp only [Work.Construction.mubar]
    ring
  have hmuid : Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁)
        (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) W₁
      - Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂)
        (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) W₂
      = (1 / (2 * α))
        * ((Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
            - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
          + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ)) 0
            - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ)) 0)
          + (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
            - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0)) := by
    simp only [Work.Construction.mufunS]
    ring
  have hsum0 : |(Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
      + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) 0)
      + (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
        - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0)|
      ≤ (K0 + KN + KT) * T := by
    have h1 := abs_add_le
      ((Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
        + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) 0
          - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ)) 0))
      (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
        - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0)
    have h2 := abs_add_le
      (Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
      (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) 0)
    linarith
  have hsumN : |(Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
      + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) 0)| ≤ (K0 + KN) * T := by
    have h2 := abs_add_le
      (Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
      (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) 0)
    linarith
  have hKmu : (1 / (2 * α)) * ((K0 + KN + KT) * T)
      ≤ (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1) * T := by
    have h1 : (1 / (2 * α)) * (K0 + KN + KT)
        ≤ max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1 := by
      linarith [le_max_left ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN)]
    calc (1 / (2 * α)) * ((K0 + KN + KT) * T)
        = ((1 / (2 * α)) * (K0 + KN + KT)) * T := by ring
      _ ≤ (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1) * T :=
          mul_le_mul_of_nonneg_right h1 hT0
  have hKbar : (K0 + KN) * T
      ≤ (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1) * T := by
    have h1 : K0 + KN ≤ max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1 := by
      linarith [le_max_right ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN)]
    exact mul_le_mul_of_nonneg_right h1 hT0
  constructor
  · rw [hmuid, abs_mul, abs_of_pos hfac]
    calc (1 / (2 * α)) * |(Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
        + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ)) 0
          - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ)) 0)
        + (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₁ z θ / (1 + z)) 0
          - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth W₂ z θ / (1 + z)) 0)|
        ≤ (1 / (2 * α)) * ((K0 + KN + KT) * T) := mul_le_mul_of_nonneg_left hsum0 hfac.le
      _ ≤ (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1) * T := hKmu
      _ = (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1)
            * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
          rw [hTdef]; ring
  · rw [hbarid]
    calc |(Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0)
        + (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ)) 0
          - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ)) 0)|
        ≤ (K0 + KN) * T := hsumN
      _ ≤ (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1) * T := hKbar
      _ = (max ((1 / (2 * α)) * (K0 + KN + KT)) (K0 + KN) + 1)
            * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
          rw [hTdef]; ring

end Work.FTS.StrongEps.EpsRLX.ModDiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.DthUC2mProfileData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

open scoped Real Topology

/-! ## Data for the angular profile `θ ↦ D_θ c2m θ`

The angular coefficient of the transport term is `c2m θ = cos(2θ) - sin²θ`, and the profile
that enters the level-five atoms is `θ ↦ dthU c2m θ = sin(2θ)·(c2m)'θ`.  This file records the
two facts the surrounding H5 machinery needs about it:

* it is `C^∞` on the open quadrant (as a function of `(z,θ)` independent of `z`);
* it and its first four angular jets are bounded by a constant times `sin(2θ)` on `[0,π/2]`.

The smoothness is inherited from `θ ↦ c2m θ` through the operator `D_θ = sin(2θ)∂_θ`, and the
bounds are the ones already established for the iterates of `dthU` on `c2m`
(`Work.FTS.StrongPersist.dthU_c2m_bound6`, which gives `|D_θ^j c2m| ≤ C sin(2θ)²` for
`1 ≤ j ≤ 6`); since `dthU^[i] (dthU c2m) = dthU^[i+1] c2m` and `sin(2θ)² ≤ sin(2θ)` on
`Iθ = [0,π/2]`, the required `sin(2θ)`-bounds follow. -/

/-- `(z,θ) ↦ dthU c2m θ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_dthU_c2m :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Spaces.dthU Work.Construction.c2m θ) := by
  have hc2m : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) := by
    have hsnd : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => p.2) := contDiff_snd
    have hcos : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.cos (2 * p.2)) :=
      Real.contDiff_cos.comp (contDiff_const.mul hsnd)
    have hsin2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) :=
      (Real.contDiff_sin.comp hsnd).pow 2
    have h1 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2) :=
      hcos.sub hsin2
    have h2 : ContDiff ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2) := h1.of_le le_top
    exact h2.contDiffOn.mono (Set.subset_univ _)
  -- `D_θ` of the `z`-independent function `c2m` is exactly `dthU c2m`
  exact hc2m.Dth

theorem DthUC2mProfileData : ∃ C : ℝ, 0 < C ∧
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Spaces.dthU Work.Construction.c2m θ) ∧
    (∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU Work.Construction.c2m θ| ≤ C) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Spaces.dthU Work.Construction.c2m θ') 0 θ|
        ≤ C * Real.sin (2 * θ)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.dthU_c2m_bound6
  refine ⟨C, hCpos, smoothOpen_dthU_c2m, ?_, ?_⟩
  · intro θ hθ
    have h := hC 1 le_rfl (by norm_num) θ
    rw [Function.iterate_one] at h
    have hs1 : Real.sin (2 * θ) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_le_one (2 * θ)]
    calc |Work.Spaces.dthU Work.Construction.c2m θ| ≤ C * Real.sin (2 * θ) ^ 2 := h
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hs1 (le_of_lt hCpos)
      _ = C := by ring
  · intro i hi1 hi4 θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
        by linarith [hθ.2, Real.pi_pos]⟩
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsq : Real.sin (2 * θ) ^ 2 ≤ Real.sin (2 * θ) := by nlinarith
    have hstep : Work.Spaces.dthU^[i + 1] Work.Construction.c2m θ
        = Work.Spaces.dthU^[i] (Work.Spaces.dthU Work.Construction.c2m) θ := by
      rw [Function.iterate_succ_apply]
    have h := hC (i + 1) (by omega) (by omega) θ
    rw [hstep] at h
    rw [Work.FTS.LocData.DthIter_rad_eq i (Work.Spaces.dthU Work.Construction.c2m) 0 θ]
    calc |Work.Spaces.dthU^[i] (Work.Spaces.dthU Work.Construction.c2m) θ|
        ≤ C * Real.sin (2 * θ) ^ 2 := h
      _ ≤ C * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsq (le_of_lt hCpos)

end Work.FTS.StrongEps.H5.Atoms
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.HkMem5N0fix =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

/-- `N0fix α` is literally the collapsed `I₁ + I₂` combination of `FstarI12H6`, i.e. the
function `(3/(2α)) sin(2θ) L₁₂(F_*) ∂_θF_* - c₂m(θ) L₁₂(F_*) D_zF_*` of tex 1398--1402.  This is
just the definition of `N0fix = N₀₁ + N₀₂` (`Work.Construction.N01`, `Work.Construction.N02`),
written in the association used by `Work.FTS.StrongPersist.H6Rows.FstarI12H6`. -/
theorem N0fix_eq_I12 (α : ℝ) : Work.FTS.Nonlin.N0fix α = fun z θ =>
    (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ := by
  funext z θ
  simp only [Work.FTS.Nonlin.N0fix, Work.Construction.N01, Work.Construction.N02]
  ring

/-- **`N0fix = N₀₁ + N₀₂` is `ℋ⁵`-honest (with a finite level-five norm).**  On the open quadrant
`N0fix α` collapses to the separated datum `8 α² c₂(θ) z² Γ(α,θ) / (c(α)(1+z)⁴)`
(`Work.Construction.N0_first_two_eq'`), which is `C^∞` on the quadrant
(`Work.FTS.StrongPersist.L3Rhs.smoothOpen_N0fix`).

Route.  Write the datum as `a(θ)·r(z)` with `a(θ) = 8α²·c₂(θ)·Γ(α,θ)/c(α)` (angular) and
`r(z) = z²/(1+z)⁴` (radial) and combine the pointwise separation at order five
(`Work.FTS.StrongEps.H5.AngRad5.HkIntegrand_ang_rad_le5`, with the angular data of `c₂` and `Γ`:
`|c₂| ≤ 2` and `|DthIter i c₂| ≤ 1000·sin 2θ` for `i ≤ 4` from
`Work.FTS.Nonlinear.Pieces.DthIter_c2m_le`, and the corresponding bounds for `Γ` / `c₂·Γ` from
`Work.FTS.Spaces.Gamma_WlInf` or the `fstarDat`-style estimates) with
`Work.FTS.LocData.HkMem_of_majorant`.  The radial factor is explicit: `DzdIter i r` is a rational
function and `(DzdIter i r z)² w(z)²` is bounded by a constant times `(1+z)^{-2}` on `(0,∞)` for
`i ≤ 5` (the elementary identity `(z²/(1+z)⁴)² w = 1/(1+z)⁴` and its analogues), so the radial
integrals and their `z`-integrability are elementary; the angular `θ`-factor is integrable by
`Work.FTS.StrongEps.H5.AngFac5.ang_fac5_integrable_bound`.  Finally transport the majorant back
to `N0fix α` with `Work.FTS.EllipticEst.HkIntegrand_congr` /
`Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0` (pointwise equality on the open quadrant).
`a` may depend on `α` (and may simply be `HkNorm α 5 (N0fix α) + 1`, since it only has to dominate
the norm).

The proof carried out here takes the shorter route through the *level-six* analysis of the same
`I₁ + I₂` combination: `Work.FTS.StrongPersist.H6Rows.FstarI12H6` already establishes the
level-`6` membership of that combination together with the bound `|·|_{ℋ⁶} ≤ K α²` (`K`
independent of `α ≤ 1`).  Since `N0fix α` is exactly that combination (`N0fix_eq_I12`) and is
`C^∞` on the quadrant (`Work.FTS.StrongPersist.L3Rhs.smoothOpen_N0fix`), the level-five statement
follows from monotonicity of `HkMem` (`Work.FTS.OpenPkg.HkMem_mono_open`) and of `HkSq`
(`Work.FTS.CoercivityStep.Norm.HkSq_mono_le`), and `a := max (K α²) 0 + 1` dominates the norm. -/
theorem HkMem5N0fix : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
    Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N0fix α) ∧
    Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N0fix α) ≤ a := by
  intro α hαI
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  obtain ⟨K, hK, hF⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
  obtain ⟨hmem6, hbd6⟩ := hF α hα hα1
  have hmem6' : Work.Spaces.HkMem α 6 (Work.FTS.Nonlin.N0fix α) := by
    rw [N0fix_eq_I12 α]; exact hmem6
  have hbd6' : Work.Spaces.HkNorm α 6 (Work.FTS.Nonlin.N0fix α) ≤ K * α ^ 2 := by
    rw [N0fix_eq_I12 α]; exact hbd6
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.StrongPersist.L3Rhs.smoothOpen_N0fix α hα hα1
  have hmem5 : Work.Spaces.HkMem α 5 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 5 (by norm_num) hmem6'
  have hsq : Work.Spaces.HkSq α 5 (Work.FTS.Nonlin.N0fix α)
      ≤ Work.Spaces.HkSq α 6 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem6'
  have hn5 : Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N0fix α) ≤ K * α ^ 2 := by
    calc Work.Spaces.HkNorm α 5 (Work.FTS.Nonlin.N0fix α)
        = Real.sqrt (Work.Spaces.HkSq α 5 (Work.FTS.Nonlin.N0fix α)) := rfl
      _ ≤ Real.sqrt (Work.Spaces.HkSq α 6 (Work.FTS.Nonlin.N0fix α)) := Real.sqrt_le_sqrt hsq
      _ = Work.Spaces.HkNorm α 6 (Work.FTS.Nonlin.N0fix α) := rfl
      _ ≤ K * α ^ 2 := hbd6'
  refine ⟨max (K * α ^ 2) 0 + 1, by positivity, hmem5, ?_⟩
  linarith [hn5, le_max_left (K * α ^ 2) 0]

end Work.FTS.StrongEps.H5.Atoms
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.L5L12W =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary sign facts for the radial iterates `D_z^i` -/

/-- `deriv` of a negated function (unconditional; `deriv` is additive even where the function
is not differentiable, both sides being the junk value `0`). -/
private theorem deriv_neg_fun (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => -f y) x = -deriv f x := by
  rw [show (fun y => -f y) = fun y => (-1 : ℝ) * f y from by funext y; ring,
    deriv_const_mul_field]
  ring

/-- The iterated `z∂_z`-operator is odd. -/
private theorem DzdIter_neg_fun (f : ℝ → ℝ) (i : ℕ) :
    Work.Elliptic.DzdIter i (fun y => -f y) = fun z => -Work.Elliptic.DzdIter i f z := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.DzdIter_succ, ih]
      funext z
      show z * deriv (fun y => -Work.Elliptic.DzdIter n f y) z
        = -(z * deriv (Work.Elliptic.DzdIter n f) z)
      rw [deriv_neg_fun]
      ring

/-- The applied form of `DzdIter_neg_fun`, for the angular moment `Qang g 0`. -/
private theorem DzdIter_neg_Qang (g : ℝ → ℝ → ℝ) (i : ℕ) (z : ℝ) :
    Work.Elliptic.DzdIter i (fun y => -Work.Elliptic.Qang g 0 y) z
      = -Work.Elliptic.DzdIter i (fun y => Work.Elliptic.Qang g 0 y) z :=
  congrFun (DzdIter_neg_fun (fun y => Work.Elliptic.Qang g 0 y) i) z

/-! ## The `ℋ⁴`-membership of a radial lift -/

/-- **A radial lift is `ℋ⁴`-honest from its radial slot data.**  If every radial slot
`(D_z^i u)²w²`, `i ≤ 4`, is integrable on `Iz` with integral at most `M`, then the lift
`(z,θ) ↦ u z` lies in `ℋ⁴` and `HkSq α 4 (z,θ ↦ u z) ≤ 5 M ·∫_θ sin(2θ)^{-η}`.

The lift has no angular derivatives, so `HkIntegrand` reduces to the `D_z`-sum times
`sin(2θ)^{-η}` (`HkIntegrand_rad'`), and the two membership clauses are the two iterated
integrations of that identity. -/
private theorem radialLift_mem4 {α : ℝ} {u : ℝ → ℝ} {M : ℝ}
    (hInt : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    (hBnd : ∀ i : ℕ, i ≤ 4 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ M) :
    Work.Spaces.HkMem α 4 (fun z _ => u z) ∧
      Work.Spaces.HkSq α 4 (fun z _ => u z) ≤ 5 * M
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hsum_int : ∀ i ∈ Finset.range 5, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ 5 * M := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 5) hsum_int]
    calc ∑ i ∈ Finset.range 5, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range 5, M :=
          Finset.sum_le_sum fun i hi => hBnd i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 5 * M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta Work.Spaces.eta_pos
      Work.Spaces.eta_lt_one).1
  have hCthnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
    setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  have hinner : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => u z) z θ)
      = (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    intro z
    rw [setIntegral_congr_fun (s := Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => u z) z θ)
      (g := fun θ => (∑ i ∈ Finset.range 5,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ)]
    rw [MeasureTheory.integral_const_mul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z _
    refine MeasureTheory.Integrable.congr (f := fun θ : ℝ =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (hsinI.const_mul _) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ).symm)
  · refine MeasureTheory.Integrable.congr (f := fun z : ℝ =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        ((MeasureTheory.integrable_finsetSum (Finset.range 5) hsum_int).mul_const _) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
    exact (hinner z).symm
  · rw [Work.Elliptic.HkSq_rad]
    exact mul_le_mul_of_nonneg_right hsum_le hCthnn

/-- **The `L5` data of the radial atom `z ↦ L₁₂(w)(z)`.**  For a `ClassC` datum `w` with
`Xn α w ≤ C₀ α²` and `HkNorm α 6 w ≤ B` there is `a > 0` with
`L5 α (fun z θ => L₁₂(w)(z)) a`, i.e. `HQo α 4` of `L₁₂(w)`, of its `D_z`-derivative and of its
`D_θ`-derivative, plus the corresponding `Xn`-bounds.

Route.  `ClassC α w` gives `SmoothOpen w`, `HkMem α 7 w` and `L₁₂(w)(0) = 0`.
* `HQo α 4 (fun z θ => L₁₂ w z)`: `Work.FTS.OpenPkg.l12H_field` (with `SmoothOpen` from
  `ClassCRHS.smoothOpen_L12_radial_classC`) gives `HkMem α 4` and `Xn α (L₁₂ w) ≤ C₁ · Xn α w`.
* `Dth (fun z θ => L₁₂ w z) = 0` pointwise (a radial function has `pth = 0`), so its `HQo α 4`
  and its `Xn`-bound are trivial.
* `HQo α 4 (Dz (fun z θ => L₁₂ w z))`: on the open quadrant `Dz (fun z θ => L₁₂ w z) = -Qang w 0`
  (`Work.FTS.OpenPkg.l12_open_bundle`, the recursion `D_z^{k+1} L₁₂ = -Qang g k` at `k = 0`,
  valid for `z > 0`), so it suffices to show `HkMem α 4 (fun z θ => - Qang w 0 z)` and
  `Xn α (fun z θ => - Qang w 0 z) ≤ C · Xn α w`.  The radial lift of `r` has
  `HkSq α 4 (fun z θ => r z) = (∫_z Σ_{i≤4} (DzdIter i r z)² w(z)²) · (∫_θ sin(2θ)^{-η})`
  (`Work.Elliptic.HkSq_rad`, `Work.FTS.Nonlinear.RadialProd.HkSq_rad_eq`), and the iterated
  `z∂_z`-derivatives of `Qang w 0` are the higher angular moments (`DzdIter i (Qang w 0) =
  Qang w i` for `i ≤ 4`, from `Work.FTS.StrongPersist.QangAe6` /
  `Work.FTS.OpenPkg.QangOpen.QangDiff_open`), each satisfying
  `∫_z (Qang w i z)² w(z)² ≤ (∫_θ Kθ²) · HkSq α 4 w`
  (`Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open`, `i ≤ 4`).  Conclude the membership
  with `Work.FTS.LocData.HkMem_of_majorant` and transport the a.e. identity with
  `Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0`.  `SmoothOpen (Dz (fun z θ => L₁₂ w z))` is
  automatic (`SmoothOpen.Dz` of the smooth radial lift). -/
theorem L5L12W : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.FTS.StrongEps.H5.L5 α (fun z θ => Work.Construction.L12 w z) a := by
  intro α hαI C₀ B
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  obtain ⟨C1, hC1pos, hL12bd⟩ := Work.FTS.OpenPkg.l12H_field
  -- ## the universal constants
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cth : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCthdef
  set Cq : ℝ := Real.sqrt (5 * AK * Cth) with hCqdef
  have hCqnn : 0 ≤ Cq := Real.sqrt_nonneg _
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hCthnn : 0 ≤ Cth := by
    rw [hCthdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  have h5 : 0 ≤ 5 * AK * Cth := mul_nonneg (mul_nonneg (by norm_num) hAKnn) hCthnn
  refine ⟨max 1 (max (C1 * (C₀ * α ^ 2)) (Cq * (C₀ * α ^ 2))),
    lt_of_lt_of_le one_pos (le_max_left 1 _), ?_⟩
  intro w hw hsmall _hB
  -- ## the `ClassC` data of the datum
  have hmem4w : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hL12 := hL12bd α hα hα1 w ⟨hw.reg, hmem4w⟩ hw.l12
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  -- ## `D_z L₁₂(w) = -Qang w 0` on the open quadrant
  have hbundle := Work.FTS.OpenPkg.l12_open_bundle α w hα hα1 hw.reg hmem4w hw.l12
  have hDzEq : ∀ z θ : ℝ, Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z) z θ
      = Work.Elliptic.DzdIter 1 (fun z => Work.Elliptic.L12 w z) z := by
    intro z θ
    show z * deriv (fun z' => Work.Construction.L12 w z') z
        = z * deriv (fun z' => Work.Elliptic.L12 w z') z
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 w]
  have hQang_eq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z) z θ
        = -Work.Elliptic.Qang w 0 z := by
    intro z θ hz _ _
    rw [hDzEq z θ]
    simpa using hbundle.1 0 (by norm_num) z hz
  -- ## the `Qang w i` slots and their a.e. identification with the iterates of `-Qang w 0`
  have hAe : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i (fun y => -Work.Elliptic.Qang w 0 y) z
        = -Work.Elliptic.Qang w i z := by
    filter_upwards [Work.FTS.OpenPkg.QangOpen.DzdIter_Qang_ae_open hw.reg hmem4w,
      MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with z hz hne hzI
    intro i hi
    rw [DzdIter_neg_Qang w i z, hz (lt_of_le_of_ne hzI (Ne.symm hne)) i hi]
  have htransfer : ∀ i : ℕ, i ≤ 4 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang w i z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i (fun y => -Work.Elliptic.Qang w 0 y) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by
    intro i hi
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hAe] with z hz hzI
    rw [hz hzI i (Finset.mem_range.mpr (by omega : i < 5))]
    ring
  have hInt : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i (fun y => -Work.Elliptic.Qang w 0 y) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hα hα1 hw.reg hmem4w
      (i := i) hi).1.congr (htransfer i hi)
  have hBnd : ∀ i : ℕ, i ≤ 4 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i (fun y => -Work.Elliptic.Qang w 0 y) z) ^ 2
        * (Work.Spaces.w z) ^ 2) ≤ AK * Work.Spaces.HkSq α 4 w := by
    intro i hi
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htransfer i hi)]
    exact (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hα hα1 hw.reg hmem4w
      (i := i) hi).2
  -- ## the radial lift of `-Qang w 0` is `ℋ⁴`
  have hrad := radialLift_mem4 (α := α) (u := fun y => -Work.Elliptic.Qang w 0 y)
    (M := AK * Work.Spaces.HkSq α 4 w) hInt hBnd
  rw [← hCthdef] at hrad
  have hmemQ : Work.Spaces.HkMem α 4 (fun y (_ : ℝ) => -Work.Elliptic.Qang w 0 y) := hrad.1
  have hXnQ : Real.sqrt (Work.Spaces.HkSq α 4 (fun y (_ : ℝ) => -Work.Elliptic.Qang w 0 y))
      ≤ Cq * Work.FTS.Nonlin.Xn α w := by
    calc Real.sqrt (Work.Spaces.HkSq α 4 (fun y (_ : ℝ) => -Work.Elliptic.Qang w 0 y))
        ≤ Real.sqrt (5 * (AK * Work.Spaces.HkSq α 4 w) * Cth) := Real.sqrt_le_sqrt hrad.2
      _ = Real.sqrt ((5 * AK * Cth) * Work.Spaces.HkSq α 4 w) := by congr 1; ring
      _ = Real.sqrt (5 * AK * Cth) * Real.sqrt (Work.Spaces.HkSq α 4 w) := Real.sqrt_mul h5 _
      _ = Cq * Work.FTS.Nonlin.Xn α w := by
          rw [hCqdef]
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
  -- ## transport to `Dz (L₁₂ w)`
  have hsqDz : Work.Spaces.HkSq α 4 (Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z))
      = Work.Spaces.HkSq α 4 (fun y (_ : ℝ) => -Work.Elliptic.Qang w 0 y) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4
      (fun z θ hz hθ hθ' => hQang_eq z θ hz hθ hθ')
  have hmemDz : Work.Spaces.HkMem α 4
      (Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hmemQ
      (fun z hz θ hθ => by
        show -Work.Elliptic.Qang w 0 z
          = Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z) z θ
        rw [hQang_eq z θ hz hθ.1 hθ.2])
  have hXnDz : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z))
      ≤ Cq * (C₀ * α ^ 2) := by
    have h1 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z))
        ≤ Cq * Work.FTS.Nonlin.Xn α w := by
      have h := hXnQ
      rwa [← hsqDz] at h
    exact le_trans h1 (mul_le_mul_of_nonneg_left hsmall hCqnn)
  -- ## `D_θ` of a radial lift vanishes
  have hDth_eq : Work.Spaces.Dth (fun z θ => Work.Construction.L12 w z)
      = fun _ _ => (0 : ℝ) := by
    funext z θ
    simp [Work.Spaces.Dth, Work.Spaces.pth]
  -- ## assembly
  refine ⟨⟨hsm, hL12.1⟩, ?_, ⟨hsm.Dz, hmemDz⟩, ?_, ⟨hsm.Dth, ?_⟩, ?_⟩
  · calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z)
        ≤ C1 * Work.FTS.Nonlin.Xn α w := hL12.2
      _ ≤ C1 * (C₀ * α ^ 2) := mul_le_mul_of_nonneg_left hsmall hC1pos.le
      _ ≤ max 1 (max (C1 * (C₀ * α ^ 2)) (Cq * (C₀ * α ^ 2))) :=
          le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans hXnDz (le_trans (le_max_right _ _) (le_max_right _ _))
  · rw [hDth_eq]
    exact Work.FTS.EllipticEst.HkMem_zero α 4
  · rw [hDth_eq]
    simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Work.FTS.Galerkin.HkSq_zero_fun,
      Real.sqrt_zero]
    exact le_trans zero_le_one (le_max_left 1 _)

end Work.FTS.StrongEps.H5.Atoms
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.DataW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.Spaces
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The level-`5` product of a `𝒲^{4,∞}`-priced factor with an `ℋ⁴`-honest factor**, from the
level-four `𝒲^{4,∞}`-priced product rule and the level shift. -/
theorem W5_mul {α Cw : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCw : 0 < Cw)
    (hfield : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g)
    {F G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : W5 α F a) (hG : L5 α G b) :
    Work.Spaces.HkMem α 5 (fun z θ => c * (F z θ * G z θ)) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => c * (F z θ * G z θ))
        ≤ |c| * (3 * (Cw * α ^ (-(1 / 2 : ℝ)) * a * b)) := by
  have hAr : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  set P : ℝ := Cw * α ^ (-(1 / 2 : ℝ)) * a * b with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact mul_nonneg (mul_nonneg hAr ha) hb
  -- ### the five level-four product estimates
  have hFG := hfield F G hF.sm hF.wm hG.qo
  have hDzFG := hfield (Dz F) G hF.smDz hF.wmDz hG.qo
  have hFDzG := hfield F (Dz G) hF.sm hF.wm hG.qoDz
  have hDthFG := hfield (Dth F) G hF.smDth hF.wmDth hG.qo
  have hFDthG := hfield F (Dth G) hF.sm hF.wm hG.qoDth
  have hsqFG : Work.Spaces.HkSq α 4 (fun z θ => F z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => F z θ * G z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hFG.2 (Pd_le hAr ha hb hF.wb hG.bd
        (Work.Spaces.WlInf_nonneg α 4 F hF.wm) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqDz : Work.Spaces.HkSq α 4 (fun z θ => Dz F z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Dz F z θ * G z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hDzFG.2 (Pd_le hAr ha hb hF.wbDz hG.bd
        (Work.Spaces.WlInf_nonneg α 4 (Dz F) hF.wmDz) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqFDz : Work.Spaces.HkSq α 4 (fun z θ => F z θ * Dz G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => F z θ * Dz G z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hFDzG.2 (Pd_le hAr ha hb hF.wb hG.bdDz
        (Work.Spaces.WlInf_nonneg α 4 F hF.wm) (Work.Spaces.HkNorm_nonneg α 4 (Dz G)))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqDth : Work.Spaces.HkSq α 4 (fun z θ => Dth F z θ * G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => Dth F z θ * G z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hDthFG.2 (Pd_le hAr ha hb hF.wbDth hG.bd
        (Work.Spaces.WlInf_nonneg α 4 (Dth F) hF.wmDth) (Work.Spaces.HkNorm_nonneg α 4 G))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  have hsqFDth : Work.Spaces.HkSq α 4 (fun z θ => F z θ * Dth G z θ) ≤ P ^ 2 := by
    have hXn : Work.FTS.Nonlin.Xn α (fun z θ => F z θ * Dth G z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
      le_trans hFDthG.2 (Pd_le hAr ha hb hF.wb hG.bdDth
        (Work.Spaces.WlInf_nonneg α 4 F hF.wm) (Work.Spaces.HkNorm_nonneg α 4 (Dth G)))
    rw [sq_eq_Xn_sq α, hPdef]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
  -- ### the level shift
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.sm hG.qo.1
  have hsmDzG : Work.FTS.EllipticEst.SmoothOpen (Dz G) := hG.qoDz.1
  have hsmDthG : Work.FTS.EllipticEst.SmoothOpen (Dth G) := hG.qoDth.1
  have hDzm : Work.Spaces.HkMem α 4 (Dz (fun z θ => F z θ * G z θ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 4
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.smDz hG.qo.1)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.sm hsmDzG)
        hDzFG.1 hFDzG.1)
      (fun z hz θ hθ => (Dz_mul_eqOn_Q0 hF.sm hG.qo.1 z θ hz hθ.1 hθ.2).symm)
  have hDthm : Work.Spaces.HkMem α 4 (Dth (fun z θ => F z θ * G z θ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (Work.FTS.EllipticEst.RPFresh.HkMem_add_open α 4
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.smDth hG.qo.1)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.sm hsmDthG)
        hDthFG.1 hFDthG.1)
      (fun z hz θ hθ => (Dth_mul_eqOn_Q0 hF.sm hG.qo.1 z θ hz hθ.1 hθ.2).symm)
  have hsq5 : Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ) ≤ 9 * P ^ 2 := by
    have hshift := HkSq_succ_le (α := α) (k := 4) hα hsm (by norm_num) hFG.1 hDzm hDthm
    have hDzsq : Work.Spaces.HkSq α 4 (Dz (fun z θ => F z θ * G z θ))
        ≤ 2 * (Work.Spaces.HkSq α 4 (fun z θ => Dz F z θ * G z θ)
            + Work.Spaces.HkSq α 4 (fun z θ => F z θ * Dz G z θ)) := by
      have h1 := Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.smDz hG.qo.1)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.sm hsmDzG) hDzFG.1 hFDzG.1
      rwa [Work.FTS.EllipticEst.HkSq_congr_open α 4
        (fun z θ hz hθ hθ' => (Dz_mul_eqOn_Q0 hF.sm hG.qo.1 z θ hz hθ hθ').symm)] at h1
    have hDthsq : Work.Spaces.HkSq α 4 (Dth (fun z θ => F z θ * G z θ))
        ≤ 2 * (Work.Spaces.HkSq α 4 (fun z θ => Dth F z θ * G z θ)
            + Work.Spaces.HkSq α 4 (fun z θ => F z θ * Dth G z θ)) := by
      have h1 := Work.FTS.GalFields.RHS.HkSq_add_le_open α 4 hα
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.smDth hG.qo.1)
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hF.sm hsmDthG) hDthFG.1 hFDthG.1
      rwa [Work.FTS.EllipticEst.HkSq_congr_open α 4
        (fun z θ hz hθ hθ' => (Dth_mul_eqOn_Q0 hF.sm hG.qo.1 z θ hz hθ hθ').symm)] at h1
    linarith [hshift, hsqFG, hsqDz, hsqFDz, hsqDth, hsqFDth, hDzsq, hDthsq, hPnn]
  -- ### the membership and the norm
  have hmem5 : Work.Spaces.HkMem α 5 (fun z θ => F z θ * G z θ) :=
    HkMem_succ_of hα hsm (k := 4) (by norm_num) hFG.1 hDzm hDthm
  refine ⟨Work.FTS.LocData.HkMem_const_mul α 5 c hmem5, ?_⟩
  have hsqc : Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))
      = c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ) :=
    Work.FTS.StrongEps.HkSq_const_mul α 5 c (fun z θ => F z θ * G z θ)
  have hroot : Work.Spaces.HkNorm α 5 (fun z θ => c * (F z θ * G z θ))
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))) := rfl
  have hsqc' : Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))
      ≤ (|c| * (3 * P)) ^ 2 := by
    rw [hsqc]
    calc c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ)
        ≤ c ^ 2 * (9 * P ^ 2) := mul_le_mul_of_nonneg_left hsq5 (sq_nonneg c)
      _ = (|c| * (3 * P)) ^ 2 := by
          rw [← sq_abs c]
          ring
  calc Work.Spaces.HkNorm α 5 (fun z θ => c * (F z θ * G z θ))
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))) := hroot
    _ ≤ Real.sqrt ((|c| * (3 * P)) ^ 2) := Real.sqrt_le_sqrt hsqc'
    _ = |c| * (3 * P) := Real.sqrt_sq (by positivity)
    _ = |c| * (3 * (Cw * α ^ (-(1 / 2 : ℝ)) * a * b)) := by rw [hPdef]

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Nb5Pkgs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `HkNorm` of a scalar multiple of a level-`5` function. -/
theorem HkNorm_const_mul5 (α : ℝ) (c : ℝ) (X : Fn) :
    Work.Spaces.HkNorm α 5 (fun z θ => c * X z θ) = |c| * Work.Spaces.HkNorm α 5 X := by
  have hsq : Work.Spaces.HkSq α 5 (fun z θ => c * X z θ)
      = c ^ 2 * Work.Spaces.HkSq α 5 X := Work.FTS.StrongEps.HkSq_const_mul α 5 c X
  calc Work.Spaces.HkNorm α 5 (fun z θ => c * X z θ)
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * X z θ)) := rfl
    _ = Real.sqrt (c ^ 2 * Work.Spaces.HkSq α 5 X) := by rw [hsq]
    _ = Real.sqrt (c ^ 2) * Real.sqrt (Work.Spaces.HkSq α 5 X) :=
        Real.sqrt_mul (sq_nonneg c) _
    _ = |c| * Work.Spaces.HkNorm α 5 X := by
        rw [Real.sqrt_sq_eq_abs]
        rfl

/-- **The `ℋ⁵`-honest atoms** (the statement of `H5.Atoms.HAtoms5`). -/
def HAtoms5Pkg : Prop :=
  ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      (Work.FTS.VocabO.HQo α 5 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 w ∧ Work.Spaces.HkNorm α 5 w ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dth w) ∧
        Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (Work.Spaces.Dz w) ∧
        Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z _ => Work.Construction.FK w z) ∧
        Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK w z) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * w z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) ≤ a)

/-- **The three star coefficients as `𝒲^{5,∞}`-atoms** (the statement of
`H5.Atoms.WAtomsStar5`); the constant is independent of `Φs`. -/
def WStar5Pkg : Prop :=
  ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {Cs6 : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {Φs : Fn}, Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            / Work.Construction.s2 θ)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInfMem α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧
        Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
          * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ a)

/-- **The four fixed `𝒲^{5,∞}`-atoms** (the statement of `H5.Atoms.WAtomsFixed5`). -/
def WFixed5Pkg : Prop :=
  ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
    ∃ a : ℝ, 0 < a ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) ∧
        Work.Spaces.WlInfMem α 5 (Work.Construction.Fstar α) ∧
        Work.Spaces.WlInf α 5 (Work.Construction.Fstar α) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInfMem α 5 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInf α 5 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInfMem α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
        Work.Spaces.WlInf α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ a) ∧
      (Work.FTS.EllipticEst.SmoothOpen (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ∧
        Work.Spaces.WlInfMem α 5 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ∧
        Work.Spaces.WlInf α 5 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ≤ a)

/-- **The five fixed `ℋ⁵`-atoms** (`φ·F_*`, `φ·D_θF_*`, `φ·D_zF_*`, `FK(F_*)·D_θF_*`,
`FK(F_*)·F_*`), the statement of `H5.Atoms.FixedAtoms5` with its engine hypothesis discharged. -/
def HFixed5Pkg : Prop :=
  ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z)
          * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z)
          * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => z / (1 + z)
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z)
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ a) ∧
      (Work.FTS.VocabO.HQo α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Work.Construction.Fstar α z θ) ∧
        Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
          * Work.Construction.Fstar α z θ) ≤ a)

/-- The order-`5` angular slot bound for `-sin²θ` (the statement of `H5.Atoms.SinSqSlot5`). -/
def SinSqSlot5Pkg : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.DthIter 5 (fun _ (θ' : ℝ) => -(Real.sin θ') ^ 2) 0 θ| ≤ B * Real.sin (2 * θ)

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12_Jeps_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem L12_Jeps_sub_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : Work.FTS.Galerkin.Fn),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
        |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0
            - Work.Construction.L12 f 0| ≤ C * ε * Work.Spaces.HkNorm α 5 f := by
  -- the `ℋ⁴`-Lipschitz continuity of the zero mode, and the mollifier approximation estimate
  obtain ⟨C₁, hC₁pos, hLip⟩ := L12_lipschitz_field
  obtain ⟨C₂, hC₂pos, hApp⟩ :=
    Work.FTS.StrongEps.EpsApprox.HkNorm_Jeps_sub_le ρ hρ.moll
  refine ⟨C₁ * C₂, mul_pos hC₁pos hC₂pos, ?_⟩
  intro α hα f hf hmem5 ε hε
  have hαpos : 0 < α := hα.1
  -- smoothness of `f` in the two equivalent shapes
  have hfQ0 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf
  have hfQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad := by
    intro n
    simpa only [Quad, Work.FTS.EllipticEst.Q0] using hfQ0 n
  -- the three profiles and their certificates
  have hJso : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε f) :=
    smoothOpen_Jeps ρ hρ hε.1 hfQuad
  have hmem4f : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf 4 (by norm_num) hmem5
  have hmem5J : Work.Spaces.HkMem α 5 (Jeps ρ ε f) :=
    HkMem_Jeps hρ.moll hα hε.1 hfQuad hmem5
  have hmem4J : Work.Spaces.HkMem α 4 (Jeps ρ ε f) :=
    Work.FTS.OpenPkg.HkMem_mono_open hJso 4 (by norm_num) hmem5J
  have hsubso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Jeps ρ ε f z θ - f z θ) := by
    have hfun : Function.uncurry (fun z θ => Jeps ρ ε f z θ - f z θ)
        = Function.uncurry (Jeps ρ ε f) - Function.uncurry f := by
      funext p; rfl
    rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
    exact hJso.sub hf
  have hsubmem : Work.Spaces.HkMem α 4 (fun z θ => Jeps ρ ε f z θ - f z θ) :=
    Work.FTS.GalBasis.hkMem_sub_open α 4 hJso hf hmem4J hmem4f
  have hlip := hLip α hαpos (Jeps ρ ε f) f ⟨hJso, hmem4J⟩ ⟨hf, hmem4f⟩ ⟨hsubso, hsubmem⟩
  have happ := hApp α hα 4 ε hε f hfQ0 hmem5 hmem4J
  calc |Work.Construction.L12 (Jeps ρ ε f) 0 - Work.Construction.L12 f 0|
      ≤ C₁ * Work.Spaces.HkNorm α 4 (fun z θ => Jeps ρ ε f z θ - f z θ) := hlip
    _ ≤ C₁ * (C₂ * ε * Work.Spaces.HkNorm α 5 f) :=
        mul_le_mul_of_nonneg_left happ (le_of_lt hC₁pos)
    _ = (C₁ * C₂) * ε * Work.Spaces.HkNorm α 5 f := by ring

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.AssemblyStep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- `Dmass` is nonnegative (it is the integral of a nonnegative function). -/
theorem Dmass_nonneg (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) (γ : ℝ) :
    0 ≤ Dmass ρ γ :=
  integral_nonneg fun t => mul_nonneg (rhoTilde_nonneg ρ hρ.moll.nonneg t) (Real.exp_pos _).le

/-- `ofReal` is multiplicative on nonnegative triples (in the product shape used below). -/
theorem ofReal_mul3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c = ENNReal.ofReal (a * b * c) := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb)]

/-- **The one-order smoothing estimate of `J_ε` in the weighted `H^k`-norms** — the auxiliary
form of `Work.FTS.StrongEps.HkSq_Jeps_step_le`, with the same statement. -/
theorem step_le_aux (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ m : ℕ, 2 ≤ m → m ≤ 8 →
      ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 → ∀ u : ℝ → ℝ → ℝ,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad) →
        Work.Spaces.HkMem α (m - 1) u →
        Work.Spaces.HkMem α m (Work.FTS.StrongEps.Jeps ρ ε u) ∧
          Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u)
            ≤ C * (ε⁻¹) ^ 2 * Work.Spaces.HkSq α (m - 1) u := by
  obtain ⟨cη, hcη, hWη0⟩ := HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγ, hWγ0⟩ := HkSqAux.Wt_shift_le
  obtain ⟨δ, hδ, hJac0⟩ := HkSqAux.logJac_shift_le
  refine ⟨Bconst ρ * Dmass ρ (2 * max cη cγ + δ) + 1, ?_, ?_⟩
  · have h1 : 0 < Bconst ρ := Bconst_pos ρ
    have h2 : 0 ≤ Dmass ρ (2 * max cη cγ + δ) := Dmass_nonneg ρ hρ _
    have h3 : 0 ≤ Bconst ρ * Dmass ρ (2 * max cη cγ + δ) := mul_nonneg h1.le h2
    linarith
  intro α hα m hm hm8 ε hεI u hu hMem
  obtain ⟨hε, hε1⟩ := hεI
  have hcη' : 0 < max cη cγ := lt_of_lt_of_le hcη (le_max_left _ _)
  have hc : (0 : ℝ) ≤ max cη cγ := hcη'.le
  have hγ : (0 : ℝ) ≤ 2 * max cη cγ + δ := by linarith
  have hMemJ : Work.Spaces.HkMem α m (Work.FTS.StrongEps.Jeps ρ ε u) :=
    HkMem_Jeps_step ρ hρ hα hm hm8 hε hε1 hu hMem
  refine ⟨hMemJ, ?_⟩
  -- the two weight-shift comparisons with the common constant `max cη cγ`
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)) := by
    intro z θ hz hθ p
    refine (hWη0 z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact div_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) := by
    intro z θ hz hθ p
    exact (hWγ0 α hα z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)))
  -- the pointwise step, extended to the closed quadrant (the integrand vanishes on the boundary)
  have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
        ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ) * ∫⁻ p : ℝ × ℝ,
            ENNReal.ofReal (Psi ρ ε p)
              * ENNReal.ofReal (Real.exp (2 * max cη cγ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                  (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
    intro z hz θ hθ
    by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
    · exact step_pointwise ρ hρ hε hε1 hα hm hm8 hu hWη hWγ hq.1 hq.2
    · have hzero : Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ = 0 :=
        HkSqAux.HkIntegrand_boundary_zero hα hz hθ hq
      rw [hzero, ENNReal.ofReal_zero]
      exact zero_le
  have hAe : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (Psi ρ ε q.2)
        * ENNReal.ofReal (Real.exp (2 * max cη cγ * (|q.2.1| + |q.2.2|)))
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
            (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
            (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
    aemeasurable_Psi_shift (ρ := ρ) (ε := ε) (c := max cη cγ) (α := α) (k := m - 1) (u := u) hρ
      (HkSqAux.continuousOn_HkIntegrand_Quad α (m - 1) hu)
  -- the generic chain
  have hmain := HkSq_step_of_pointwise (ρ := ρ) (α := α) (c := max cη cγ) (δ := δ)
    (B := Bconst ρ) (ε := ε) (m := m) (by omega) (u := u) (Ψ := Psi ρ ε)
    hc hδ.le hMemJ hMem hu hAe hP (fun s ζ p₁ p₂ => hJac0 s ζ p₁ p₂)
  -- the moment bound for the density
  have hmom : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p
        * Real.exp ((2 * max cη cγ + δ) * (|p.1| + |p.2|))))
      ≤ ENNReal.ofReal (ε⁻¹ * Dmass ρ (2 * max cη cγ + δ)) := by
    have hint := Psi_moment_integrable ρ hρ hε hε1 hγ
    refine (le_of_eq (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun p =>
        mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)).symm).trans ?_
    exact ENNReal.ofReal_le_ofReal (Psi_mass ρ hρ hε hε1 hγ)
  -- the final assembly
  have h1 : 0 ≤ ε⁻¹ * Bconst ρ := mul_nonneg (by positivity) (Bconst_pos ρ).le
  have h2 : 0 ≤ ε⁻¹ * Dmass ρ (2 * max cη cγ + δ) := by
    exact mul_nonneg (by positivity) (Dmass_nonneg ρ hρ _)
  have hBD : 0 ≤ Bconst ρ * Dmass ρ (2 * max cη cγ + δ) :=
    mul_nonneg (Bconst_pos ρ).le (Dmass_nonneg ρ hρ _)
  have hH : 0 ≤ Work.Spaces.HkSq α (m - 1) u := Work.Spaces.HkSq_nonneg α (m - 1) u
  have hfinal : ENNReal.ofReal (Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u))
      ≤ ENNReal.ofReal ((Bconst ρ * Dmass ρ (2 * max cη cγ + δ) + 1) * (ε⁻¹) ^ 2
          * Work.Spaces.HkSq α (m - 1) u) := by
    refine hmain.trans ?_
    calc ENNReal.ofReal (ε⁻¹ * Bconst ρ)
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p
              * Real.exp ((2 * max cη cγ + δ) * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)
        ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ)
            * ENNReal.ofReal (ε⁻¹ * Dmass ρ (2 * max cη cγ + δ))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) :=
          mul_le_mul_left (mul_le_mul_right hmom (ENNReal.ofReal (ε⁻¹ * Bconst ρ))) _
      _ = ENNReal.ofReal ((ε⁻¹ * Bconst ρ) * (ε⁻¹ * Dmass ρ (2 * max cη cγ + δ))
            * Work.Spaces.HkSq α (m - 1) u) :=
          ofReal_mul3 h1 h2 hH
      _ ≤ ENNReal.ofReal ((Bconst ρ * Dmass ρ (2 * max cη cγ + δ) + 1) * (ε⁻¹) ^ 2
            * Work.Spaces.HkSq α (m - 1) u) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hsq : 0 ≤ (ε⁻¹) ^ 2 := sq_nonneg _
          calc (ε⁻¹ * Bconst ρ) * (ε⁻¹ * Dmass ρ (2 * max cη cγ + δ))
                * Work.Spaces.HkSq α (m - 1) u
              = (Bconst ρ * Dmass ρ (2 * max cη cγ + δ))
                  * ((ε⁻¹) ^ 2 * Work.Spaces.HkSq α (m - 1) u) := by ring
            _ ≤ (Bconst ρ * Dmass ρ (2 * max cη cγ + δ) + 1)
                  * ((ε⁻¹) ^ 2 * Work.Spaces.HkSq α (m - 1) u) :=
                mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hsq hH)
            _ = (Bconst ρ * Dmass ρ (2 * max cη cγ + δ) + 1) * (ε⁻¹) ^ 2
                  * Work.Spaces.HkSq α (m - 1) u := by ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfinal

end Work.FTS.StrongEps.StepFacts
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.smoothOpen_dynRHS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission/Work/FTS/StrongEps/smoothOpen_dynRHS.lean`

**Target.** `Work.FTS.StrongEps.smoothOpen_dynRHS`: the nonlinear right-hand side
`dynRHS α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ` of the fake-time equation is `C^n` on
the open quadrant `Quad` for every `n`, given the corresponding regularity of its *atoms*:

* `F = Ftau α (JfamP ρ ε g) τ` and `g̃ = slice (JfamP ρ ε g) τ` are `C^n` on the quadrant (`hF`,
  `hg`);
* the radial functions `z ↦ L₁₂(F)(z)`, `z ↦ L₁₂(g̃)(z)` and `z ↦ (F,K)(z) = FK F z` are `C^n`
  on `(0,∞)` (`hL12F`, `hL12g`, `hFK`);
* the three transported coefficients
  `ℛ(Φ̃)`, `𝒰(Φ̃)`, `𝒱(Φ̃)` at `Φ̃ = PhiTil α F (slice (PsiCan Φs E (JfamP ρ ε g)) τ)` are `C^n`
  on the quadrant (`hR`, `hU`, `hV`).

Note `dynRHS = Construction.gRHS` evaluated at the two modulation constants `muDyn`, `lamDyn`,
which are *numbers* (integrals of the nonlinear blocks at `z = 0`): smoothness of `gRHS` is
therefore insensitive to them, and the only other ingredient is the fixed smooth datum
`AK α = (Γ(θ)/c α)·2z²/(1+z)³`, whose angular factor `Γ` is smooth on the open quadrant
(`AK_smoothO`).  The hypotheses `hPhi` (regularity of `Φ` itself) and the smoothness of the
Fourier/profile data `Φs`, `E`, `ρ`, `ε` are not used: `Φ` enters `N` only through `PhiTil`, and
`JfamP` enters only through its slice.

The proof decomposes the right-hand side into the blocks `N₀` (`smoothOpen_N0_gen`), `N`
(`smoothOpen_N_gen`), `N_*` (`smoothOpen_Nstar_of`), the fixed `AK α` and the constant
`-μ̄·AK`, and assembles the four with the closure of `SmoothOpen` under finite sums, products and
constant multiples.
-/

namespace Work.FTS.StrongEps

open Work.FTS.EllipticEst (SmoothOpen)

set_option linter.unusedVariables false

/-! ## The quadratic block `N₀` -/

/-- `N₀ α F g` is `C^∞` on the open quadrant as soon as the profile `F`, the perturbation `g` and
the radial function `z ↦ L₁₂(g)(z)` are.  (The datum `F_*` and its moment `L₁₂(F_*)` are fixed
smooth functions, supplied by the library.) -/
theorem smoothOpen_N0_gen {α : ℝ} {F g : ℝ → ℝ → ℝ}
    (hF : SmoothOpen F) (hg : SmoothOpen g)
    (hLg : SmoothOpen (fun z _ => Work.Construction.L12 g z)) :
    SmoothOpen (Work.Construction.N0 α F g) := by
  have hFs : SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hLFs : SmoothOpen (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α
  have hs2 : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_s2
  have hc2m : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m
  have t1 : SmoothOpen (fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hs2) hLFs) hFs.pth
  have t2 : SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hc2m hLFs) hFs.Dz
  have t3 : SmoothOpen (fun z θ => (1 / α) * Work.Construction.L12 g z * g z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (1 / α) hLg) hg
  have t4 : SmoothOpen (fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 g z * Work.Spaces.pth F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hs2) hLg) hF.pth
  have t5 : SmoothOpen (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z
      * Work.Spaces.Dz F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hc2m hLg) hF.Dz
  have t6 : SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz g z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hc2m hLFs) hg.Dz
  have key : SmoothOpen (fun z θ =>
      (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        + (1 / α) * Work.Construction.L12 g z * g z θ
        + (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z
          * Work.Spaces.pth F z θ
        - Work.Construction.c2m θ * Work.Construction.L12 g z
          * Work.Spaces.Dz F z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz g z θ) :=
    ((((t1.sub t2).add t3).add t4).sub t5).sub t6
  refine ContDiffOn.congr
    (f₁ := Function.uncurry (fun z θ => Work.Construction.N0 α F g z θ)) key ?_
  intro p hp
  simp only [Function.uncurry, Work.Construction.N0]

/-! ## The elliptic-correction block `N` -/

/-- `N α F (Φ)` is `C^∞` on the open quadrant as soon as the profile `F`, the angular moment
`z ↦ FK F z` and the three transported coefficients `ℛ(Φ̃)`, `𝒰(Φ̃)`, `𝒱(Φ̃)` of the residual
`Φ̃ = PhiTil α F Φ` are. -/
theorem smoothOpen_N_gen {α : ℝ} {F Φ : ℝ → ℝ → ℝ}
    (hF : SmoothOpen F)
    (hFK : SmoothOpen (fun z _ => Work.Construction.FK F z))
    (hR : SmoothOpen (Work.Construction.Rop α (Work.Construction.PhiTil α F Φ)))
    (hU : SmoothOpen (Work.Construction.Uop α (Work.Construction.PhiTil α F Φ)))
    (hV : SmoothOpen (Work.Construction.Vop (Work.Construction.PhiTil α F Φ))) :
    SmoothOpen (Work.Construction.N α F Φ) := by
  have hs2 : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) :=
    Work.FTS.GalFields.RHS.smoothOpen_sin_two
  have hsin : SmoothOpen (fun _ (θ : ℝ) => Real.sin θ ^ 2) :=
    Work.FTS.GalFields.RHS.smoothOpen_sin_sq
  have t1 : SmoothOpen (fun z θ => 2 * Work.Construction.Rop α
      (Work.Construction.PhiTil α F Φ) z θ * F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul 2 hR) hF
  have t2 : SmoothOpen (fun z θ => 2 * Work.Construction.Uop α
      (Work.Construction.PhiTil α F Φ) z θ * Work.Spaces.pth F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul 2 hU) hF.pth
  have t3 : SmoothOpen (fun z θ => 2 * α * Work.Construction.Vop
      (Work.Construction.PhiTil α F Φ) z θ * Work.Spaces.Dz F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (2 * α) hV) hF.Dz
  have t4 : SmoothOpen (fun z θ => (1 / 2) * Work.Construction.s2 θ
      * Work.Construction.FK F z * Work.Spaces.pth F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (1 / 2) hs2) hFK) hF.pth
  have t5 : SmoothOpen (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hsin hFK) hF
  have key : SmoothOpen (fun z θ =>
      2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ * F z θ
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
          * Work.Spaces.pth F z θ
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ
          * Work.Spaces.Dz F z θ
        - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
          * Work.Spaces.pth F z θ
        - Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ) :=
    (((t1.sub t2).sub t3).sub t4).sub t5
  refine ContDiffOn.congr
    (f₁ := Function.uncurry (fun z θ => Work.Construction.N α F Φ z θ)) key ?_
  intro p hp
  simp only [Function.uncurry, Work.Construction.N]

/-! ## The full right-hand side -/

/-- `gRHS α μ lam F Φ g` is `C^∞` on the open quadrant under the regularity of the atoms.  This
is the general form of the smoothness of `dynRHS`; the modulation constants `μ`, `lam` are free
(numbers). -/
theorem smoothOpen_gRHS_gen {α μ lam : ℝ} {F Φ gg : ℝ → ℝ → ℝ}
    (hF : SmoothOpen F) (hg : SmoothOpen gg)
    (hLg : SmoothOpen (fun z _ => Work.Construction.L12 gg z))
    (hFK : SmoothOpen (fun z _ => Work.Construction.FK F z))
    (hR : SmoothOpen (Work.Construction.Rop α (Work.Construction.PhiTil α F Φ)))
    (hU : SmoothOpen (Work.Construction.Uop α (Work.Construction.PhiTil α F Φ)))
    (hV : SmoothOpen (Work.Construction.Vop (Work.Construction.PhiTil α F Φ))) :
    SmoothOpen (Work.Construction.gRHS α μ lam F Φ gg) := by
  have hAK : SmoothOpen (Work.Construction.AK α) := Work.FTS.StrongPersist.AK_smoothO α
  have hN0 : SmoothOpen (Work.Construction.N0 α F gg) := smoothOpen_N0_gen hF hg hLg
  have hN : SmoothOpen (Work.Construction.N α F Φ) := smoothOpen_N_gen hF hFK hR hU hV
  have hNs : SmoothOpen (Work.Construction.Nstar μ lam gg) :=
    Work.FTS.GalFields.RHS.smoothOpen_Nstar_of hg
  have h1 : SmoothOpen (fun z θ => -Work.Construction.mubar (Work.Construction.N0 α F gg)
      (Work.Construction.N α F Φ) * Work.Construction.AK α z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul
      (-Work.Construction.mubar (Work.Construction.N0 α F gg) (Work.Construction.N α F Φ)) hAK
  have key : SmoothOpen (fun z θ =>
      -Work.Construction.mubar (Work.Construction.N0 α F gg) (Work.Construction.N α F Φ)
          * Work.Construction.AK α z θ
        + Work.Construction.N0 α F gg z θ + Work.Construction.N α F Φ z θ
        + Work.Construction.Nstar μ lam gg z θ) :=
    ((h1.add hN0).add hN).add hNs
  refine ContDiffOn.congr
    (f₁ := Function.uncurry (fun z θ => Work.Construction.gRHS α μ lam F Φ gg z θ)) key ?_
  intro p hp
  simp only [Function.uncurry, Work.Construction.gRHS]

/-! ## The target -/


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.CorrAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm HkIntegrand Dz Dth mixed)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §1 `Corr` in separated form -/

theorem Corr_eq_sep (α : ℝ) (f : Fn) :
    Work.FTS.CoercivityFix.Corr α f
      = fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α f z := by
  funext z θ
  exact Work.FTS.CoercivityFix.Transfer.Corr_eq_radA α f z θ

/-- `Gam α = c(α)·gamCoef α` as functions (`c(α) ≠ 0` for `α ∈ (0,1]`). -/
theorem Gam_eq_c_mul_gamCoef {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.Gam α = fun θ => Work.Spaces.c α * Work.FTS.StrongPersist.gamCoef α θ := by
  have hc : Work.Spaces.c α ≠ 0 := ne_of_gt (Work.FTS.StrongPersist.L3Aux.c_pos hα hα1)
  funext θ
  rw [Work.FTS.StrongPersist.gamCoef_eq_inv_mul]
  simp only
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- The iterated `D_θ`-derivatives of `Gam α` are `c(α)` times those of `gamCoef α`. -/
theorem dthU_iter_Gam_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) :
    Work.Spaces.dthU^[i] (Work.Spaces.Gam α)
      = fun θ => Work.Spaces.c α
          * Work.Spaces.dthU^[i] (Work.FTS.StrongPersist.gamCoef α) θ := by
  rw [Gam_eq_c_mul_gamCoef hα hα1]
  exact Work.FTS.StrongPersist.dthU_iter_const_mul (Work.Spaces.c α)
    (Work.FTS.StrongPersist.gamCoef α) i

/-- **The angular factor of the separation bound** at `C = Gam α` is exactly `c(α)²·Mth6 α`. -/
theorem sepFactor_eq_Mth6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 7,
            (if 1 ≤ i then (Work.Spaces.dthU^[i] (Work.Spaces.Gam α) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
      = (Work.Spaces.c α) ^ 2 * Work.FTS.StrongPersist.Mth6 α θ := by
  have hGam : Work.Spaces.Gam α θ
      = Work.Spaces.c α * Work.FTS.StrongPersist.gamCoef α θ :=
    congrFun (Gam_eq_c_mul_gamCoef hα hα1) θ
  rw [Work.FTS.StrongPersist.Mth6, mul_add, Finset.mul_sum]
  congr 1
  · rw [hGam]; ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : 1 ≤ i
    · rw [if_pos h1, if_pos h1, congrFun (dthU_iter_Gam_eq hα hα1 i) θ]
      ring
    · rw [if_neg h1, if_neg h1, mul_zero]

/-! ## §2 The pointwise `ℋ⁶`-integrand bound -/

/-- **The pointwise bound at the heart of the proof.**  For `θ ∈ Iθ` the `ℋ⁶`-integrand of
`Corr α f` is dominated by the product of the angular mass `c(α)²·Mth6 α θ` and the radial slot
sum `SlotSum (radA α f) z` of the radial profile of `Corr`. -/
theorem HkIntegrand_Corr_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (f : Fn) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 6 (Work.FTS.CoercivityFix.Corr α f) z θ
      ≤ (Work.Spaces.c α) ^ 2 * Work.FTS.StrongPersist.Mth6 α θ
          * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z := by
  have h := Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 6)
    (C := Work.Spaces.Gam α) (B := Work.FTS.CoercivityFix.Transfer.radA α f)
    (z := z) (θ := θ) hθ
  rw [Corr_eq_sep α f]
  refine le_trans h (le_of_eq ?_)
  rw [sepFactor_eq_Mth6 hα hα1 θ, Work.FTS.StrongPersist.SlotSum]

/-! ## §3 The finite-order smoothness of `Corr` on the open quadrant -/

theorem contDiffOn_six_ampA {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 6 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) := by
  have hc : Work.Spaces.c α ≠ 0 := ne_of_gt (Work.FTS.StrongPersist.L3Aux.c_pos hα hα1)
  have hden : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have h1 : (1 : ℝ) + z ≠ 0 := by
      have : (0 : ℝ) < z := hz
      linarith
    exact mul_ne_zero hc (pow_ne_zero 2 h1)
  have hnum : ContDiffOn ℝ 6 (fun z : ℝ => 2 * z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_const.mul contDiffOn_id
  have hdenm : ContDiffOn ℝ 6 (fun z : ℝ => Work.Spaces.c α * (1 + z) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    contDiffOn_const.mul ((contDiffOn_const.add contDiffOn_id).pow 2)
  exact hnum.div hdenm hden

theorem contDiffOn_six_ampB_div (α : ℝ) :
    ContDiffOn ℝ 6 (fun z : ℝ =>
      Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α) (Set.Ioi (0 : ℝ)) := by
  have hden : ∀ z ∈ Set.Ioi (0 : ℝ), (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by
      have : (0 : ℝ) < z := hz
      linarith
    exact ne_of_gt (by positivity)
  have hnum : ContDiffOn ℝ 6 (fun z : ℝ => 2 * z ^ 2) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_const.mul (contDiffOn_id.pow 2)
  have hdenm : ContDiffOn ℝ 6 (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_const.add contDiffOn_id).pow 3
  exact (hnum.div hdenm hden).div_const _

/-- `radA α f` is `C⁶` on `(0,∞)` — from the `C⁶`-smoothness of `L₁₂f`, which `HkMem α 7 f`
supplies (`contDiffOn6_L12_of`). -/
theorem contDiffOn_six_radA {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 6 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) := by
  have h12 : ContDiffOn ℝ 6 (fun z => Work.Coercivity.L12f f z) (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.StrongPersist.contDiffOn6_L12_of (α := α) (f := f) hsm hmem7
    have hfun : (fun z => Work.Coercivity.L12f f z)
        = fun z => Work.Construction.L12 f z := rfl
    rw [hfun]
    exact h
  have hfun : Work.FTS.CoercivityFix.Transfer.radA α f
      = fun z => -(Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)
          + ((Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) := by
    funext z
    rw [Work.FTS.CoercivityFix.Transfer.radA_eq]
    simp only [Work.FTS.CoercivityFix.Transfer.ampA, Work.FTS.CoercivityFix.Transfer.ampB]
    ring
  rw [hfun]
  exact (((contDiffOn_six_ampA hα hα1).mul h12).neg).add
    ((contDiffOn_six_ampB_div α).mul contDiffOn_const)

/-- **`Corr α f` is `C⁶` on the open quadrant.** -/
theorem contDiffOn_six_Corr {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 6 (Function.uncurry (Work.FTS.CoercivityFix.Corr α f))
      Work.FTS.EllipticEst.Q0 := by
  have hsep := Work.FTS.StrongPersist.linMem_sep_mul (α := α) (n := 6)
    (B := Work.FTS.CoercivityFix.Transfer.radA α f) (contDiffOn_six_radA hα hα1 hsm hmem7)
  have hfun : Work.FTS.CoercivityFix.Corr α f
      = fun z θ => Work.Spaces.c α * (Work.FTS.StrongPersist.gamCoef α θ
          * Work.FTS.CoercivityFix.Transfer.radA α f z) := by
    funext z θ
    rw [Corr_eq_sep α f]
    show Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α f z
      = Work.Spaces.c α * (Work.FTS.StrongPersist.gamCoef α θ
          * Work.FTS.CoercivityFix.Transfer.radA α f z)
    rw [congrFun (Gam_eq_c_mul_gamCoef hα hα1) θ]
    ring
  rw [hfun]
  have hconst : ContDiffOn ℝ 6 (fun _ : ℝ × ℝ => Work.Spaces.c α)
      Work.FTS.EllipticEst.Q0 := contDiffOn_const
  refine (hconst.mul hsep).congr (fun p _ => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Pi.mul_apply, Function.uncurry_apply_pair]

/-- **Continuity of the `ℋ⁶`-integrand of `Corr α f` on the open quadrant**: the hypothesis of
`LocData.HkMem_of_majorant`. -/
theorem continuousOn_HkIntegrand_Corr {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 6 (Work.FTS.CoercivityFix.Corr α f) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
  Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (le_refl 6)
    (contDiffOn_six_Corr hα hα1 hsm hmem7)

/-! ## §4 The two conclusions, given the angular and radial inputs -/

/-- The angular mass is nonnegative (`Mth6_nonneg` on `Iθ`). -/
theorem Mth6_integral_nonneg (α : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ hθ => ?_)
  exact Work.FTS.StrongPersist.Mth6_nonneg α hθ

/-- **`HkMem α 6 (Corr α f)`** from the angular bound `∫_θ Mth6 α ≤ Cang` and the radial bound
`∫_z SlotSum (radA α f) ≤ Crad·HkSq α 6 f` (`LocData.HkMem_of_majorant` with the majorant
`M z θ = c(α)²·Mth6 α θ·SlotSum (radA α f) z`). -/
theorem HkMem_Corr_of {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f)
    {Cang : ℝ}
    (hang : ∀ β ∈ Set.Ioc 0 1,
      (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 β θ) ≤ Cang)
    {Crad : ℝ}
    (hrad : MeasureTheory.IntegrableOn
        (Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        ≤ Crad * Work.Spaces.HkSq α 6 f) :
    Work.Spaces.HkMem α 6 (Work.FTS.CoercivityFix.Corr α f) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 6
    (f := Work.FTS.CoercivityFix.Corr α f)
    (M := fun z θ => (Work.Spaces.c α) ^ 2 * Work.FTS.StrongPersist.Mth6 α θ
        * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
    ?_ ?_ ?_ ?_
  · exact continuousOn_HkIntegrand_Corr hα hα1 hsm hmem7
  · intro z hz
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => ((Work.Spaces.c α) ^ 2
            * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          * Work.FTS.StrongPersist.Mth6 α θ) Work.Spaces.Iθ :=
      (Work.FTS.StrongPersist.Mth6_integrable (α := α) hα hα1).const_mul _
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  · have hfun : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.c α) ^ 2 * Work.FTS.StrongPersist.Mth6 α θ
          * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        = fun z => ((Work.Spaces.c α) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ))
          * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z := by
      funext z
      have h1 : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.c α) ^ 2 * Work.FTS.StrongPersist.Mth6 α θ
              * Work.FTS.StrongPersist.SlotSum
                (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          = ∫ θ in Work.Spaces.Iθ,
              ((Work.Spaces.c α) ^ 2
                * Work.FTS.StrongPersist.SlotSum
                  (Work.FTS.CoercivityFix.Transfer.radA α f) z)
                * Work.FTS.StrongPersist.Mth6 α θ :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => by ring)
      rw [h1, MeasureTheory.integral_const_mul]
      ring
    rw [hfun]
    exact hrad.1.const_mul _
  · intro z hz θ hθ
    exact HkIntegrand_Corr_le hα hα1 f hθ

/-- **The quantitative bound** `HkSq α 6 (Corr α f) ≤ 100·Cang·Crad·HkSq α 6 f`, from the same
two inputs (together with the `ℋ⁶`-membership, which makes the slices integrable). -/
theorem HkSq_Corr_le_of {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hmem6 : Work.Spaces.HkMem α 6 (Work.FTS.CoercivityFix.Corr α f))
    {Cang Crad : ℝ} (hCang : 0 ≤ Cang)
    (hang : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ) ≤ Cang)
    (hrad : MeasureTheory.IntegrableOn
        (Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        ≤ Crad * Work.Spaces.HkSq α 6 f) :
    Work.Spaces.HkSq α 6 (Work.FTS.CoercivityFix.Corr α f)
      ≤ (100 * Cang * Crad) * Work.Spaces.HkSq α 6 f := by
  have hc2 : (Work.Spaces.c α) ^ 2 ≤ 100 := by
    have h := (Work.Spaces.c_bounds α hα hα1).2
    nlinarith [Work.FTS.StrongPersist.L3Aux.c_pos hα hα1]
  have hA0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ :=
    Mth6_integral_nonneg α
  have hS0 : 0 ≤ ∫ z in Work.Spaces.Iz,
      Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z :=
    integral_nonneg fun z => Work.FTS.StrongPersist.SlotSum_nonneg _ z
  have hB0 : 0 ≤ Crad * Work.Spaces.HkSq α 6 f := le_trans hS0 hrad.2
  have hstep : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (Work.FTS.CoercivityFix.Corr α f) z θ)
        ≤ ((Work.Spaces.c α) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ))
          * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => ((Work.Spaces.c α) ^ 2
            * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          * Work.FTS.StrongPersist.Mth6 α θ) Work.Spaces.Iθ :=
      (Work.FTS.StrongPersist.Mth6_integrable (α := α) hα hα1).const_mul _
    have h2 := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      h1
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => by
          refine le_trans (HkIntegrand_Corr_le hα hα1 f hθ) ?_
          exact le_of_eq (by ring)))
    rw [MeasureTheory.integral_const_mul] at h2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
        (Work.FTS.CoercivityFix.Corr α f) z θ)
      ≤ ∫ z in Work.Spaces.Iz, ((Work.Spaces.c α) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ))
          * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      (hrad.1.const_mul _) hstep
  rw [Work.Spaces.HkSq]
  refine houter.trans ?_
  rw [MeasureTheory.integral_const_mul]
  calc ((Work.Spaces.c α) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ))
        * (∫ z in Work.Spaces.Iz,
            Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
      ≤ ((Work.Spaces.c α) ^ 2 * Cang)
          * (∫ z in Work.Spaces.Iz,
            Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hang (sq_nonneg _)) hS0
    _ ≤ ((Work.Spaces.c α) ^ 2 * Cang) * (Crad * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hrad.2
          (mul_nonneg (sq_nonneg _) hCang)
    _ ≤ (100 * Cang) * (Crad * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 hCang) hB0
    _ = (100 * Cang * Crad) * Work.Spaces.HkSq α 6 f := by ring

end Work.FTS.StrongPersist.H6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.q0Sm_Corr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

open scoped Real Topology
open MeasureTheory Set

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The three elementary ingredients

`Corr α f = Γ(θ)·radA α f z` (`Transfer.Corr_eq_radA`), where

`radA α f z = −ampA α z·L₁₂ f(z) + (ampB α z/c(α))·L₁₂(Transport f)(0)`,

`ampA α z = 2z/(c(α)(1+z)²)`, `ampB α z = 2z²/(1+z)³`.  Each factor is smooth on its own
domain: `L₁₂ f` is `C⁶` on `(0,∞)` (order-seven honesty of `f`, `LinMem6Acf.contDiffOn6_L12_of`),
the two rational `z`-factors are `C^∞` on `(0,∞)` (their denominators do not vanish there,
`c(α) ≠ 0` from `Spaces.c_bounds`), and `Γ` is `C^∞` on `(0,π/2)` (`OpenPkg.contDiffOn_Gam_Q0`).
The lemmas below assemble them. -/

/-- `c(α) ≠ 0` for `0 < α ≤ 1` (from `1/10 ≤ c(α)`, `Work.Spaces.c_bounds`). -/
theorem c_ne_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : Work.Spaces.c α ≠ 0 := by
  have h := (Work.Spaces.c_bounds α hα hα1).1
  intro h0; rw [h0] at h; norm_num at h

/-- The nonlocal `z`-factor `ampA α = 2z/(c(α)(1+z)²)` is `C^n` on `(0,∞)`. -/
theorem contDiffOn_ampA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    ContDiffOn ℝ n (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) := by
  have hc := c_ne_zero hα hα1
  change ContDiffOn ℝ n (fun z : ℝ => 2 * z / (Work.Spaces.c α * (1 + z) ^ 2))
    (Set.Ioi (0 : ℝ))
  exact (((contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_id).div
    ((contDiffOn_const (c := Work.Spaces.c α)).mul
      (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 2))
    (fun z hz => mul_ne_zero hc (pow_ne_zero 2 (by linarith [show (0 : ℝ) < z from hz]))))

/-- The projector `z`-factor `ampB α = 2z²/(1+z)³` is `C^n` on `(0,∞)` (it does not depend on
`α`). -/
theorem contDiffOn_ampB (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi (0 : ℝ)) := by
  change ContDiffOn ℝ n (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) (Set.Ioi (0 : ℝ))
  exact (((contDiffOn_const (c := (2 : ℝ))).mul (contDiffOn_id.pow 2)).div
    (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 3)
    (fun z hz => pow_ne_zero 3 (by linarith [show (0 : ℝ) < z from hz])))

/-- **The radial profile of the transfer defect is `C⁶` on the open half-line** as soon as
`L₁₂ f` is. -/
theorem contDiffOn_radA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hL : ContDiffOn ℝ 6 (fun z => Work.Coercivity.L12f f z) (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ 6 (fun z => Work.FTS.CoercivityFix.Transfer.radA α f z) (Set.Ioi (0 : ℝ)) := by
  have hampA := contDiffOn_ampA α hα hα1 6
  have hampB := contDiffOn_ampB α 6
  have key : ContDiffOn ℝ 6
      (fun z : ℝ => -(Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)
        + (Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi (0 : ℝ)) :=
    ((hampA.mul hL).neg).add ((hampB.div_const (Work.Spaces.c α)).mul contDiffOn_const)
  refine key.congr (fun z _ => ?_)
  simp only [Work.FTS.CoercivityFix.Transfer.radA]
  ring

/-- **`L₁₂ f` is `C⁶` on `(0,∞)`** for the coercivity class `H6Adm α f` with order-seven
honesty.  (The statement of `LinMem6Acf.contDiffOn6_L12_of` is phrased with
`Construction.L12`, which is `Coercivity.L12f` definitionally.) -/
theorem contDiffOn6_L12f {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 6 (fun z => Work.Coercivity.L12f f z) (Set.Ioi (0 : ℝ)) := by
  have h := Work.FTS.StrongPersist.contDiffOn6_L12_of (α := α) (f := f) hsm hmem7
  rwa [show (fun z => Work.Construction.L12 f z)
        = (fun z => Work.Coercivity.L12f f z) from rfl] at h

/-- **Finite-order regularity of the nonlocal correction.**  `Corr α f = LGammaT α f − Lhat f` is, by `Corr_eq`, the separated sum `-(2zΓ(θ)/(c(1+z)²))·L₁₂(f)(z) + (Γ(θ)/c)(2z²/(1+z)³)·L₁₂(Transport f)(0)`.  For `H6Adm α f` (giving `SmoothOpen f` and `L₁₂f(0) = 0`) and order-seven honesty `HkMem α 7 f`, the moment `L₁₂ f` is `C^6` on `(0,∞)` (`EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk`, packaged as `L6Aux.LinMem6Acf.contDiffOn6_L12_of`), so `Corr α f` is `C^6` on the open quadrant — the finite-order class the level-six additivity clause needs.  (The *infinite-order* statement is false — see `NOTES_L3_lin_FALSE.md` — but order six suffices.) -/
theorem q0Sm_Corr : ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.FTS.CoercivityFix.Transfer.Q0Sm 6 (Work.FTS.CoercivityFix.Corr α f) := by
  refine ⟨1, one_pos, ?_⟩
  intro α hα f hadm h7
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the two analytic inputs
  have hL : ContDiffOn ℝ 6 (fun z => Work.Coercivity.L12f f z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn6_L12f hadm.reg.1 h7
  have hR : ContDiffOn ℝ 6 (fun z => Work.FTS.CoercivityFix.Transfer.radA α f z)
      (Set.Ioi (0 : ℝ)) := contDiffOn_radA α hα0 hα1 hL
  -- the separated product is `C⁶` on the quadrant
  have hGR : ContDiffOn ℝ 6
      (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2 * Work.FTS.CoercivityFix.Transfer.radA α f p.1)
      Work.Construction.Qd := by
    have h1 : ContDiffOn ℝ 6 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
        Work.Construction.Qd := Work.FTS.OpenPkg.contDiffOn_Gam_Q0 α 6
    exact h1.mul (hR.comp contDiffOn_fst (fun p hp => hp.1))
  -- `Corr` is that product
  have hfun : Work.FTS.CoercivityFix.Corr α f
      = fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α f z := by
    funext z θ
    exact Work.FTS.CoercivityFix.Transfer.Corr_eq_radA α f z θ
  rw [hfun]
  unfold Work.FTS.CoercivityFix.Transfer.Q0Sm
  exact hGR

end Work.FTS.StrongPersist.H6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6LinMem6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm HkIntegrand)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §5 The projector summand `Bcoef α · K0f f` -/

/-- The projector summand is in `ℋ⁶`: it is the constant `K0f f` times the fixed smooth
separated coefficient `Bcoef α`. -/
theorem Bcoef_mem6_of {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hB : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ∧
      Work.Spaces.HkMem α 6
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3))) :
    Work.Spaces.HkMem α 6 (fun z θ => Bcoef α z θ * K0f f) := by
  have h1 : Work.Spaces.HkMem α 6
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) := hB.2
  have h2 := Work.FTS.LocData.HkMem_const_mul α 6 (K0f f) h1
  have hfun : (fun z θ => (K0f f) * ((Work.Spaces.Gam α θ / Work.Spaces.c α)
        * (2 * z ^ 2 / (1 + z) ^ 3))) = fun z θ => Bcoef α z θ * K0f f := by
    funext z θ
    rw [Bcoef_eq_mul, gamCoef, bcoef]
    ring
  rwa [hfun] at h2

/-- The projector summand is `C^∞` on the open quadrant (hence `C⁶`). -/
theorem Bcoef_smoothOpen_of {α : ℝ} {f : Fn}
    (hB : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -(Bcoef α z θ * K0f f)) := by
  have h1 : (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3))
      = fun z θ => Bcoef α z θ := by
    funext z θ
    rw [Bcoef_eq_mul]
    rfl
  rw [h1] at hB
  refine linMem_neg ?_
  have h2 : (fun z θ => Bcoef α z θ * K0f f) = fun z θ => (K0f f) * Bcoef α z θ := by
    funext z θ
    ring
  rw [h2]
  exact linMem_const_mul (K0f f) hB

/-! ## §6 The assembly -/

/-- **The `ℋ⁶`-membership of the linear part.** -/
theorem H6LinMem6 : ∃ α₂ : ℝ, 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.linPart α f) := by
  obtain ⟨K₁, hK₁, hK₁b⟩ := Work.FTS.StrongPersist.L6Aux.PhiZopBound6
  obtain ⟨K₂, hK₂, hK₂b⟩ := Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
  obtain ⟨C₂, hC₂, hBc⟩ := Work.FTS.StrongPersist.L6Aux.BcoefMem6
  obtain ⟨C₃, hC₃, hL12⟩ := Work.FTS.StrongPersist.L6Aux.L12SlotSum6
  refine ⟨1, one_pos, ?_⟩
  intro α hαIoc f hf hmem7
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have h0 : Work.Construction.L12 f 0 = 0 := hf.l12
  -- the `acoef`-jet bound in the `Zop`-form of `zmul_finite6`
  have hzb2 : ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] acoef z| ≤ K₂ := by
    intro b hb z hz
    have hz' : (0 : ℝ) < z := hz
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz'
    have hθ0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_refl 0, by linarith [Real.pi_pos]⟩
    have h := hK₂b b hb z hzI 0 hθ0
    have h2 : Work.Spaces.Zop^[b] acoef z
        = Work.Spaces.DzIter b (fun z (_ : ℝ) => acoef z) z 0 :=
      (congrFun (Work.Spaces.Zop_slice b (fun z (_ : ℝ) => acoef z) 0) z).symm
    rw [h2]
    exact h
  -- the radial slot sum of `L₁₂ f`
  have hslot := hL12 α hα0 hα1 f hsm hmem6 h0
  -- the level-six separation lemma, in the `Mth6`/`SlotSum` vocabulary
  have hsep : ∀ {z θ : ℝ}, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 6
          (fun z' θ' => gamCoef α θ' * Work.Construction.L12 f z') z θ
        ≤ Mth6 α θ * SlotSum (fun z => Work.Construction.L12 f z) z := by
    intro z θ hθ
    simpa only [Mth6, SlotSum] using
      (Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 6)
        (C := gamCoef α) (B := fun z => Work.Construction.L12 f z) hθ)
  -- the three memberships
  have hloc : Work.Spaces.HkMem α 6 (locOp f) :=
    LocOp_mem6_of hα0 hK₁.le (fun b hb z hz => hK₁b b hb z (le_of_lt hz)) hsm hmem7
  have hacf : Work.Spaces.HkMem α 6 (fun z θ => Acoef α z θ * Mf f z θ) :=
    Acf_mem6_of hα0 hα1 hK₂.le hzb2 hslot hsep hsm hmem7 h0
  have hproj0 : Work.Spaces.HkMem α 6 (fun z θ => Bcoef α z θ * K0f f) :=
    Bcoef_mem6_of hα0 hα1 ⟨(hBc α hα0 hα1).1, (hBc α hα0 hα1).2.1⟩
  have hproj : Work.Spaces.HkMem α 6 (fun z θ => -(Bcoef α z θ * K0f f)) := by
    have h := Work.FTS.LocData.HkMem_const_mul α 6 (-1) hproj0
    rwa [show (fun z θ => (-1) * (Bcoef α z θ * K0f f))
        = fun z θ => -(Bcoef α z θ * K0f f) from by funext z θ; ring] at h
  -- the finite-order smoothness of the summands
  have h12 : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn6_L12_of hsm hmem7
  have hloc6 : ContDiffOn ℝ 6 (Function.uncurry (locOp f)) Work.FTS.EllipticEst.Q0 :=
    (locOp_smoothOpen hsm).forall 6
  have hacf6 : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => Acoef α z θ * Mf f z θ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn6_Acf h12
  have hproj6 : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => -(Bcoef α z θ * K0f f))) Work.FTS.EllipticEst.Q0 :=
    (Bcoef_smoothOpen_of (hBc α hα0 hα1).1).forall 6
  have hsum6 : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => locOp f z θ + Acoef α z θ * Mf f z θ))
      Work.FTS.EllipticEst.Q0 :=
    (hloc6.add hacf6).congr (fun p hp => rfl)
  -- the glue
  have hsum : Work.Spaces.HkMem α 6 (fun z θ => locOp f z θ + Acoef α z θ * Mf f z θ) :=
    (Work.FTS.StrongPersist.HkAddFin hloc6 hacf6 hloc hacf).1
  have hmem : Work.Spaces.HkMem α 6
      (fun z θ => (locOp f z θ + Acoef α z θ * Mf f z θ) + (-(Bcoef α z θ * K0f f))) :=
    (Work.FTS.StrongPersist.HkAddFin hsum6 hproj6 hsum hproj).1
  have hlin : linPart α f = fun z θ => (locOp f z θ + Acoef α z θ * Mf f z θ)
      + (-(Bcoef α z θ * K0f f)) := by
    rw [linPart_eq]
    funext z θ
    ring
  rwa [hlin]

end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.FkRowPrices =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section




end

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.fkSlotShift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open MeasureTheory Set

set_option maxHeartbeats 1600000

/-! ## The `canonW`-weighted slot shift

The requested lemma is the "slot shift": a leaf weight `ρ` attached to the slot of order `a`
(the three leaves being `leafEta = w²sin(2θ)^{-η}`, `leafOne = w²` and, for `a ≥ 1`,
`leafGam α = w²sin(2θ)^{-γ}`) prices *any* higher slot `(a', j)` with `a ≤ a'` and
`a' + j ≤ 6`, with the same bound `C·HkSq α 6 f`.

Pointwise, every leaf weight of the slot of order `a ≤ a'` is dominated by `canonW q` for an
exponent `q` admissible at the higher slot `(a', j)` (namely `q ∈ {η, 0, γ}`, and the `γ`-leaf
necessarily comes with `a ≥ 1`, hence `a' ≥ 1`), and the level-six slot estimates
`T1SixAux.slotSliceIntegrable` / `T1SixAux.slotEnergyZOuter` give exactly the three conjuncts
of the target. -/




/-- `leafOne = w²` is the canonical weight `canonW 0`. -/
private theorem leafOne_eq_canonW_zero_prv :
    Work.FTS.TransportS.leafOne = Work.FTS.TransportS.SlotT2.canonW 0 := by
  funext z θ
  simp only [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW, neg_zero,
    Real.rpow_zero, mul_one]


end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSinSqLeibniz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux



end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The two endpoints are null for the angular measure -/

/-- For `volume.restrict Iθ` the two endpoints `0`, `π/2` are null, so `θ` lies in the open
interval almost everywhere. -/
private theorem ae_mem_Ioo_Iθ_prv :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## The leaf weights: vanishing at `z = 0`, and continuity on the open quadrant -/




/-! ## Integrability of the angular slice, and of the `z`-marginal -/



/-! ## The requested lemma -/


end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
