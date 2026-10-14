import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Ring.Real
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_bslOp_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_smooth_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsODEDefs
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCoefCase
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.NstarRow
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkJets
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMass
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyLeft
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.ClassCHon.CmpSupp.coeff_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.ClassCHon.CmpSupp


end Work.FTS.ClassCHon.CmpSupp
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.EpsSqIter_mixed_Jeps_le_gen =====
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

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## The order-six mass bound for the routed kernels -/

/-- **The mass of a routed kernel is at most the level-`M` mass** `Ksm ρ 1 M`.  This is the
general-`M` form of the level-three bound contained in `KdKFacts` (`Ksm` is the double sum of
the masses of all routed kernels of order `≤ M`, so every slot of order `≤ M` is dominated by
`Ksm ρ 1 M`). -/
theorem integral_abs_KdK_one_le_Ksm_gen (ρ : ℝ × ℝ → ℝ) {M a b : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
      ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M := by
  simp only [Work.FTS.StrongEps.EpsE4Thr.Ksm]
  calc ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
      ≤ ∑ a' ∈ Finset.range (M + 1),
          ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b p| :=
        Finset.single_le_sum (f := fun a' => ∫ p : ℝ × ℝ,
            |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b p|)
          (fun _ _ => integral_nonneg fun p => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))
    _ ≤ ∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1),
          ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b' p| :=
        Finset.sum_le_sum fun a' _ => Finset.single_le_sum
          (f := fun b' => ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b' p|)
          (fun _ _ => integral_nonneg fun p => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))

/-! ## The main theorem -/

theorem EpsSqIter_mixed_Jeps_le_gen (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ f : Work.FTS.Galerkin.Fn,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) →
        Work.FTS.StrongEps.EpsMem α f →
          Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε f) ∧
          ∀ j i : ℕ, j + i ≤ M →
            (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
                  * Work.FTS.StrongEps.epsW α z θ) ^ 2))
              ≤ ENNReal.ofReal (C * (C / ε) ^ (2 * (j + i)) * Work.FTS.StrongEps.EpsSq α f) := by
  obtain ⟨c, hcpos, hWc⟩ := Work.FTS.StrongEps.HkSqAux.Wt_shift_le
  obtain ⟨δ, hδpos, hJac0⟩ := Work.FTS.StrongEps.HkSqAux.logJac_shift_le
  have hc0 : 0 ≤ c := hcpos.le
  have hδ0 : 0 ≤ δ := hδpos.le
  obtain ⟨kscale, ksm_le, kint, ksupp, kmom⟩ := Work.FTS.StrongEps.EpsSqTools.KdKFacts ρ hρ
  set Cv : ℝ := max 1 (((4 : ℝ) ^ M) * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2
    * Real.exp (2 * (2 * c + δ))) with hCv
  have hCv1 : 1 ≤ Cv := le_max_left _ _
  have hCvpos : 0 < Cv := lt_of_lt_of_le zero_lt_one hCv1
  have hCvbig : ((4 : ℝ) ^ M) * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2
      * Real.exp (2 * (2 * c + δ)) ≤ Cv := le_max_right _ _
  refine ⟨Cv, hCvpos, ?_⟩
  intro α hα ε hε0 hε1 f hf hfmem
  have hα0 : 0 < α := hα.1
  have hfcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2) Work.FTS.StrongEps.Quad :=
    (hf 0).continuousOn
  have hFcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2
      * Work.FTS.StrongEps.epsW α q.1 q.2) Work.FTS.StrongEps.Quad :=
    hfcont.mul (Work.FTS.StrongEps.EpsSqTools.continuousOn_epsW_quad α)
  have hFmeas : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal
      ((f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2))
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hfmem.aestronglyMeasurable.aemeasurable
  -- the generic chain, for every slot `(j,i)`
  have hgen : ∀ j i : ℕ,
      (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
            * Work.FTS.StrongEps.epsW α z θ) ^ 2))
        ≤ ENNReal.ofReal ((((4 : ℝ) ^ i
              * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|)
            * (Real.exp (2 * (2 * c + δ))
              * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|))
            * Work.FTS.StrongEps.EpsSq α f) := by
    intro j i
    set A : ℝ := ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| with hAdef
    set Λ : ℝ × ℝ → ℝ := fun p =>
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| * Real.exp (2 * c * (|p.1| + |p.2|))
      with hΛdef
    have hA0 : 0 ≤ A := by
      rw [hAdef]
      exact integral_nonneg fun p => abs_nonneg _
    have hΛ0 : ∀ p : ℝ × ℝ, 0 ≤ Λ p := by
      intro p
      rw [hΛdef]
      exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
    have hpt : ∀ {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
              * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ ENNReal.ofReal (4 ^ i * A) * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
      intro z θ hz hθ
      exact Work.FTS.StrongEps.EpsSqTools.MixedJepsEpsWpt ρ hρ (ε := ε) (α := α) (c := c)
        hε0 (f := f) hf hz hθ
        (fun p => hWc α hα z θ p.1 p.2 hz hθ) j i
    have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
              * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ ENNReal.ofReal (4 ^ i * A) * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
      intro z hz θ hθ
      by_cases hc' : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
      · exact hpt hc'.1 hc'.2
      · rw [Work.FTS.StrongEps.EpsSqTools.epsW_eq_zero_of_not_mem_quad hα0 hz hθ hc', mul_zero,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero]
        exact zero_le
    have hΛexp : ∀ p : ℝ × ℝ, Λ p * Real.exp (δ * (|p.1| + |p.2|))
        = |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|
            * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)) := by
      intro p
      rw [hΛdef, mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    have hΛfin : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|)))
        ≤ ENNReal.ofReal (Real.exp (2 * (2 * c + δ)) * A) := by
      refine le_trans (le_of_eq (lintegral_congr (fun p => by rw [hΛexp p]))) ?_
      simpa only [hAdef] using kmom hε0 hε1 hc0 hδ0 j i
    have hΛcont : Continuous Λ := by
      rw [hΛdef]
      refine (Work.FTS.StrongEps.EpsE4Thr.KdK_continuous hρ ε j i).abs.mul ?_
      refine Real.continuous_exp.comp ?_
      exact continuous_const.mul
        ((continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd))
    have hAe : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2)
        * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
              (Work.FTS.StrongEps.thShift z.1.2 z.2.2)
            * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
                (Work.FTS.StrongEps.thShift z.1.2 z.2.2)) ^ 2))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
      have h2 := Work.FTS.StrongEps.EpsSqTools.aemeasurable_shift_comp'
        (F := fun q : ℝ × ℝ => ENNReal.ofReal
          ((f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)) hFmeas
      have h1 : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2))
          (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
        (ENNReal.measurable_ofReal.comp hΛcont.measurable).comp_aemeasurable
          measurable_snd.aemeasurable
      exact h1.mul h2
    have hC₀ : 0 ≤ (4 : ℝ) ^ i * A := mul_nonneg (by positivity) hA0
    have hKmass : 0 ≤ Real.exp (2 * (2 * c + δ)) * A :=
      mul_nonneg (Real.exp_pos _).le hA0
    exact Work.FTS.StrongEps.EpsSqTools.iter_le_of_pointwise (α := α) (c := c) (δ := δ) (Λ := Λ)
      (C₀ := (4 : ℝ) ^ i * A) (Kmass := Real.exp (2 * (2 * c + δ)) * A)
      (f := f) (g := Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f))
      hC₀ hKmass hΛ0 hΛfin hfmem hJac0 hFcont hAe hP
  -- finiteness of the `(0,0)` slot, hence `EpsMem α (J_ε f)`
  have hlin0 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (((Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * Work.FTS.StrongEps.epsW α z θ) ^ 2)) < ⊤ := by
    have h := hgen 0 0
    simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] at h
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hEmem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε f) := by
    have hJcont : ContinuousOn (fun q : ℝ × ℝ => Work.FTS.StrongEps.Jeps ρ ε f q.1 q.2)
        Work.FTS.StrongEps.Quad :=
      Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps hρ.moll hε0 hfcont
    have hcont2 : ContinuousOn (fun q : ℝ × ℝ =>
        ((Work.FTS.StrongEps.Jeps ρ ε f) q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)
        Work.FTS.StrongEps.Quad :=
      (hJcont.mul (Work.FTS.StrongEps.EpsSqTools.continuousOn_epsW_quad α)).pow 2
    have hAESM : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        ((Work.FTS.StrongEps.Jeps ρ ε f) q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (by simpa only [Work.FTS.StrongEps.Quad] using hcont2)
    have hfin : MeasureTheory.HasFiniteIntegral (fun q : ℝ × ℝ =>
        ((Work.FTS.StrongEps.Jeps ρ ε f) q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun q => sq_nonneg _)]
      rw [← MeasureTheory.lintegral_lintegral (f := fun z θ => ENNReal.ofReal
          (((Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2))
        (hAESM.aemeasurable.ennreal_ofReal)]
      exact hlin0
    have hmeas : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]
    rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hmeas]
    exact ⟨hAESM, hfin⟩
  refine ⟨hEmem, ?_⟩
  intro j i hji
  have hjM : j ≤ M := by omega
  have hiM : i ≤ M := by omega
  have hZ := hgen j i
  -- the constants
  have hKsm0 : 0 ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M :=
    Work.FTS.StrongEps.EpsE4Thr.Ksm_nonneg hρ 1 M
  set A : ℝ := ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg fun p => abs_nonneg _
  have hA_bound : A ≤ ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M := by
    rw [hAdef, kscale hε0 j i]
    exact mul_le_mul_of_nonneg_left (integral_abs_KdK_one_le_Ksm_gen ρ hjM hiM) (by positivity)
  have hAA : A ^ 2 ≤ (ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2 :=
    pow_le_pow_left₀ hA0 hA_bound 2
  have h4i : (4 : ℝ) ^ i ≤ (4 : ℝ) ^ M := pow_le_pow_right₀ (by norm_num) hiM
  have hexp2 : (ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2
      = ε⁻¹ ^ (2 * (j + i)) * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm]
  have hconst : (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
      ≤ Cv * ε⁻¹ ^ (2 * (j + i)) := by
    have h2 : A ^ 2 ≤ ε⁻¹ ^ (2 * (j + i))
        * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2 := by
      rw [← hexp2]
      exact hAA
    calc (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
        = (4 ^ i * Real.exp (2 * (2 * c + δ))) * A ^ 2 := by ring
      _ ≤ (4 ^ i * Real.exp (2 * (2 * c + δ)))
            * (ε⁻¹ ^ (2 * (j + i))
              * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (4 ^ i * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2
              * Real.exp (2 * (2 * c + δ))) * ε⁻¹ ^ (2 * (j + i)) := by ring
      _ ≤ (((4 : ℝ) ^ M) * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2
              * Real.exp (2 * (2 * c + δ))) * ε⁻¹ ^ (2 * (j + i)) := by
          have hfe : (4 : ℝ) ^ i * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2
                * Real.exp (2 * (2 * c + δ))
              = (4 : ℝ) ^ i * ((Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2
                  * Real.exp (2 * (2 * c + δ))) := by ring
          have hfe2 : ((4 : ℝ) ^ M) * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2
                * Real.exp (2 * (2 * c + δ))
              = ((4 : ℝ) ^ M) * ((Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 M) ^ 2
                  * Real.exp (2 * (2 * c + δ))) := by ring
          rw [hfe, hfe2]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right h4i
            (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ ≤ Cv * ε⁻¹ ^ (2 * (j + i)) := mul_le_mul_of_nonneg_right hCvbig (by positivity)
  have hCeps : Cv * ε⁻¹ ^ (2 * (j + i)) ≤ Cv * (Cv / ε) ^ (2 * (j + i)) := by
    refine mul_le_mul_of_nonneg_left ?_ hCvpos.le
    rw [div_eq_mul_inv]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    simpa using mul_le_mul_of_nonneg_right hCv1 (by positivity : (0 : ℝ) ≤ ε⁻¹)
  refine hZ.trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((4 : ℝ) ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
        * Work.FTS.StrongEps.EpsSq α f
      ≤ (Cv * ε⁻¹ ^ (2 * (j + i))) * Work.FTS.StrongEps.EpsSq α f :=
        mul_le_mul_of_nonneg_right hconst (Work.FTS.StrongEps.EpsSq_nonneg α f)
    _ ≤ (Cv * (Cv / ε) ^ (2 * (j + i))) * Work.FTS.StrongEps.EpsSq α f :=
        mul_le_mul_of_nonneg_right hCeps (Work.FTS.StrongEps.EpsSq_nonneg α f)


end

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.sharp_N0_diff =====
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
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.acoeff_perModeEnergy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

/-! ## The per-mode energy inequality in weighted `L²` form

The target is the *normalised* form of the sharp per-mode weighted energy bound
`radGreen_modeEnergy_of_o`:

  `μ_m² ∫_0^∞ (radGreen α m c)² w² ≤ ∫_0^∞ c² w²`,   `μ_m = λ_m − 3α² − 3α(5+α)/2`,

at `c = cmode m F` (clamped outside `(0,∞)`, which is all that `radGreen` sees).  Taking square
roots and using `√(eNorm m) ≥ 1` on the right-hand side turns that into

  `μ_m · √(∫_z (acoeff α m F)² w²) ≤ √(∫_z (√(eNorm m) · cmode m F)² w²)`,

which is exactly the requested statement.  All the analytic hypotheses of
`radGreen_modeEnergy_of_o` (`AEMeasurable c`, `∫_0^1 c²/t⁴ < ∞`, `∫_1^∞ c² < ∞`, the `o(t^{3/2})`
rate) are supplied from `SmoothOpen F` / `HkMem α 0 F` by the imported `Honesty` bricks. -/

/-! ### Two elementary auxiliary lemmas -/

/-- For `z > 0` the value `radGreen α m c z` depends only on the values of `c` on the open
half-line `(0,∞)`: both integrals in `radGreen` are taken over subsets of `(0,∞)`. -/
private lemma radGreen_congr_Ioi_prv {α : ℝ} {m : ℕ} {c₁ c₂ : ℝ → ℝ}
    (h : ∀ t : ℝ, 0 < t → c₁ t = c₂ t) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Radial.radGreen α m c₁ z
      = Work.FTS.PhiStar.Radial.radGreen α m c₂ z := by
  have h1 : (∫ t in (0 : ℝ)..z, c₁ t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = ∫ t in (0 : ℝ)..z, c₂ t * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
    rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht => by rw [h t ht.1])
  have h2 : (∫ t in Set.Ioi z, c₁ t * t ^ (-(2 * (m : ℝ) / α) - 1))
      = ∫ t in Set.Ioi z, c₂ t * t ^ (-(2 * (m : ℝ) / α) - 1) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => by rw [h t (lt_trans hz ht)])
  rw [Work.FTS.PhiStar.Radial.radGreen, Work.FTS.PhiStar.Radial.radGreen, h1, h2]

/-- The arithmetic transfer: `μ² A ≤ B`, `μ > 0`, `B ≥ 0`, `1 ≤ e` give `μ √A ≤ √(e·B)`. -/
private lemma sqrt_mu_bound {μ A B e : ℝ} (hμ : 0 < μ) (hB : 0 ≤ B) (he : 1 ≤ e)
    (h : μ ^ 2 * A ≤ B) : μ * Real.sqrt A ≤ Real.sqrt (e * B) := by
  have h1 : μ * Real.sqrt A ≤ Real.sqrt B := by
    have h2 := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ.le] at h2
  have h3 : Real.sqrt B ≤ Real.sqrt (e * B) := Real.sqrt_le_sqrt (by nlinarith)
  exact le_trans h1 h3

theorem acoeff_perModeEnergy {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 0 F)
    (heNorm : 1 ≤ Work.EllipticEst.ModalSolution.eNorm m)
    (hvy : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |Work.FTS.PhiStar.Series.cmode m F t| ≤ ε * t ^ ((3 : ℝ) / 2)) :
    (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2)
        * Real.sqrt (∫ z in Work.Spaces.Iz,
            (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz,
          (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  classical
  -- the clamped mode coefficient: `radGreen` (and every weighted integral of it) only sees
  -- `cmode m F` on `(0,∞)`
  set cl : ℝ → ℝ := fun z => if 0 < z then Work.FTS.PhiStar.Series.cmode m F z else 0 with hcl
  have hcl_eq : ∀ t : ℝ, 0 < t → cl t = Work.FTS.PhiStar.Series.cmode m F t := by
    intro t ht; simp [hcl, ht]
  have hENpos : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  have hc : AEMeasurable cl (μ := volume) := by
    rw [hcl]
    exact aemeasurable_cmode_clamp (α := α) m hsm
  -- the slice mass uniformly dominates the squared (clamped) mode coefficient
  have hbnd : ∀ z : ℝ, 0 < z → (cl z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        / Work.EllipticEst.ModalSolution.eNorm m := by
    intro z hz
    have h := eNorm_mul_cmode_sq_le_sliceMass (m := m) (F := F) (z := z)
      (integrableOn_sq_sEta_of_HkMem hF hz)
    have h' : (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        * Work.EllipticEst.ModalSolution.eNorm m
        ≤ ∫ θ in Work.Spaces.Iθ,
            (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_comm]; exact h
    rw [hcl_eq z hz]
    exact (le_div_iff₀ hENpos).mpr h'
  -- near `0`: `∫_0^1 c²/t⁴ < ∞`
  have hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (cl t) ^ 2 / t ^ 4) (Set.Ioo 0 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
          * ((∫ θ in Work.Spaces.Iθ,
              (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / t ^ 4))
        (Set.Ioo 0 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_sliceMass_div_z4_of_HkMem hF) _
    refine MeasureTheory.Integrable.mono' (MeasureTheory.IntegrableOn.integrable hdom) ?_ ?_
    · exact (AEMeasurable.div
        ((hc.mono_measure MeasureTheory.Measure.restrict_le_self).pow_const 2)
        ((measurable_id.pow_const 4).aemeasurable)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := ht.1
      have hb := hbnd t ht0
      rw [Real.norm_of_nonneg (by positivity)]
      calc (cl t) ^ 2 / t ^ 4
          ≤ ((∫ θ in Work.Spaces.Iθ,
                (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              / Work.EllipticEst.ModalSolution.eNorm m) / t ^ 4 :=
            div_le_div_of_nonneg_right hb (by positivity)
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
              * ((∫ θ in Work.Spaces.Iθ,
                  (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / t ^ 4) := by
            ring_nf
  -- far `∞`: `∫_1^∞ c² < ∞`
  have hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (cl t) ^ 2) (Set.Ioi 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
          * (∫ θ in Work.Spaces.Iθ,
              (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Ioi 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_sliceMass_Ioi_one_of_HkMem hF) _
    refine MeasureTheory.Integrable.mono' (MeasureTheory.IntegrableOn.integrable hdom) ?_ ?_
    · exact ((hc.mono_measure MeasureTheory.Measure.restrict_le_self).pow_const 2
        ).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      have hb := hbnd t ht0
      rw [Real.norm_of_nonneg (by positivity)]
      calc (cl t) ^ 2
          ≤ ((∫ θ in Work.Spaces.Iθ,
                (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              / Work.EllipticEst.ModalSolution.eNorm m) := hb
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
              * (∫ θ in Work.Spaces.Iθ,
                  (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [div_eq_inv_mul]
  -- the vanishing rate at `0` transfers to the clamped coefficient
  have hvy' : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |cl t| ≤ ε * t ^ ((3 : ℝ) / 2) := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hvy ε hε
    exact ⟨δ, hδ, fun t ht htδ => by rw [hcl_eq t ht]; exact h t ht htδ⟩
  -- the sharp per-mode weighted energy bound for the clamped source
  have hmain : (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2) ^ 2
        * (∫ z in Set.Ioi 0,
            (Work.FTS.PhiStar.Radial.radGreen α m cl z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (cl z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    radGreen_modeEnergy_of_o hα hα4 hm hc hnear hfar hvy'
  -- convert the `Iz`-integral of the solution into the `(0,∞)`-integral of `radGreen α m cl`
  have hAeq : (∫ z in Work.Spaces.Iz,
        (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi 0,
        (Work.FTS.PhiStar.Radial.radGreen α m cl z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    rw [Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    have hrg : Work.FTS.PhiStar.Series.acoeff α m F z
        = Work.FTS.PhiStar.Radial.radGreen α m cl z := by
      rw [show Work.FTS.PhiStar.Series.acoeff α m F z
          = Work.FTS.PhiStar.Radial.radGreen α m
              (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t) z from rfl]
      exact (radGreen_congr_Ioi_prv (fun t ht => hcl_eq t ht) hz).symm
    rw [hrg]
  -- the right-hand side: `(√(eNorm m) · cmode m F)² = eNorm m · (cl)²` on `(0,∞)`
  have hRHS : (∫ z in Work.Spaces.Iz,
        (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
          * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = Work.EllipticEst.ModalSolution.eNorm m
        * (∫ z in Set.Ioi 0, (cl z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hsq : (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
        * Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        = Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hENpos)]
    rw [hsq, ← hcl_eq z hz]; ring
  have hBnn : 0 ≤ ∫ z in Set.Ioi 0, (cl z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    MeasureTheory.integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hμ : 0 < Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [Work.FTS.PhiStar.Radial.lamR]
    nlinarith [sq_nonneg α, hα.le, hα4, hm1]
  rw [hAeq, hRHS]
  exact sqrt_mu_bound hμ hBnn heNorm hmain

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.isBslSol_psiSeries_of_cptQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **`psiSeries α G` is a `bslOp`-solution of a compact-source datum.** -/
theorem isBslSol_psiSeries_of_cptQ {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {G : ℝ → ℝ → ℝ}
    (hG : SmoothCptQ G) (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) :
    Work.Elliptic.IsBslSol α G (Work.FTS.PhiStar.Series.psiSeries α G) :=
  ⟨psiSeries_bslOp_of_cptQ hα hα4 hG hFs,
    fun z => psiSeries_zero_theta_zero α G z,
    fun z => psiSeries_zero_theta_pi_half α G z,
    fun θ hθ => psiSeries_atTop_zero_of_cptQ hα hα4 hG θ hθ⟩

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4NA1 =====
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

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem NA1_HkSq4_le (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (NA1 α) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨K12, hK12, hNA1⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
  refine ⟨K12 ^ 2 + 1, by positivity, ?_⟩
  intro α hαIoc w _ _
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hmem6, hbd⟩ := hNA1 α hα hα1
  have h5w : (0 : ℝ) ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
  have hmono : Work.Spaces.HkSq α 4 (NA1 α) ≤ Work.Spaces.HkSq α 6 (NA1 α) :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hmem6
  have hsq : Work.Spaces.HkSq α 6 (NA1 α) = (Work.Spaces.HkNorm α 6 (NA1 α)) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 (NA1 α))]
  have h3 : (Work.Spaces.HkNorm α 6 (NA1 α)) ^ 2 ≤ (K12 * α ^ 2) ^ 2 :=
    pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 (NA1 α)) hbd 2
  have h4 : (K12 * α ^ 2) ^ 2 ≤ K12 ^ 2 := by
    have h5 : (K12 * α ^ 2) ^ 2 = K12 ^ 2 * (α ^ 2) ^ 2 := by ring
    rw [h5]
    have h6 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
    have h7 : (α ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ^ 2), h6]
    calc K12 ^ 2 * (α ^ 2) ^ 2 ≤ K12 ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h7 (sq_nonneg K12)
      _ = K12 ^ 2 := by ring
  have h8 : Work.Spaces.HkSq α 4 (NA1 α) ≤ K12 ^ 2 :=
    le_trans hmono (le_trans (le_of_eq hsq) (le_trans h3 h4))
  calc Work.Spaces.HkSq α 4 (NA1 α) ≤ K12 ^ 2 := h8
    _ ≤ K12 ^ 2 * (1 + Work.Spaces.HkSq α 5 w) := by
        have h9 : K12 ^ 2 * 1 ≤ K12 ^ 2 * (1 + Work.Spaces.HkSq α 5 w) :=
          mul_le_mul_of_nonneg_left hone (sq_nonneg K12)
        linarith [h9]
    _ ≤ (K12 ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
        have hKnn : (0 : ℝ) ≤ K12 ^ 2 := sq_nonneg K12
        have hHnn : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
        nlinarith [hKnn, hHnn]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4P1 =====
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

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Elementary nonnegativity helpers (the opaque constant `Maj4C` defeats `positivity`) -/

theorem sq_nn (x : ℝ) : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x

theorem four_nn (x : ℝ) : (0 : ℝ) ≤ x ^ 4 := by
  rw [show x ^ 4 = (x ^ 2) ^ 2 by ring]
  exact sq_nonneg _

theorem maj4C1_pos : (0 : ℝ) < Maj4C + 1 := by
  have h := Maj4C_pos
  linarith

theorem maj4C1_nn : (0 : ℝ) ≤ Maj4C + 1 := maj4C1_pos.le

theorem NP3_HkSq4_le (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (NP3 α w) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨CL, hCL, hL12sup⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  have hK4nn : (0 : ℝ) ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 :=
    mul_nonneg (mul_nonneg maj4C1_nn (sq_nn CL)) (four_nn C₀)
  refine ⟨(Maj4C + 1) * CL ^ 2 * C₀ ^ 4 + 1, by linarith, ?_⟩
  intro α hαIoc w hw hXw
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hw.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hm7
  have hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  have hLcd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 6
        (Function.uncurry (fun z (_ : ℝ) => Work.Construction.L12 w z))
        Work.FTS.EllipticEst.Q0 := hL.forall 6
    have h2 : ContDiffOn ℝ 6 (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi 0) :=
      ContDiffOn.prodMk contDiffOn_id contDiffOn_const
    have h3 := h1.comp h2 (fun z hz => ⟨hz, by norm_num, by linarith [Real.pi_gt_three]⟩)
    exact h3.congr (fun z _ => rfl)
  have hjet : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ CL * Work.FTS.Nonlin.Xn α w :=
    fun j hj z hz => hL12sup α w hα hα1 hsmw hm6 hw.l12 j hj z hz
  have hCB : (0 : ℝ) ≤ CL * Work.FTS.Nonlin.Xn α w :=
    mul_nonneg hCL.le (Work.Spaces.HkNorm_nonneg α 4 w)
  have hCsq : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 * α ^ 4 := by
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hw5 : Work.Spaces.HkSq α 4 w ≤ C₀ ^ 2 * α ^ 4 := by
    rw [sq_xn w]; exact hCsq
  have hsqCL : (CL * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ CL ^ 2 * (C₀ ^ 2 * α ^ 4) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hCsq (sq_nonneg CL)
  have h5w : (0 : ℝ) ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
  have hMaj4 : (0 : ℝ) < Maj4C := Maj4C_pos
  have hRnn : (0 : ℝ) ≤ (Maj4C + 1) * (CL ^ 2 * (C₀ ^ 2 * α ^ 4)) :=
    mul_nonneg maj4C1_nn (mul_nonneg (sq_nn CL) (mul_nonneg (sq_nn C₀) (four_nn α)))
  have hM := radialMaj4 (α := α) (B := CL * Work.FTS.Nonlin.Xn α w)
    (X := fun z => Work.Construction.L12 w z) (f := w) hCB hLcd hsmw hm4 hjet
  have h1 : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 w z * w z θ)
      ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 8 := by
    refine le_trans hM ?_
    calc (Maj4C + 1) * (CL * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 4 w
        ≤ (Maj4C + 1) * (CL ^ 2 * (C₀ ^ 2 * α ^ 4)) * (C₀ ^ 2 * α ^ 4) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hsqCL maj4C1_nn) hw5
            (Work.Spaces.HkSq_nonneg α 4 w) hRnn
      _ = (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 8 := by ring
  have hs : Work.Spaces.HkSq α 4 (NP3 α w)
      = (1 / α) ^ 2 * Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 w z * w z θ) :=
    Work.FTS.StrongEps.HkSq_const_mul α 4 (1 / α)
      (fun z θ => Work.Construction.L12 w z * w z θ)
  rw [hs]
  have h2 : (1 / α) ^ 2 * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 8)
      = (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 6 := by
    field_simp <;> ring
  have h3 : (0 : ℝ) ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 := hK4nn
  calc (1 / α) ^ 2 * Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 w z * w z θ)
      ≤ (1 / α) ^ 2 * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 8) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 6 := h2
    _ ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hα.le hα1) h3
    _ ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * (1 + Work.Spaces.HkSq α 5 w) :=
        mul_le_mul_of_nonneg_left hone h3
    _ ≤ ((Maj4C + 1) * CL ^ 2 * C₀ ^ 4 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
        nlinarith [h3, hone, h5w]

theorem NP4b_HkSq4_le (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (NP4b α w) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨CL, hCL, hL12sup⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  have hK0nn : (0 : ℝ) ≤ 4 * (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) maj4C1_nn) (sq_nn CL)) (sq_nn C₀)
  refine ⟨4 * (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 + 1, by linarith, ?_⟩
  intro α hαIoc w hw hXw
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hw.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hm5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 5 (by norm_num) hm7
  have hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  have hLcd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 6
        (Function.uncurry (fun z (_ : ℝ) => Work.Construction.L12 w z))
        Work.FTS.EllipticEst.Q0 := hL.forall 6
    have h2 : ContDiffOn ℝ 6 (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi 0) :=
      ContDiffOn.prodMk contDiffOn_id contDiffOn_const
    have h3 := h1.comp h2 (fun z hz => ⟨hz, by norm_num, by linarith [Real.pi_gt_three]⟩)
    exact h3.congr (fun z _ => rfl)
  have hjet : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ CL * Work.FTS.Nonlin.Xn α w :=
    fun j hj z hz => hL12sup α w hα hα1 hsmw hm6 hw.l12 j hj z hz
  have hCB : (0 : ℝ) ≤ CL * Work.FTS.Nonlin.Xn α w :=
    mul_nonneg hCL.le (Work.Spaces.HkNorm_nonneg α 4 w)
  have hCsq : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 * α ^ 4 := by
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hsqCL : (CL * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ CL ^ 2 * (C₀ ^ 2 * α ^ 4) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hCsq (sq_nonneg CL)
  have h5w : (0 : ℝ) ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
  have hRnn : (0 : ℝ) ≤ (Maj4C + 1) * (CL ^ 2 * (C₀ ^ 2 * α ^ 4)) :=
    mul_nonneg maj4C1_nn (mul_nonneg (sq_nn CL) (mul_nonneg (sq_nn C₀) (four_nn α)))
  have hM := radialMaj4 (α := α) (B := CL * Work.FTS.Nonlin.Xn α w)
    (X := fun z => Work.Construction.L12 w z) (f := Work.Spaces.Dth w)
    hCB hLcd hsmw.Dth
    (Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := 4) (by linarith [hα]) hsmw hm5) hjet
  have hDth : Work.Spaces.HkSq α 4 (Work.Spaces.Dth w) ≤ Work.Spaces.HkSq α 5 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dth_le_succ' α (by linarith [hα]) 4 hm5
  have h1 : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ)
      ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 5 w) := by
    refine le_trans hM ?_
    calc (Maj4C + 1) * (CL * Work.FTS.Nonlin.Xn α w) ^ 2
          * Work.Spaces.HkSq α 4 (Work.Spaces.Dth w)
        ≤ (Maj4C + 1) * (CL ^ 2 * (C₀ ^ 2 * α ^ 4)) * Work.Spaces.HkSq α 5 w := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hsqCL maj4C1_nn) hDth
            (Work.Spaces.HkSq_nonneg α 4 (Work.Spaces.Dth w)) hRnn
      _ = (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 5 w) := by ring
  have hs : Work.Spaces.HkSq α 4 (NP4b α w)
      = (3 / (2 * α)) ^ 2 * Work.Spaces.HkSq α 4
          (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ) :=
    Work.FTS.StrongEps.HkSq_const_mul α 4 (3 / (2 * α))
      (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ)
  rw [hs]
  have h2 : (3 / (2 * α)) ^ 2
        * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 5 w))
      = (9 / 4) * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2) * α ^ 2 * Work.Spaces.HkSq α 5 w := by
    field_simp <;> ring
  have h5 : (0 : ℝ) ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 :=
    mul_nonneg (mul_nonneg maj4C1_nn (sq_nn CL)) (sq_nn C₀)
  have h6 : (9 / 4 : ℝ) * α ^ 2 * Work.Spaces.HkSq α 5 w
      ≤ 4 * (1 + Work.Spaces.HkSq α 5 w) := by
    have h7 : (9 / 4 : ℝ) * α ^ 2 ≤ 4 := by nlinarith [hα2]
    calc (9 / 4) * α ^ 2 * Work.Spaces.HkSq α 5 w ≤ 4 * Work.Spaces.HkSq α 5 w :=
          mul_le_mul_of_nonneg_right h7 h5w
      _ ≤ 4 * (1 + Work.Spaces.HkSq α 5 w) := by linarith [h5w]
  have hHnn : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
  calc (3 / (2 * α)) ^ 2 * Work.Spaces.HkSq α 4
        (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ)
      ≤ (3 / (2 * α)) ^ 2 * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2
          * (α ^ 4 * Work.Spaces.HkSq α 5 w)) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = (9 / 4) * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2) * α ^ 2 * Work.Spaces.HkSq α 5 w := h2
    _ = ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2) * ((9 / 4) * α ^ 2 * Work.Spaces.HkSq α 5 w) := by ring
    _ ≤ ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2) * (4 * (1 + Work.Spaces.HkSq α 5 w)) :=
        mul_le_mul_of_nonneg_left h6 h5
    _ = 4 * (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 * (1 + Work.Spaces.HkSq α 5 w) := by ring
    _ ≤ (4 * (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
        nlinarith [hHnn, hK0nn]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP3_NP4b_HkSq6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Auxiliary lemmas

`HkSq` is homogeneous of degree two in the amplitude *unconditionally* (the version
`Work.FTS.LocData.HkSq_const_mul` carries an unused `HkMem` hypothesis, which we would have to
produce for the product `L₁₂(w)·w`; the identity itself needs none), and the two smallness
absorptions `α^{-2}·(c·|w|₄)² ≤ c²·(C₀')²` and `α^{-2}·HkSq α 2 w ≤ (C₀')²·α²` used at the end. -/

/-- **Homogeneity of `HkSq` in the amplitude, unconditionally.** -/
private theorem HkSq_const_mul_u (α : ℝ) (k : ℕ) (β : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => β * f z θ) = β ^ 2 * Work.Spaces.HkSq α k f := by
  have hpoint : ∀ z θ : ℝ,
      Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ
        = β ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => Work.FTS.LocData.HkIntegrand_const_mul α k β f z θ
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ)
        = β ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z
    rw [funext (fun θ => hpoint z θ)]
    exact MeasureTheory.integral_const_mul (β ^ 2) _
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  simp only [hinner]
  exact MeasureTheory.integral_const_mul (β ^ 2) _

/-- **The absorption of the low `ℋ⁴`-jet of the radial factor.**  If `|ξ| ≤ C₀'·α²` with
`0 < α ≤ 1` then `α^{-2}·(c·ξ)² ≤ c²·C₀'²`. -/
private lemma scale_sq_le {α c ξ C₀' : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc : 0 ≤ c) (_hC₀' : 0 ≤ C₀') (hξ0 : 0 ≤ ξ) (h : ξ ≤ C₀' * α ^ 2) :
    (1 / α) ^ 2 * (c * ξ) ^ 2 ≤ c ^ 2 * C₀' ^ 2 := by
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα0, hα1]
  have h1 : ξ ^ 2 ≤ (C₀' * α ^ 2) ^ 2 := pow_le_pow_left₀ hξ0 h 2
  have h2 : (1 / α) ^ 2 * ξ ^ 2 ≤ (1 / α) ^ 2 * (C₀' * α ^ 2) ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have heq : (1 / α) ^ 2 * (C₀' * α ^ 2) ^ 2 = C₀' ^ 2 * α ^ 2 := by field_simp
  have h3 : C₀' ^ 2 * α ^ 2 ≤ C₀' ^ 2 := by nlinarith [sq_nonneg C₀', hα2]
  calc (1 / α) ^ 2 * (c * ξ) ^ 2 = c ^ 2 * ((1 / α) ^ 2 * ξ ^ 2) := by ring
    _ ≤ c ^ 2 * (C₀' ^ 2 * α ^ 2) := by
        rw [← heq]; exact mul_le_mul_of_nonneg_left h2 (sq_nonneg c)
    _ ≤ c ^ 2 * C₀' ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg c)

/-- **The absorption of the `ℋ²`-slot against the smallness.**  If `H2 ≤ C₀'²·α⁴`, `H6 ≥ 0` and
`0 < α ≤ 1` then `α^{-2}·c²·H6·H2 ≤ c²·C₀'²·H6`. -/
private lemma scale_Hsq_le {α c H6 H2 C₀' : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc : 0 ≤ c) (_hC₀' : 0 ≤ C₀') (hH6 : 0 ≤ H6) (h2 : H2 ≤ C₀' ^ 2 * α ^ 4) :
    (1 / α) ^ 2 * (c ^ 2 * H6 * H2) ≤ c ^ 2 * C₀' ^ 2 * H6 := by
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα0, hα1]
  have h1 : (1 / α) ^ 2 * H2 ≤ (1 / α) ^ 2 * (C₀' ^ 2 * α ^ 4) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have heq : (1 / α) ^ 2 * (C₀' ^ 2 * α ^ 4) = C₀' ^ 2 * α ^ 2 := by field_simp
  have h3 : C₀' ^ 2 * α ^ 2 ≤ C₀' ^ 2 := by nlinarith [sq_nonneg C₀', hα2]
  calc (1 / α) ^ 2 * (c ^ 2 * H6 * H2) = c ^ 2 * H6 * ((1 / α) ^ 2 * H2) := by ring
    _ ≤ c ^ 2 * H6 * (C₀' ^ 2 * α ^ 2) := by
        rw [← heq]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ c ^ 2 * H6 * C₀' ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = c ^ 2 * C₀' ^ 2 * H6 := by ring

/-
Route hint.  Write `NP3 α w = (1/α) • (Lᵢ · w)` and `NP4b α w = (3/(2α)) • (Lᵢ · Dth w)` with
the radial function `Lᵢ z := Work.Construction.L12 w z`, use
`Work.Spaces.HkSq_const_mul` to pull the scalar out, then the engine
`Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split` with `X := Lᵢ`,
`f := w` resp. `f := Work.Spaces.Dth w` (all hypotheses: `ContDiffOn ℝ 6 Lᵢ (Ioi 0)` from
`ClassC.reg` + `EllipticEst.UopHk.contDiffOn_L12_k`, `SmoothOpen f` from `ClassC.reg`+`Dth`,
`HkMem α 6 f` from `ClassC.mem` (`Dth`: `HkMem α 7 w` and `IPGen`/`HkMem_Dth_le`), and the jet
bounds `Blo := CL4 * Xn α w`, `Bhi := CL6 * HkNorm α 6 w` from
`H6Pair6Aux.L12Sup4` / `H6Pair6Aux.L12Sup6`).
The side bounds are `HkSq α 6 (Dth w) ≤ HkSq α 7 w` and `HkSq α 2 (Dth w) ≤ HkSq α 3 w`
(`StrongPersist.H6Aux.HkSq_Dth_le_succ'`), `HkSq α 2 w ≤ HkSq α 4 w = (Xn α w)² ≤ C₀²α⁴`
(`H6Aux.HkSq_mono_order`), so every `α`-power is absorbed by the smallness `Xn α w ≤ C₀α²`.
-/
theorem NP3_NP4b_HkSq6 : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP3 α w)
        ≤ K * (1 + Work.Spaces.HkSq α 6 w) ∧
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4b α w)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  intro C₀
  obtain ⟨C₄, hC₄pos, hC₄⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  obtain ⟨C₆, hC₆pos, hC₆⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
  obtain ⟨CA, hCApos, hCA⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split
  set K : ℝ := CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 * (9 / 4) + 1 with hK
  refine ⟨K, ?_, ?_⟩
  · have h1 : 0 ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 * (9 / 4) := by positivity
    rw [hK]; linarith
  intro α hαIoc w hcls hXn
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hα10 : -(1 / 10 : ℝ) ≤ α := by linarith
  have hreg : Work.FTS.EllipticEst.SmoothOpen w := hcls.reg
  have hmem7 : Work.Spaces.HkMem α 7 w := hcls.mem
  have hmem6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 6 (by norm_num) hmem7
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 4 (by norm_num) hmem7
  have hmem3 : Work.Spaces.HkMem α 3 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 3 (by norm_num) hmem7
  have hl12 : Work.Construction.L12 w 0 = 0 := hcls.l12
  -- ## The smallness
  have hC₀'nn : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
  have hXn' : Work.FTS.Nonlin.Xn α w ≤ max C₀ 0 * α ^ 2 :=
    le_trans hXn (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg α))
  have hXn4sq : Work.Spaces.HkSq α 4 w ≤ (max C₀ 0) ^ 2 * α ^ 4 := by
    have h1 : (Work.Spaces.HkNorm α 4 w) ^ 2 ≤ (max C₀ 0 * α ^ 2) ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXn' 2
    have h2 : Work.Spaces.HkSq α 4 w ≤ (max C₀ 0 * α ^ 2) ^ 2 := by
      simpa only [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 w)] using h1
    calc Work.Spaces.HkSq α 4 w ≤ (max C₀ 0 * α ^ 2) ^ 2 := h2
      _ = (max C₀ 0) ^ 2 * α ^ 4 := by ring
  have hE6nn : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
  have hE7nn : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hH2le : Work.Spaces.HkSq α 2 w ≤ (max C₀ 0) ^ 2 * α ^ 4 :=
    le_trans (Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hmem4) hXn4sq
  have hH3le : Work.Spaces.HkSq α 3 w ≤ (max C₀ 0) ^ 2 * α ^ 4 :=
    le_trans (Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hmem4) hXn4sq
  have hE6le7 : Work.Spaces.HkSq α 6 w ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hmem7
  -- ## The radial factor: smoothness and the two jet bounds
  have hXcd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
    have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 6 w hα0 hα1 hreg hmem6
      (by norm_num : 2 ≤ 6)
    exact h.congr (fun x _ =>
      (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 w) x).symm)
  have hLo : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ C₄ * Work.FTS.Nonlin.Xn α w :=
    fun j hj z hz => hC₄ α w hα0 hα1 hreg hmem6 hl12 j hj z hz
  have hHi : ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ C₆ * Work.Spaces.HkNorm α 6 w :=
    fun j hj z hz => hC₆ α w hα0 hα1 hreg hmem6 hmem7 hl12 j hj z hz
  -- ## The engine, for an arbitrary field `f`
  have hEng : ∀ (f : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.L12 w z * f z θ)
        ≤ CA * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 6 f
            + (C₆ * Work.Spaces.HkNorm α 6 w) ^ 2 * Work.Spaces.HkSq α 2 f) := by
    intro f hf hm
    exact hCA α (fun z => Work.Construction.L12 w z) f (C₄ * Work.FTS.Nonlin.Xn α w)
      (C₆ * Work.Spaces.HkNorm α 6 w) hXcd hf hm
      (mul_nonneg hC₄pos.le (Work.Spaces.HkNorm_nonneg α 4 w))
      (mul_nonneg hC₆pos.le (Work.Spaces.HkNorm_nonneg α 6 w)) hLo hHi
  have heng3 := hEng w hreg hmem6
  have hDthMem : Work.Spaces.HkMem α 6 (Work.Spaces.Dth w) :=
    Work.FTS.IPGen.HkMem_Dth_le hα10 hreg hmem7
  have heng4 := hEng (Work.Spaces.Dth w) hreg.Dth hDthMem
  have hN6 : (C₆ * Work.Spaces.HkNorm α 6 w) ^ 2 = C₆ ^ 2 * Work.Spaces.HkSq α 6 w := by
    rw [mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 w)]
  have hs1 : (1 / α) ^ 2 * (C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
      ≤ C₄ ^ 2 * (max C₀ 0) ^ 2 :=
    scale_sq_le hα0 hα1 hC₄pos.le hC₀'nn (Work.Spaces.HkNorm_nonneg α 4 w) hXn'
  -- ## `NP3`
  have hsc3 : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP3 α w)
      = (1 / α) ^ 2 * Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.L12 w z * w z θ) := by
    change Work.Spaces.HkSq α 6 (fun z θ => (1 / α)
      * (Work.Construction.L12 w z * w z θ))
      = (1 / α) ^ 2 * Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.L12 w z * w z θ)
    exact HkSq_const_mul_u α 6 (1 / α) _
  have hs2 : (1 / α) ^ 2
      * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w * Work.Spaces.HkSq α 2 w)
      ≤ C₆ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w :=
    scale_Hsq_le hα0 hα1 hC₆pos.le hC₀'nn hE6nn hH2le
  have hb3 : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP3 α w)
      ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
          * (1 + Work.Spaces.HkSq α 6 w) := by
    calc Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP3 α w)
        = (1 / α) ^ 2 * Work.Spaces.HkSq α 6
            (fun z θ => Work.Construction.L12 w z * w z θ) := hsc3
      _ ≤ (1 / α) ^ 2 * (CA * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
            * Work.Spaces.HkSq α 6 w + (C₆ * Work.Spaces.HkNorm α 6 w) ^ 2
            * Work.Spaces.HkSq α 2 w)) :=
          mul_le_mul_of_nonneg_left heng3 (by positivity)
      _ = CA * ((1 / α) ^ 2 * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
              * Work.Spaces.HkSq α 6 w)
            + (1 / α) ^ 2 * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w
              * Work.Spaces.HkSq α 2 w)) := by
          rw [hN6]; ring
      _ = CA * (((1 / α) ^ 2 * (C₄ * Work.FTS.Nonlin.Xn α w) ^ 2)
              * Work.Spaces.HkSq α 6 w
            + (1 / α) ^ 2 * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w
              * Work.Spaces.HkSq α 2 w)) := by ring
      _ ≤ CA * (C₄ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w
            + C₆ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ hs2) hCApos.le
          exact mul_le_mul_of_nonneg_right hs1 hE6nn
      _ = CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w := by ring
      _ ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
            * (1 + Work.Spaces.HkSq α 6 w) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hb3K : CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
        * (1 + Work.Spaces.HkSq α 6 w) ≤ K * (1 + Work.Spaces.HkSq α 6 w) := by
    rw [hK]
    have h1 : 0 ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 := by positivity
    have h2 : CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
        ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 * (9 / 4) + 1 := by nlinarith
    have h3 : 0 ≤ 1 + Work.Spaces.HkSq α 6 w := by linarith
    exact mul_le_mul_of_nonneg_right h2 h3
  -- ## `NP4b`
  have hsc4 : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4b α w)
      = (3 / (2 * α)) ^ 2 * Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ) := by
    change Work.Spaces.HkSq α 6 (fun z θ => (3 / (2 * α))
      * (Work.Construction.L12 w z * Work.Spaces.Dth w z θ))
      = (3 / (2 * α)) ^ 2 * Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ)
    exact HkSq_const_mul_u α 6 (3 / (2 * α)) _
  have hDth6le : Work.Spaces.HkSq α 6 (Work.Spaces.Dth w) ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dth_le_succ' α hα10 6 hmem7
  have hDth2le : Work.Spaces.HkSq α 2 (Work.Spaces.Dth w) ≤ Work.Spaces.HkSq α 3 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dth_le_succ' α hα10 2 hmem3
  have hs2' : (1 / α) ^ 2
      * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w * Work.Spaces.HkSq α 3 w)
      ≤ C₆ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w :=
    scale_Hsq_le hα0 hα1 hC₆pos.le hC₀'nn hE6nn hH3le
  have hb4 : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4b α w)
      ≤ (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
          * (1 + Work.Spaces.HkSq α 7 w) := by
    calc Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4b α w)
        = (3 / (2 * α)) ^ 2 * Work.Spaces.HkSq α 6
            (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ) := hsc4
      _ ≤ (3 / (2 * α)) ^ 2 * (CA * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
            * Work.Spaces.HkSq α 6 (Work.Spaces.Dth w)
            + (C₆ * Work.Spaces.HkNorm α 6 w) ^ 2
              * Work.Spaces.HkSq α 2 (Work.Spaces.Dth w))) :=
          mul_le_mul_of_nonneg_left heng4 (by positivity)
      _ ≤ (3 / (2 * α)) ^ 2 * (CA * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
            * Work.Spaces.HkSq α 7 w
            + (C₆ * Work.Spaces.HkNorm α 6 w) ^ 2
              * Work.Spaces.HkSq α 3 w)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hCApos.le
          · exact mul_le_mul_of_nonneg_left hDth6le (sq_nonneg _)
          · exact mul_le_mul_of_nonneg_left hDth2le (sq_nonneg _)
      _ = (9 / 4) * (CA * ((1 / α) ^ 2 * ((C₄ * Work.FTS.Nonlin.Xn α w) ^ 2
              * Work.Spaces.HkSq α 7 w)
            + (1 / α) ^ 2 * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w
              * Work.Spaces.HkSq α 3 w))) := by
          rw [hN6]; ring
      _ = (9 / 4) * (CA * (((1 / α) ^ 2 * (C₄ * Work.FTS.Nonlin.Xn α w) ^ 2)
              * Work.Spaces.HkSq α 7 w
            + (1 / α) ^ 2 * (C₆ ^ 2 * Work.Spaces.HkSq α 6 w
              * Work.Spaces.HkSq α 3 w))) := by ring
      _ ≤ (9 / 4) * (CA * (C₄ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 7 w
            + C₆ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 6 w)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ hs2') hCApos.le
          exact mul_le_mul_of_nonneg_right hs1 hE7nn
      _ ≤ (9 / 4) * (CA * (C₄ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 7 w
            + C₆ ^ 2 * (max C₀ 0) ^ 2 * Work.Spaces.HkSq α 7 w)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hCApos.le
          exact mul_le_mul_of_nonneg_left hE6le7 (by positivity)
      _ = (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
            * Work.Spaces.HkSq α 7 w := by ring
      _ ≤ (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
            * (1 + Work.Spaces.HkSq α 7 w) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hb4K : (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
        * (1 + Work.Spaces.HkSq α 7 w) ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
    rw [hK]
    have h1 : 0 ≤ (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 := by positivity
    have h2 : (9 / 4) * CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2
        ≤ CA * (C₄ ^ 2 + C₆ ^ 2) * (max C₀ 0) ^ 2 * (9 / 4) + 1 := by nlinarith
    have h3 : 0 ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith
    exact mul_le_mul_of_nonneg_right h2 h3
  exact ⟨hb3.trans hb3K, hb4.trans hb4K⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.angBlk4_VfsA_mass =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux (AngBlk4 AngBlk4_eq_angMaj_add AngBlk4_nonneg)
open Work.FTS.StrongPersist.L3Rhs (VfsA1 VfsA2 VfsGc VfsJetMaj VfsJetMajMass angMaj
  angMaj_VfsA1_le angMaj_VfsA2_le measurable_VfsGc measurable_VfsJetMaj measurable_angMaj
  measurable_dthU_iter sin_two_pos_Ioo)
open Work.FTS.StrongPersist.H6Pair6Aux.T5bAux (c2mJets)

/-! ## Elementary exponent arithmetic

`Γ(θ)² sin(2θ)^{-γ(α)} ≤ sin(2θ)^{-(1-17α/30)}`: the exponent `1 - 17α/30` is exactly what is
left of `2α/3 - γ(α)` after the `Γ(θ)² ≤ sin(2θ)^{2α/3}` of `Coercivity.Gam_sq_le_sin_two`
is spent. -/

private lemma gam_sq_mul_rpow_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
  have hsp : 0 < Real.sin (2 * θ) := sin_two_pos_Ioo hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := hsp.le
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hG := Work.Coercivity.Gam_sq_le_sin_two α hα θ hθI
  have hexp : 2 * α / 3 + -(Work.Spaces.gam α) = -(1 - 17 * α / 30) := by
    rw [Work.Spaces.gam]; ring
  calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right hG (Real.rpow_nonneg hs0 _)
    _ = (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
        rw [← Real.rpow_add hsp (2 * α / 3) (-(Work.Spaces.gam α)), hexp]

/-! ## The jets of `Γ/c`

Every `dthU`-jet of `Γ/c` of order at most four is dominated by `10⁶·Γ`: the angular jet bound
`|dthU^m Γ| ≤ 10⁵·Γ` (`LocData6.DthIter_Gam_abs_le6`, via `LocData.DthIter_rad_eq`) and
`1/c ≤ 10` (`Spaces.c_bounds`). -/

private lemma gamGc_jet {m : ℕ} (hm : m ≤ 4) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[m] (VfsGc α) θ| ≤ 10 ^ 6 * Work.Spaces.Gam α θ := by
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hfe : VfsGc α = fun θ' : ℝ => (1 / Work.Spaces.c α) * Work.Spaces.Gam α θ' := by
    funext θ'
    rw [VfsGc]
    ring
  rw [hfe, Work.Spaces.dthU_iter_const_mul]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Work.Spaces.c α)]
  have hjet : |Work.Spaces.dthU^[m] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
    have hkey := Work.FTS.LocData6.DthIter_Gam_abs_le6 m (by omega) α hα hα1 hθ
    rwa [Work.FTS.LocData.DthIter_rad_eq m (fun t : ℝ => Work.Spaces.Gam α t) 0 θ] at hkey
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hinv : 1 / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hcpos]
    linarith
  calc (1 / Work.Spaces.c α)
        * |Work.Spaces.dthU^[m] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ (1 / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_left hjet (by positivity)
    _ ≤ 10 * (100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = 10 ^ 6 * Work.Spaces.Gam α θ := by ring

/-! ## Measurability -/

private lemma measurable_VfsA1' (α : ℝ) : Measurable (VfsA1 α) := by
  have hX : Measurable (VfsGc α) := measurable_VfsGc α
  show Measurable (fun θ : ℝ => (3 / 2) * Work.Spaces.dthU (VfsGc α) θ)
  exact measurable_const.mul (measurable_dthU_iter _ hX 1)

private lemma measurable_VfsA2' (α : ℝ) : Measurable (VfsA2 α) := by
  have hX : Measurable (VfsGc α) := measurable_VfsGc α
  have hc2 : Measurable Work.Construction.c2m := by
    rw [show Work.Construction.c2m
        = fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2 from
      funext (fun θ => Work.Construction.c2m_eq θ)]
    fun_prop
  show Measurable (fun θ : ℝ => -α * Work.Construction.c2m θ * VfsGc α θ)
  exact (measurable_const.mul hc2).mul hX

private lemma measurable_AngBlk4' (α : ℝ) {C : ℝ → ℝ} (hC : Measurable C) :
    Measurable (AngBlk4 α C) := by
  have h1 : Measurable (fun θ : ℝ => angMaj α C θ) := measurable_angMaj α C hC
  have h2 : Measurable (fun θ : ℝ =>
      (Work.Spaces.dthU^[4] C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    ((measurable_dthU_iter C hC 4).pow_const 2).mul (by fun_prop)
  rw [funext (fun θ => AngBlk4_eq_angMaj_add α C θ)]
  exact h1.add h2

/-! ## From the open quadrant to `Iθ` a.e. -/

private lemma angBlk4_ae_le {α : ℝ} {C M : ℝ → ℝ} (hC : Measurable C) (hM : Measurable M)
    (hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), AngBlk4 α C θ ≤ M θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), AngBlk4 α C θ ≤ M θ := by
  have hAmeas : MeasurableSet {θ : ℝ | ¬ (AngBlk4 α C θ ≤ M θ)} := by
    have heq : {θ : ℝ | ¬ (AngBlk4 α C θ ≤ M θ)}
        = {θ : ℝ | M θ < AngBlk4 α C θ} := by
      ext θ
      exact not_le
    rw [heq]
    exact measurableSet_lt hM (measurable_AngBlk4' α hC)
  rw [MeasureTheory.ae_iff, MeasureTheory.Measure.restrict_apply hAmeas]
  refine MeasureTheory.measure_mono_null ?_
    (((Set.finite_singleton (Real.pi / 2)).insert (0 : ℝ)).measure_zero volume)
  intro θ hθ
  rw [Set.mem_inter_iff] at hθ
  obtain ⟨hneg, hIθ⟩ := hθ
  by_contra hcon
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
  push Not at hcon
  exact hneg (hpt θ ⟨lt_of_le_of_ne hIθ.1 (Ne.symm hcon.1),
    lt_of_le_of_ne hIθ.2 hcon.2⟩)

/-! ## Integrability and the integral bound from a pointwise majorant -/

private lemma angBlk4_integral_le {α : ℝ} {C X : ℝ → ℝ} (hC : Measurable C) (hX : Measurable X)
    (hXint : Integrable X (volume.restrict Work.Spaces.Iθ))
    (hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), AngBlk4 α C θ ≤ X θ) :
    Integrable (AngBlk4 α C) (volume.restrict Work.Spaces.Iθ) ∧
      (∫ θ in Work.Spaces.Iθ, AngBlk4 α C θ) ≤ ∫ θ in Work.Spaces.Iθ, X θ := by
  have hae := angBlk4_ae_le hC hX hpt
  have hInt : Integrable (AngBlk4 α C) (volume.restrict Work.Spaces.Iθ) := by
    refine hXint.mono' (measurable_AngBlk4' α hC).aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc, hae] with θ hθ hle
    rw [Real.norm_of_nonneg (AngBlk4_nonneg (α := α) (C := C) hθ)]
    exact hle
  exact ⟨hInt, MeasureTheory.integral_mono_ae hInt hXint hae⟩

/-! ## The `VfsA1` half -/

private lemma massA1 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hslot : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.dthU^[4] (VfsA1 α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))) :
    MeasureTheory.IntegrableOn (AngBlk4 α (VfsA1 α)) Work.Spaces.Iθ ∧
      α * (∫ θ in Work.Spaces.Iθ, AngBlk4 α (VfsA1 α) θ) ≤ 10 ^ 17 := by
  obtain ⟨hVJMint, hVJMbd⟩ := VfsJetMajMass α hα hα1
  have hq0 : 0 < 1 - 17 * α / 30 := by linarith
  have hq1 : 1 - 17 * α / 30 < 1 := by linarith
  have hQ := Work.Coercivity.integral_sin_two_neg_rpow_le (1 - 17 * α / 30) hq0 hq1
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), AngBlk4 α (VfsA1 α) θ
      ≤ 9 * VfsJetMaj α θ + 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
    intro θ hθ
    have h1 := angMaj_VfsA1_le (α := α) hθ hα.le
    have h2 := hslot θ hθ
    rw [AngBlk4_eq_angMaj_add]
    linarith
  have hXmeas : Measurable (fun θ : ℝ => 9 * VfsJetMaj α θ
      + 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))) :=
    (measurable_VfsJetMaj α).const_mul 9 |>.add (by fun_prop)
  have hXint : Integrable (fun θ : ℝ => 9 * VfsJetMaj α θ
      + 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
      (volume.restrict Work.Spaces.Iθ) :=
    (hVJMint.const_mul 9).add (hQ.1.const_mul (2250000000000 : ℝ))
  obtain ⟨hInt, hIle⟩ := angBlk4_integral_le (measurable_VfsA1' α) hXmeas hXint hpt
  refine ⟨hInt, ?_⟩
  have hb : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
      ≤ 120 / (17 * α) := by
    have h := (vfs4_maj_integral (A := 0) (Bm := 1) (α := α)
      (by norm_num) (by norm_num) hα hα1).2
    simpa using h
  have hval : (∫ θ in Work.Spaces.Iθ, (9 * VfsJetMaj α θ
        + 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))))
      ≤ 9 * 10 ^ 16 + 2250000000000 * (120 / (17 * α)) := by
    rw [MeasureTheory.integral_add (hVJMint.const_mul 9) (hQ.1.const_mul (2250000000000 : ℝ)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have h1 : (9 : ℝ) * (∫ θ in Work.Spaces.Iθ, VfsJetMaj α θ) ≤ 9 * 10 ^ 16 :=
      mul_le_mul_of_nonneg_left hVJMbd (by norm_num)
    have h2 : (2250000000000 : ℝ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
        ≤ 2250000000000 * (120 / (17 * α)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    linarith
  have hmid : α * (∫ θ in Work.Spaces.Iθ, AngBlk4 α (VfsA1 α) θ)
      ≤ α * (9 * 10 ^ 16 + 2250000000000 * (120 / (17 * α))) :=
    mul_le_mul_of_nonneg_left (le_trans hIle hval) hα.le
  have hkey : α * (2250000000000 * (120 / (17 * α))) = 2250000000000 * (120 / 17) := by
    have hαne : α ≠ 0 := ne_of_gt hα
    field_simp
  have hfin : α * (9 * 10 ^ 16 + 2250000000000 * (120 / (17 * α))) ≤ 10 ^ 17 := by
    have hA : α * (9 * 10 ^ 16) ≤ 9 * 10 ^ 16 := by
      have h0 : (0 : ℝ) ≤ 9 * 10 ^ 16 := by norm_num
      exact mul_le_of_le_one_left h0 hα1
    have hB : (2250000000000 : ℝ) * (120 / 17) ≤ 10 ^ 16 := by norm_num
    rw [mul_add, hkey]
    linarith
  exact le_trans hmid hfin

/-! ## The `VfsA2` half -/

private lemma massA2 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {B Cj : ℝ} (hB : 0 < B)
    (hCj : 0 < Cj)
    (hc2 : ∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ B)
    (hjet : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.dthU^[i] (VfsA2 α) θ|
        ≤ Cj * B * α
          * (|VfsGc α θ| + ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ|))
    (hΓ : ∀ m ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (VfsGc α) θ| ≤ 10 ^ 6 * Work.Spaces.Gam α θ) :
    MeasureTheory.IntegrableOn (AngBlk4 α (VfsA2 α)) Work.Spaces.Iθ ∧
      α * (∫ θ in Work.Spaces.Iθ, AngBlk4 α (VfsA2 α) θ)
        ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16
          + (Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17) := by
  obtain ⟨hVJMint, hVJMbd⟩ := VfsJetMajMass α hα hα1
  have hq0 : 0 < 1 - 17 * α / 30 := by linarith
  have hq1 : 1 - 17 * α / 30 < 1 := by linarith
  have hQ := Work.Coercivity.integral_sin_two_neg_rpow_le (1 - 17 * α / 30) hq0 hq1
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), AngBlk4 α (VfsA2 α) θ
      ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * VfsJetMaj α θ
        + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsp : 0 < Real.sin (2 * θ) := sin_two_pos_Ioo hθ
    have h1 := angMaj_VfsA2_le (α := α) hθ hα hα1 hB hCj
      (fun j hj => hc2 j hj θ hθI)
      (fun i hi1 hi3 => hjet i hi1 (by omega) θ hθ)
    have h2 : (Work.Spaces.dthU^[4] (VfsA2 α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
      have hinner : |VfsGc α θ|
          + ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ|
          ≤ 5 * 10 ^ 6 * Work.Spaces.Gam α θ := by
        have h0 : |VfsGc α θ| ≤ 10 ^ 6 * Work.Spaces.Gam α θ := by
          simpa only [Function.iterate_zero, id_eq] using hΓ 0 (by norm_num) θ hθI
        have hs : ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ|
            ≤ 4 * (10 ^ 6 * Work.Spaces.Gam α θ) := by
          refine le_trans (Finset.sum_le_sum
            (fun m hm => hΓ m (Finset.mem_Icc.mp hm).2 θ hθI)) ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          norm_num
        linarith
      have hj4 := hjet 4 (by norm_num) (le_refl 4) θ hθ
      have h4 : |Work.Spaces.dthU^[4] (VfsA2 α) θ|
          ≤ Cj * B * α * (5 * 10 ^ 6 * Work.Spaces.Gam α θ) :=
        le_trans hj4 (mul_le_mul_of_nonneg_left hinner (by positivity))
      calc (Work.Spaces.dthU^[4] (VfsA2 α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          = |Work.Spaces.dthU^[4] (VfsA2 α) θ| ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by rw [sq_abs]
        _ ≤ (Cj * B * α * (5 * 10 ^ 6 * Work.Spaces.Gam α θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h4 2)
              (Real.rpow_nonneg hsp.le _)
        _ = (Cj * B * α * 5000000) ^ 2
            * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
            ring
        _ ≤ (Cj * B * α * 5000000) ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) :=
            mul_le_mul_of_nonneg_left (gam_sq_mul_rpow_le hα hθ) (sq_nonneg _)
        _ = (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by ring
    rw [AngBlk4_eq_angMaj_add]
    linarith
  have hXmeas : Measurable (fun θ : ℝ => 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * VfsJetMaj α θ
      + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
          * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))) :=
    (measurable_VfsJetMaj α).const_mul _ |>.add (by fun_prop)
  have hXint : Integrable (fun θ : ℝ => 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * VfsJetMaj α θ
      + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
          * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
      (volume.restrict Work.Spaces.Iθ) :=
    (hVJMint.const_mul _).add (hQ.1.const_mul _)
  obtain ⟨hInt, hIle⟩ := angBlk4_integral_le (measurable_VfsA2' α) hXmeas hXint hpt
  refine ⟨hInt, ?_⟩
  have hb : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
      ≤ 120 / (17 * α) := by
    have h := (vfs4_maj_integral (A := 0) (Bm := 1) (α := α)
      (by norm_num) (by norm_num) hα hα1).2
    simpa using h
  have hval : (∫ θ in Work.Spaces.Iθ, (100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * VfsJetMaj α θ
        + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))))
      ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16
        + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / (17 * α)) := by
    rw [MeasureTheory.integral_add (hVJMint.const_mul _) (hQ.1.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have h1 : 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * (∫ θ in Work.Spaces.Iθ, VfsJetMaj α θ)
        ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16 :=
      mul_le_mul_of_nonneg_left hVJMbd (by positivity)
    have h2 : (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
        ≤ (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / (17 * α)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    linarith
  have hkey : α * ((Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / (17 * α)))
      = (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / 17) := by
    have hαne : α ≠ 0 := ne_of_gt hα
    field_simp
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
  have hA : α * (100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16)
      ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16 := by
    have h0 : (0 : ℝ) ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16 := by positivity
    exact mul_le_of_le_one_left h0 hα1
  have hBc : (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / 17)
      ≤ (Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17) := by
    have h0 : (0 : ℝ) ≤ (Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17) := by positivity
    calc (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / 17)
        = ((Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17)) * α ^ 2 := by ring
      _ ≤ ((Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17)) * 1 :=
          mul_le_mul_of_nonneg_left hα2 h0
      _ = (Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17) := by ring
  calc α * (∫ θ in Work.Spaces.Iθ, AngBlk4 α (VfsA2 α) θ)
      ≤ α * (100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16
          + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / (17 * α))) :=
        mul_le_mul_of_nonneg_left (le_trans hIle hval) hα.le
    _ = α * (100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16)
          + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / 17) := by rw [mul_add, hkey]
    _ ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16
          + (Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17) := add_le_add hA hBc

/-! ## The main theorem -/

-- `α`-uniform angular masses of the two angular profiles `VfsA1 α θ = (3/2)·dthU(Γ/c) θ`
-- and `VfsA2 α θ = -α·c2m θ·Γ(θ)/c(α)` of the separated star part `Vfs α`
-- (`Work.FTS.StrongPersist.L3Rhs.VfsA1`, `VfsA2`), for the level-four angular block
-- `AngBlk4 α C θ = (C θ)² sin(2θ)^{-η} + Σ_{1 ≤ i ≤ 4} (dthU^i C θ)² sin(2θ)^{-γ(α)}`
-- of `...blocks/N0Aux/B4SepDefs.lean`.
-- The integrals are `O(1/α)`, stated as `α · ∫ ≤ K` with an `α`-independent constant.
-- Route (crude is fine: the `α^{-1}` loss is later absorbed by `HkSq α 4 w ≤ C₀²α⁴`):
-- `LocData.DthIter_rad_eq` identifies `DthIter m (fun _ θ' => φ θ') z θ` with `dthU^[m] φ θ`;
-- `LocData6.DthIter_Gam_abs_le6` gives `|dthU^m Γ| ≤ 10^5·Γ` for `m ≤ 6`, `Gam_bounds` gives
-- `Γ ≤ 1` and `Coercivity.Gam_sq_le_sin_two` gives `Γ² ≤ sin(2θ)^{2α/3}`; with `c_bounds`
-- (`1/10 ≤ c ≤ 10`) and `Coercivity.integral_sin_two_neg_rpow_le` for the exponent
-- `q = 1 - 17α/30 ∈ (0,1)` (`∫_Iθ sin(2θ)^{-q} ≤ 4/(1-q) = 120/(17α)`) the `γ`-slots of
-- `VfsA1` are `≤ (10^5/c)²·Γ²·sin^{-γ} = (10^5/c)²·sin^{-q}`, and the `η`-slot is `≤ 10^6`
-- (`∫_Iθ sin(2θ)^{-η} ≤ 10^4`).  For `VfsA2` expand `dthU^i(c2m·Γ/c)` by Leibniz and use
-- `c2mJets` (`|DthIter r c2m| ≤ C·sin 2θ ≤ C` for `r ≤ 8`), so every jet term carries a factor
-- `α²` and is bounded by `α²·C·sin^{-q}`.
theorem angBlk4_VfsA_mass : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    MeasureTheory.IntegrableOn
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α
          (Work.FTS.StrongPersist.L3Rhs.VfsA1 α)) Work.Spaces.Iθ ∧
    α * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α
          (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ) ≤ K ∧
    MeasureTheory.IntegrableOn
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α
          (Work.FTS.StrongPersist.L3Rhs.VfsA2 α)) Work.Spaces.Iθ ∧
    α * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α
          (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ) ≤ K := by
  obtain ⟨C2c, hC2cpos, -, hC2cabs, hC2cjet⟩ := c2mJets
  obtain ⟨Cj, hCjpos, hCj⟩ := vfs4_VfsA2_jet
  refine ⟨10 ^ 22 * (C2c ^ 2 + Cj ^ 2 * C2c ^ 2 + 1), by positivity, ?_⟩
  intro α hαIoc
  obtain ⟨hα, hα1⟩ := hαIoc
  -- the `c2m` jet bound in the form required by the `VfsA2` machinery
  have hc2 : ∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ C2c := by
    intro j hj θ hθ
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      simpa using hC2cabs θ hθ
    · have hkey := hC2cjet j hpos (by omega) 0 θ hθ
      rw [Work.FTS.LocData.DthIter_rad_eq j Work.Construction.c2m 0 θ] at hkey
      refine le_trans hkey ?_
      have hs : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      nlinarith [hC2cpos]
  have hΓ : ∀ m ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (VfsGc α) θ| ≤ 10 ^ 6 * Work.Spaces.Gam α θ :=
    fun m hm θ hθ => gamGc_jet hm hα hα1 hθ
  have hjet : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.dthU^[i] (VfsA2 α) θ|
        ≤ Cj * C2c * α
          * (|VfsGc α θ| + ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ|) :=
    fun i hi1 hi4 θ hθ => hCj C2c hC2cpos hc2 α hα hα1 i hi1 hi4 θ hθ
  obtain ⟨hA1int, hA1bd⟩ := massA1 hα hα1 (vfs4_A1_slot4 α hα hα1)
  obtain ⟨hA2int, hA2bd⟩ := massA2 (B := C2c) (Cj := Cj) hα hα1 hC2cpos hCjpos hc2 hjet hΓ
  have hK1 : (10 : ℝ) ^ 17 ≤ 10 ^ 22 * (C2c ^ 2 + Cj ^ 2 * C2c ^ 2 + 1) := by
    nlinarith [sq_nonneg C2c, sq_nonneg Cj, mul_nonneg (sq_nonneg Cj) (sq_nonneg C2c)]
  have hK2 : 100 * (C2c ^ 2 + Cj ^ 2 * C2c ^ 2) * 10 ^ 16
        + (Cj * 5000000) ^ 2 * C2c ^ 2 * (120 / 17)
      ≤ 10 ^ 22 * (C2c ^ 2 + Cj ^ 2 * C2c ^ 2 + 1) := by
    have hXY : Cj ^ 2 * C2c ^ 2 ≤ C2c ^ 2 + Cj ^ 2 * C2c ^ 2 := by
      linarith [sq_nonneg C2c]
    have hY0 : (0 : ℝ) ≤ Cj ^ 2 * C2c ^ 2 := by positivity
    have hexp : (Cj * 5000000) ^ 2 * C2c ^ 2 * (120 / 17)
        = (25000000000000 * (120 / 17)) * (Cj ^ 2 * C2c ^ 2) := by ring
    rw [hexp]
    nlinarith [hXY, hY0, sq_nonneg C2c, sq_nonneg Cj]
  exact ⟨hA1int, le_trans hA1bd hK1, hA2int, le_trans hA2bd hK2⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.RadPer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## The per-order slots

The two lemmas below are the pointwise, per-order versions of `N0Aux.zslot6_split` and
`N0Aux.mslot6_split`: instead of pricing the order-`b` jet of `X` by one of two global constants,
the `b`-th summand of the Leibniz expansion is priced by `B b` and by the `ℋ^{6-b}`-integrand
of `f`. -/

/-- A single pure `D_z`-slot at level `6`, with the jet of `X` at order `b` priced by `B b`. -/
theorem zslot6_per {α : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {B : ℕ → ℝ} {z θ : ℝ}
    (hB : ∀ b : ℕ, 0 ≤ B b)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi (0 : ℝ)))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hjet : ∀ b : ℕ, b ≤ 6 → (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b)
    (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 200704 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
  have hlei := Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf i 0
    (by omega) z θ hz hθ0 hθ1
  have hmm : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      = Work.Spaces.mixed i 0 (fun z θ => X z * f z θ) z θ := rfl
  have hsum : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1),
          (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) := by
    rw [hmm, hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Work.Spaces.mixed_zero_right]
      ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (i + 1),
      ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    intro b hbmem
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 :=
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.choose_sq_le_4096 i b hbi hi
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b := hjet b (by omega)
    have hG : (Work.Spaces.DzIter (i - b) f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α (6 - b) f z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α (6 - b) f z θ (i - b) (by omega)
    calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          ring
      _ ≤ 4096 * B b * Work.Spaces.HkIntegrand α (6 - b) f z θ := by
          have hc : (0 : ℝ) ≤ 4096 * B b := mul_nonneg (by norm_num) (hB b)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
      _ = 4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : i + 1 ≤ 7)
  have hsum2 : (∑ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
      ≤ 4096 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    calc (∑ b ∈ Finset.range (i + 1),
          ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
        ≤ ∑ b ∈ Finset.range (i + 1),
            (4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
          Finset.sum_le_sum hper
      _ = 4096 * (∑ b ∈ Finset.range (i + 1),
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
          rw [Finset.mul_sum]
      _ ≤ 4096 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega)) ?_
          intro b _ _
          exact mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ)
  refine hcs.trans ?_
  calc (((Finset.range (i + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 7 * (4096 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ ≤ 200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
        have hnn : 0 ≤ ∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ :=
          Finset.sum_nonneg fun b _ =>
            mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ)
        nlinarith [hnn]

/-- A single mixed slot at level `6`, with the jet of `X` at order `b` priced by `B b`. -/
theorem mslot6_per {α : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {B : ℕ → ℝ} {z θ : ℝ}
    (hB : ∀ b : ℕ, 0 ≤ B b)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi (0 : ℝ)))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hjet : ∀ b : ℕ, b ≤ 6 → (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 200704 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
  have hj6 : j ≤ 6 := by omega
  have hlei := Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf j i hj6 z θ
    hz hθ0 hθ1
  have hsum : Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1),
          (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) := by
    rw [hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (j + 1),
      ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    intro b hbmem
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 :=
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.choose_sq_le_4096 j b hbj hj6
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b := hjet b (by omega)
    have hG : (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α (6 - b) f z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α (6 - b) f z θ i (j - b) hi (by omega)
    calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
        = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          ring
      _ ≤ 4096 * B b * Work.Spaces.HkIntegrand α (6 - b) f z θ := by
          have hc : (0 : ℝ) ≤ 4096 * B b := mul_nonneg (by norm_num) (hB b)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
      _ = 4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
    (f := fun b => (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))))
  have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : j + 1 ≤ 7)
  have hsum2 : (∑ b ∈ Finset.range (j + 1),
        ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
      ≤ 4096 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    calc (∑ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
        ≤ ∑ b ∈ Finset.range (j + 1),
            (4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
          Finset.sum_le_sum hper
      _ = 4096 * (∑ b ∈ Finset.range (j + 1),
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
          rw [Finset.mul_sum]
      _ ≤ 4096 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega)) ?_
          intro b _ _
          exact mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ)
  refine hcs.trans ?_
  calc (((Finset.range (j + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (j + 1),
              ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 7 * (4096 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ ≤ 200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
        have hnn : 0 ≤ ∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ :=
          Finset.sum_nonneg fun b _ =>
            mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ)
        nlinarith [hnn]

/-! ## The pointwise majorant of the whole integrand -/

/-- The universal constant of the per-order radial engine (the value of `MajC` for the
per-order family, with room to spare over the exact `200704 * 56`). -/
def RadPerC : ℝ := 20000000

theorem RadPerC_pos : 0 < RadPerC := by norm_num [RadPerC]

/-- **The per-order pointwise majorant**: the `ℋ⁶`-integrand of `X · f` is bounded by the
per-order family `Σ_{b≤6} B b · HkIntegrand α (6-b) f`. -/
theorem maj_pt_per {α : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {B : ℕ → ℝ} {z θ : ℝ}
    (hB : ∀ b : ℕ, 0 ≤ B b)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi (0 : ℝ)))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hjet : ∀ b : ℕ, b ≤ 6 → (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b) :
    Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ
      ≤ RadPerC * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
  have hSnn : 0 ≤ ∑ b ∈ Finset.range 7,
      B b * Work.Spaces.HkIntegrand α (6 - b) f z θ :=
    Finset.sum_nonneg fun b _ =>
      mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ)
  have hBase : 0 ≤ 200704 * (∑ b ∈ Finset.range 7,
      B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) :=
    mul_nonneg (by norm_num) hSnn
  have hZ : (∑ i ∈ Finset.range (6 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 7 * (200704 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
    calc (∑ i ∈ Finset.range (6 + 1),
          (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (6 + 1),
            (200704 * (∑ b ∈ Finset.range 7,
              B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
          Finset.sum_le_sum fun i hi =>
            zslot6_per hB hX hf hz hθ0 hθ1 hjet i
              (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 7 * (200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have hM : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0))
      ≤ 49 * (200704 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
    calc (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ ∑ _i ∈ Finset.range (6 + 1), ∑ _j ∈ Finset.range (6 + 1),
            (200704 * (∑ b ∈ Finset.range 7,
              B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 6
          · rw [ite_eq_left hc]
            exact mslot6_per hB hX hf hz hθ0 hθ1 hjet i j hc.1 hc.2
          · rw [ite_eq_right hc]
            exact hBase
      _ = 49 * (200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
          ring
  rw [Work.Spaces.HkIntegrand]
  calc (∑ i ∈ Finset.range (6 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      + ∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
      ≤ 7 * (200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
        + 49 * (200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := add_le_add hZ hM
    _ ≤ RadPerC * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
        have hM' : 200704 * 56 ≤ RadPerC := by norm_num [RadPerC]
        calc 7 * (200704 * (∑ b ∈ Finset.range 7,
                B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
              + 49 * (200704 * (∑ b ∈ Finset.range 7,
                B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
            = (200704 * 56) * (∑ b ∈ Finset.range 7,
                B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by ring
          _ ≤ RadPerC * (∑ b ∈ Finset.range 7,
                B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) :=
              mul_le_mul_of_nonneg_right hM' hSnn

/-! ## The engine -/

/-- **The per-order radial-product engine at level `6`** (namespace `Work.FTS.StrongEps.E4R3.Nblock6`).

For a *radial* factor `X : ℝ → ℝ` (only `C⁶` on `(0,∞)` is assumed — `SmoothOpen` of the lift
is FALSE for angular moments such as `FK w`) and a `SmoothOpen` datum `f` which is
`ℋ⁶`-honest, with per-order pointwise jet bounds `(D_z^b X z)² ≤ B b` (`b ≤ 6`, a.e. in `z`),

  `HkSq α 6 (X·f) ≤ C * Σ_{b≤6} B b * HkSq α (6-b) f`.

This is the per-order refinement of `Apriori4Proofs.N0Aux.radialMaj6_split` (which prices the
orders `b ≤ 4` by a single `Blo` and `b ≥ 5` by a single `Bhi`; that dichotomy is not enough
here, because the radial factor `FK w` at hand has order-`4` jets bounded only by the
`ℋ⁵`-price of `w`).

Recipe: copy `Apriori4Proofs/blocks/N0Aux/Maj6SplitSlots.lean` (`zslot6_split`, `mslot6_split`)
and `Maj6Split.lean` (`maj_pt`, `radialMaj6_split`), replacing the two constants `Blo`/`Bhi`
(used for `b ≤ 4` resp. `b ≥ 5`, priced by `HkIntegrand α 6 f` resp. `HkIntegrand α 2 f`) by the
single family `B : ℕ → ℝ`: the summand indexed by `b` in the Leibniz expansion of a slot `(i,j)`
is priced by `HkIntegrand α (6 - b) f` via `Work.Spaces.sq_le_HkIntegrand_z` (`i - b ≤ 6 - b`)
resp. `Work.Spaces.sq_le_HkIntegrand_mixed` (`1 ≤ i`, `i + (j - b) ≤ 6 - b`), using
`leibniz_radial_mul`, `(i.choose b)² ≤ 4096` for `i ≤ 6` and `sq_sum_le_card_mul_sum_sq`.  Then
integrate over `z ∈ Iz`, `θ ∈ Iθ` using `HkMem_mono_open`, `HkIntegrand_mono` and the a.e. jet
hypothesis (the RHS slices are integrable by `HkMem α (6-b) f`). -/
theorem RadPer : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {B : ℕ → ℝ},
    ContDiffOn ℝ 6 X (Set.Ioi (0 : ℝ)) → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 f → (∀ b : ℕ, 0 ≤ B b) →
    (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), ∀ b : ℕ, b ≤ 6 →
      (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b) →
    Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ C * ∑ b ∈ Finset.range 7, B b * Work.Spaces.HkSq α (6 - b) f := by
  refine ⟨RadPerC + 1, by linarith [RadPerC_pos], ?_⟩
  intro α X f B hX hf hm6 hB hjet
  -- honesty of the lower-order data
  have hm : ∀ b : ℕ, b ≤ 6 → Work.Spaces.HkMem α (6 - b) f := fun b _ =>
    Work.FTS.OpenPkg.HkMem_mono_open hf (6 - b) (Nat.sub_le 6 b) hm6
  -- the majorant slices are integrable
  have hSlice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ =>
      ∑ b ∈ Finset.range 7, B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)
      Work.Spaces.Iθ := by
    intro z hz
    show Integrable (fun θ => ∑ b ∈ Finset.range 7,
      B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) (volume.restrict Work.Spaces.Iθ)
    refine MeasureTheory.integrable_finsetSum (Finset.range 7) (fun b hb => ?_)
    exact ((hm b (by simp only [Finset.mem_range] at hb; omega)).1 z hz).const_mul (B b)
  -- the inner integral of a sum is the sum of the inner integrals
  have hS7eq : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)
        = ∑ b ∈ Finset.range 7, B b * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    intro z hz
    rw [MeasureTheory.integral_finsetSum (Finset.range 7)
      (f := fun b θ => B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)
      (fun b hb => ((hm b (by simp only [Finset.mem_range] at hb; omega)).1 z hz).const_mul (B b))]
    exact Finset.sum_congr rfl fun b _ => MeasureTheory.integral_const_mul (B b) _
  -- the outer integral of the sum is the sum of the outer integrals
  have hT : IntegrableOn (fun z => ∑ b ∈ Finset.range 7,
      B b * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
      Work.Spaces.Iz := by
    show Integrable (fun z => ∑ b ∈ Finset.range 7,
      B b * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
      (volume.restrict Work.Spaces.Iz)
    refine MeasureTheory.integrable_finsetSum (Finset.range 7) (fun b hb => ?_)
    exact ((hm b (by simp only [Finset.mem_range] at hb; omega)).2).const_mul (B b)
  have hinner : (fun z => ∫ θ in Work.Spaces.Iθ, RadPerC * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => RadPerC * (∑ b ∈ Finset.range 7, B b * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (6 - b) f z θ))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (s := Work.Spaces.Iz) measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul, hS7eq z hz]
  have hGint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, RadPerC *
      (∑ b ∈ Finset.range 7, B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
      Work.Spaces.Iz :=
    (hT.const_mul RadPerC).congr hinner.symm
  -- the a.e. jet bounds, together with `z ∈ Iz`
  have hgood : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      z ∈ Work.Spaces.Iz ∧
        (∀ b : ℕ, b ≤ 6 → (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b) :=
    (MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) (s := Work.Spaces.Iz)
      measurableSet_Ici).and hjet
  have hIoo : (volume.restrict Work.Spaces.Iθ)
      = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
      MeasureTheory.Ioo_ae_eq_Icc
    exact Measure.restrict_congr_set haeeq.symm
  -- the pointwise comparison, sliced in `θ`
  have hslice_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, RadPerC * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    filter_upwards [hgood] with z hz
    obtain ⟨hzIz, hzjet⟩ := hz
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      ((hSlice z hzIz).const_mul RadPerC) ?_
    rw [hIoo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hzIz) with hz0 | hzpos
    · rw [← hz0, Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.HkIntegrand_zero]
      exact mul_nonneg RadPerC_pos.le (Finset.sum_nonneg fun b _ =>
        mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f 0 θ))
    · exact maj_pt_per hB hX hf hzpos hθ.1 hθ.2 hzjet
  -- integrate in `z`
  have houter : Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, RadPerC * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    rw [Work.Spaces.HkSq]
    exact MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      hGint hslice_ae
  -- evaluate the majorant integral
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, RadPerC *
      (∑ b ∈ Finset.range 7, B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
      = RadPerC * ∑ b ∈ Finset.range 7, B b * Work.Spaces.HkSq α (6 - b) f := by
    have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, RadPerC *
        (∑ b ∈ Finset.range 7, B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
        = ∫ z in Work.Spaces.Iz, RadPerC * (∑ b ∈ Finset.range 7, B b *
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
      MeasureTheory.integral_congr_ae hinner
    rw [h1, MeasureTheory.integral_const_mul]
    have h2 : (∫ z in Work.Spaces.Iz, (∑ b ∈ Finset.range 7, B b *
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)))
        = ∑ b ∈ Finset.range 7, B b * (∫ z in Work.Spaces.Iz,
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
      rw [MeasureTheory.integral_finsetSum (Finset.range 7)
        (f := fun b z => B b * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α (6 - b) f z θ))
        (fun b hb => ((hm b (by simp only [Finset.mem_range] at hb; omega)).2).const_mul (B b))]
      exact Finset.sum_congr rfl fun b _ => MeasureTheory.integral_const_mul (B b) _
    rw [h2]
    simp only [Work.Spaces.HkSq]
  refine houter.trans_eq hval |>.trans ?_
  have hSq_nn : 0 ≤ ∑ b ∈ Finset.range 7, B b * Work.Spaces.HkSq α (6 - b) f :=
    Finset.sum_nonneg fun b _ => mul_nonneg (hB b) (Work.Spaces.HkSq_nonneg α (6 - b) f)
  exact mul_le_mul_of_nonneg_right (by linarith [RadPerC_pos]) hSq_nn

end Work.FTS.StrongEps.E4R3.Nblock6
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptBoundDth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

def ptdC1 : ℝ := 2401 * 4096 * ptdK2

theorem ptdC1_pos : 0 < ptdC1 := by
  have h := ptdK2_pos
  rw [ptdC1]; positivity

theorem ptdC1_nonneg : 0 ≤ ptdC1 := le_of_lt ptdC1_pos

/-- `(∑_{a∈s} ∑_{b∈t} G a b)² ≤ s.card · t.card · ∑_{a∈s} ∑_{b∈t} (G a b)²`. -/
theorem sq_sum_sq_le {ι : Type*} (s t : Finset ι) (G : ι → ι → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t, G a b) ^ 2
      ≤ (s.card : ℝ) * (t.card : ℝ) * ∑ a ∈ s, ∑ b ∈ t, (G a b) ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq s (fun a => ∑ b ∈ t, G a b)
  have h2 : ∀ a ∈ s, (∑ b ∈ t, G a b) ^ 2 ≤ (t.card : ℝ) * ∑ b ∈ t, (G a b) ^ 2 :=
    fun a _ => sq_sum_le_card_mul_sum_sq t (fun b => G a b)
  have h3 : ∑ a ∈ s, (∑ b ∈ t, G a b) ^ 2
      ≤ (t.card : ℝ) * ∑ a ∈ s, ∑ b ∈ t, (G a b) ^ 2 := by
    calc ∑ a ∈ s, (∑ b ∈ t, G a b) ^ 2
        ≤ ∑ a ∈ s, ((t.card : ℝ) * ∑ b ∈ t, (G a b) ^ 2) := Finset.sum_le_sum h2
      _ = (t.card : ℝ) * ∑ a ∈ s, ∑ b ∈ t, (G a b) ^ 2 := by rw [Finset.mul_sum]
  calc (∑ a ∈ s, ∑ b ∈ t, G a b) ^ 2
      ≤ (s.card : ℝ) * ∑ a ∈ s, (∑ b ∈ t, G a b) ^ 2 := h1
    _ ≤ (s.card : ℝ) * ((t.card : ℝ) * ∑ a ∈ s, ∑ b ∈ t, (G a b) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (s.card : ℝ) * (t.card : ℝ) * ∑ a ∈ s, ∑ b ∈ t, (G a b) ^ 2 := by ring

/-- A single binomial coefficient of the Leibniz rule at level `≤ 6`. -/
theorem choose_le_64 (j b : ℕ) (hj : j ≤ 6) : (j.choose b : ℝ) ≤ 64 := by
  have h1 : j.choose b ≤ 2 ^ j := Nat.choose_le_two_pow j b
  have h3 : (2 : ℕ) ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hj
  have h5 : j.choose b ≤ 64 := le_trans h1 h3
  exact_mod_cast h5

/-- The product of the two binomial coefficients of a mixed Leibniz summand at level `≤ 6`. -/
theorem choose_mul_choose_le_64 (i j a b : ℕ) (hij : i + j ≤ 6) :
    (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 64 := by
  have h1 : i.choose a ≤ 2 ^ i := Nat.choose_le_two_pow i a
  have h2 : j.choose b ≤ 2 ^ j := Nat.choose_le_two_pow j b
  have h3 : (2 : ℕ) ^ (i + j) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hij
  have h4 : (2 : ℕ) ^ i * 2 ^ j ≤ 64 := by
    rw [← Nat.pow_add]; simpa using h3
  have h5 : i.choose a * j.choose b ≤ 64 := le_trans (Nat.mul_le_mul h1 h2) h4
  exact_mod_cast h5

/-- `D_z^k (D_θ f) = D_z^k D_θ^1 f`, definitionally. -/
theorem mixed_one_eq_DzIter_Dth (k : ℕ) (f : ℝ → ℝ → ℝ) :
    mixed k 1 f = DzIter k (Dth f) := rfl

/-! ## The two slot bounds -/

/-- The mixed slots of `HkIntegrand α 6 (A · D_θ f)` are bounded by `ptdC1 · ptdBud`. -/
theorem slotM_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {A f : ℝ → ℝ → ℝ} {MA : ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmA : Work.Spaces.HkMem α 6 A) (hmf : Work.Spaces.HkMem α 6 f)
    (hMA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (mixed j i (fun z θ => A z θ * Dth f z θ) z θ * Wt α z θ) ^ 2
      ≤ ptdC1 * ptdBud α A f MA z θ := by
  have hDth : Work.FTS.EllipticEst.SmoothOpen (Dth f) := hf.Dth
  have hpoint : mixed j i (fun z θ => A z θ * Dth f z θ) z θ * Wt α z θ
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) := by
    rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i A (Dth f) hA hDth z θ hz hθ0 hθ1]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [Work.FTS.StrongEps.H5.mixed_Dth_eq]
    ring
  rw [hpoint]
  have hbud0 : 0 ≤ ptdBud α A f MA z θ := ptdBud_nonneg hα A f MA z θ
  have hK2 : 0 ≤ ptdK2 := le_of_lt ptdK2_pos
  have h4096 : (0:ℝ) ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) :=
    mul_nonneg (by norm_num) (mul_nonneg hK2 hbud0)
  -- the per-summand bound, with the binomial coefficient absorbed
  have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      (((i.choose a : ℝ) * (j.choose b : ℝ))
          * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
        ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) := by
    intro a ha b hb
    have ha' : a ≤ i := by
      have := Finset.mem_range.mp ha; omega
    have hb' : b ≤ j := by
      have := Finset.mem_range.mp hb; omega
    have hbase := PtDthAux.summandM_bound α hα hα1 hA hf hmA hmf hMA hz hθ0 hθ1 hi hij ha' hb'
    have hc := choose_mul_choose_le_64 i j a b hij
    have hc0 : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
    have hc2 : ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2 ≤ 4096 := by nlinarith
    have hsq : (((i.choose a : ℝ) * (j.choose b : ℝ))
          * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
        = ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2
          * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2 := by
      ring
    rw [hsq]
    calc ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2
        ≤ 4096 * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
      _ ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) :=
          mul_le_mul_of_nonneg_left hbase (by norm_num)
  -- the two Cauchy–Schwarz steps
  have hinner : ∀ a ∈ Finset.range (i + 1),
      ∑ b ∈ Finset.range (j + 1),
          (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
        ≤ ((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by
    intro a ha
    have h := Finset.sum_le_card_nsmul (Finset.range (j + 1))
      (fun b => (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2)
      (4096 * (ptdK2 * ptdBud α A f MA z θ)) (fun b hb => hterm a ha b hb)
    simpa [Finset.card_range, nsmul_eq_mul] using h
  have hsum : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
      ≤ ((i : ℝ) + 1) * (((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ))) := by
    have h := Finset.sum_le_card_nsmul (Finset.range (i + 1))
      (fun a => ∑ b ∈ Finset.range (j + 1),
          (((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2)
      (((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ))) (fun a ha => hinner a ha)
    simpa [Finset.card_range, nsmul_eq_mul] using h
  have hCS := sq_sum_sq_le (Finset.range (i + 1)) (Finset.range (j + 1))
    (fun a b => ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ))
  have hCS' : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
      ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
        * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (((i.choose a : ℝ) * (j.choose b : ℝ))
              * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2 := by
    simpa [Finset.card_range] using hCS
  have hi7 : ((i : ℝ) + 1) ≤ 7 := by
    have : (i : ℝ) ≤ 6 := by exact_mod_cast (by omega : i ≤ 6)
    linarith
  have hj7 : ((j : ℝ) + 1) ≤ 7 := by
    have : (j : ℝ) ≤ 6 := by exact_mod_cast (by omega : j ≤ 6)
    linarith
  have hi0 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2
      ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
        * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (((i.choose a : ℝ) * (j.choose b : ℝ))
              * (mixed b a A z θ * mixed (j - b) (i - a + 1) f z θ * Wt α z θ)) ^ 2 := hCS'
    _ ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
        * (((i : ℝ) + 1) * (((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ)))) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hi0 hj0)
    _ = (((i : ℝ) + 1) * ((j : ℝ) + 1) * (((i : ℝ) + 1) * ((j : ℝ) + 1)))
          * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by ring
    _ ≤ 2401 * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by
          have hab : ((i : ℝ) + 1) * ((j : ℝ) + 1) ≤ 49 := by nlinarith
          have hab0 : 0 ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1) := mul_nonneg hi0 hj0
          refine mul_le_mul_of_nonneg_right ?_ h4096
          nlinarith [hab, hab0]
    _ ≤ ptdC1 * ptdBud α A f MA z θ := by
          rw [ptdC1]
          have h1 : (2401:ℝ) * (4096 * (ptdK2 * ptdBud α A f MA z θ))
              = 2401 * 4096 * ptdK2 * ptdBud α A f MA z θ := by ring
          rw [h1]

/-- The pure `D_z`-slots of `HkIntegrand α 6 (A · D_θ f)` are bounded by `ptdC1 · ptdBud`. -/
theorem slotZ_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {A f : ℝ → ℝ → ℝ} {MA : ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hmA : Work.Spaces.HkMem α 6 A) (hmf : Work.Spaces.HkMem α 6 f)
    (hMA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {j : ℕ} (hj : j ≤ 6) :
    (DzIter j (fun z θ => A z θ * Dth f z θ) z θ
        * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
      ≤ ptdC1 * ptdBud α A f MA z θ := by
  have hDth : Work.FTS.EllipticEst.SmoothOpen (Dth f) := hf.Dth
  have hpoint : DzIter j (fun z θ => A z θ * Dth f z θ) z θ
        * (w z / Real.sin (2 * θ) ^ (eta / 2))
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2))) := by
    rw [← Work.Spaces.mixed_zero_right j (fun z θ => A z θ * Dth f z θ)]
    rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j 0 A (Dth f) hA hDth z θ hz hθ0 hθ1]
    rw [show Finset.range (0 + 1) = Finset.range 1 from rfl]
    simp only [Finset.sum_range_one]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, mixed_zero_right]
    rw [← mixed_one_eq_DzIter_Dth]
    ring
  rw [hpoint]
  have hbud0 : 0 ≤ ptdBud α A f MA z θ := ptdBud_nonneg hα A f MA z θ
  have hK2 : 0 ≤ ptdK2 := le_of_lt ptdK2_pos
  have h4096 : (0:ℝ) ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) :=
    mul_nonneg (by norm_num) (mul_nonneg hK2 hbud0)
  have hterm : ∀ b ∈ Finset.range (j + 1),
      ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2
        ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) := by
    intro b hb
    have hb' : b ≤ j := by
      have := Finset.mem_range.mp hb; omega
    have hbase := PtDthAux.summandZ_bound α hα hα1 hA hf hmA hmf hMA hz hθ0 hθ1 hj hb'
    have hc := choose_le_64 j b hj
    have hc0 : 0 ≤ (j.choose b : ℝ) := by positivity
    have hc2 : (j.choose b : ℝ) ^ 2 ≤ 4096 := by nlinarith
    have hsq : ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2
        = (j.choose b : ℝ) ^ 2 * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 := by ring
    rw [hsq]
    calc (j.choose b : ℝ) ^ 2 * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
        ≤ 4096 * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 :=
          mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
      _ ≤ 4096 * (ptdK2 * ptdBud α A f MA z θ) :=
          mul_le_mul_of_nonneg_left hbase (by norm_num)
  have hCS := sq_sum_le_card_mul_sum_sq (Finset.range (j + 1))
    (fun b => (j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2))))
  have hCS' : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (DzIter b A z θ * mixed (j - b) 1 f z θ
            * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2 := by
    simpa [Finset.card_range] using hCS
  have hsum : ∑ b ∈ Finset.range (j + 1),
        ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2
      ≤ ((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by
    have h := Finset.sum_le_card_nsmul (Finset.range (j + 1))
      (fun b => ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2)
      (4096 * (ptdK2 * ptdBud α A f MA z θ)) (fun b hb => hterm b hb)
    simpa [Finset.card_range, nsmul_eq_mul] using h
  have hj7 : ((j : ℝ) + 1) ≤ 7 := by
    have : (j : ℝ) ≤ 6 := by exact_mod_cast (by omega : j ≤ 6)
    linarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  calc (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (DzIter b A z θ * mixed (j - b) 1 f z θ
            * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1),
          ((j.choose b : ℝ) * (DzIter b A z θ * mixed (j - b) 1 f z θ
              * (w z / Real.sin (2 * θ) ^ (eta / 2)))) ^ 2 := hCS'
    _ ≤ ((j : ℝ) + 1) * (((j : ℝ) + 1) * (4096 * (ptdK2 * ptdBud α A f MA z θ))) :=
          mul_le_mul_of_nonneg_left hsum hj0
    _ = (((j : ℝ) + 1) * ((j : ℝ) + 1)) * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by ring
    _ ≤ 49 * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by
          have hab : ((j : ℝ) + 1) * ((j : ℝ) + 1) ≤ 49 := by nlinarith
          have hab0 : 0 ≤ ((j : ℝ) + 1) * ((j : ℝ) + 1) := mul_nonneg hj0 hj0
          refine mul_le_mul_of_nonneg_right ?_ h4096
          nlinarith [hab, hab0]
    _ ≤ ptdC1 * ptdBud α A f MA z θ := by
          rw [ptdC1]
          have h1 : (49:ℝ) * (4096 * (ptdK2 * ptdBud α A f MA z θ))
              ≤ 2401 * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := by
            refine mul_le_mul_of_nonneg_right ?_ h4096
            norm_num
          calc (49:ℝ) * (4096 * (ptdK2 * ptdBud α A f MA z θ))
              ≤ 2401 * (4096 * (ptdK2 * ptdBud α A f MA z θ)) := h1
            _ = 2401 * 4096 * ptdK2 * ptdBud α A f MA z θ := by ring

/-! ## The assembly -/

/-- The two energy-priced budget terms are dominated by the middle part of the target RHS. -/
theorem inv_pair_le_mid {α : ℝ} (hα : 0 < α) {hA6 hf6 X6A X6f : ℝ}
    (hA6n : 0 ≤ hA6) (hf6n : 0 ≤ hf6) (hXAn : 0 ≤ X6A) (hXfn : 0 ≤ X6f) :
    (gam α - 1)⁻¹ * hA6 * X6f + (gam α - 1)⁻¹ * hf6 * X6A
      ≤ (1 + (gam α - 1)⁻¹ * (hA6 + hf6)) * (X6A + X6f) := by
  have hI : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have hS : 0 ≤ X6A + X6f := by linarith
  have hkey : (gam α - 1)⁻¹ * (hA6 + hf6) * (X6A + X6f)
        - ((gam α - 1)⁻¹ * hA6 * X6f + (gam α - 1)⁻¹ * hf6 * X6A)
      = (gam α - 1)⁻¹ * (hA6 * X6A + hf6 * X6f) := by ring
  have hnn : 0 ≤ (gam α - 1)⁻¹ * (hA6 * X6A + hf6 * X6f) :=
    mul_nonneg hI (by linarith [mul_nonneg hA6n hXAn, mul_nonneg hf6n hXfn])
  have hstep : (gam α - 1)⁻¹ * hA6 * X6f + (gam α - 1)⁻¹ * hf6 * X6A
      ≤ (gam α - 1)⁻¹ * (hA6 + hf6) * (X6A + X6f) := by linarith [hkey, hnn]
  have hmono : (gam α - 1)⁻¹ * (hA6 + hf6) * (X6A + X6f)
      ≤ (1 + (gam α - 1)⁻¹ * (hA6 + hf6)) * (X6A + X6f) :=
    mul_le_mul_of_nonneg_right (by linarith) hS
  linarith [hstep, hmono]

theorem ptBoundDth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
          ≤ K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
            + K * (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
            + K * (Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
                * Work.Spaces.Wt α z θ) ^ 2 := by
  have hKpos : 0 < 10 ^ 14 * (CP + 1) + 1 := by
    have := CP_pos; positivity
  refine ⟨10 ^ 14 * (CP + 1) + 1, hKpos, ?_⟩
  intro A f MA hA hf hmA hmf hm7f hMA z θ hz hθ0 hθ1
  set RHS : ℝ := MA ^ 2 * HkIntegrand α 7 f z θ
      + (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
        * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ)
      + (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2 with hRHS
  have hbud0 : 0 ≤ ptdBud α A f MA z θ := ptdBud_nonneg hα A f MA z θ
  -- the budget is dominated by `RHS`
  have hbud_le : ptdBud α A f MA z θ ≤ RHS := by
    have hI : 0 ≤ (gam α - 1)⁻¹ :=
      inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
    have h2 := HkSq_nonneg α 6 A
    have h3 := HkSq_nonneg α 6 f
    have h4 := HkIntegrand_nonneg α 6 A z θ
    have h5 := HkIntegrand_nonneg α 6 f z θ
    have h1 := HkIntegrand_nonneg α 7 f z θ
    have e2 := inv_pair_le_mid (α := α) hα h2 h3 h4 h5
    rw [ptdBud, hRHS]
    linarith [e2]
  -- the level-six integrand is bounded by `56 · ptdC1 · ptdBud`
  have hLHS : HkIntegrand α 6 (fun z θ => A z θ * Dth f z θ) z θ
      ≤ 56 * ptdC1 * ptdBud α A f MA z θ := by
    have hZ : ∑ i ∈ Finset.range 7,
        (DzIter i (fun z θ => A z θ * Dth f z θ) z θ
          * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
        ≤ 7 * (ptdC1 * ptdBud α A f MA z θ) := by
      have h := Finset.sum_le_card_nsmul (Finset.range 7)
        (fun i => (DzIter i (fun z θ => A z θ * Dth f z θ) z θ
          * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2)
        (ptdC1 * ptdBud α A f MA z θ)
        (fun i hi => slotZ_bound α hα hα1 hA hf hmA hmf hMA hz hθ0 hθ1
          (by have := Finset.mem_range.mp hi; omega))
      simpa [Finset.card_range, nsmul_eq_mul] using h
    have hM : ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6
          then (mixed j i (fun z θ => A z θ * Dth f z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ 49 * (ptdC1 * ptdBud α A f MA z θ) := by
      have hinner : ∀ i ∈ Finset.range 7,
          ∑ j ∈ Finset.range 7,
            (if 1 ≤ i ∧ i + j ≤ 6
              then (mixed j i (fun z θ => A z θ * Dth f z θ) z θ * Wt α z θ) ^ 2 else 0)
          ≤ 7 * (ptdC1 * ptdBud α A f MA z θ) := by
        intro i hi
        have h := Finset.sum_le_card_nsmul (Finset.range 7)
          (fun j => (if 1 ≤ i ∧ i + j ≤ 6
              then (mixed j i (fun z θ => A z θ * Dth f z θ) z θ * Wt α z θ) ^ 2 else 0))
          (ptdC1 * ptdBud α A f MA z θ) (fun j hj => by
            by_cases hic : 1 ≤ i ∧ i + j ≤ 6
            · rw [if_pos hic]
              exact slotM_bound α hα hα1 hA hf hmA hmf hMA hz hθ0 hθ1 hic.1 hic.2
            · rw [if_neg hic]
              exact mul_nonneg ptdC1_nonneg hbud0)
        simpa [Finset.card_range, nsmul_eq_mul] using h
      have h := Finset.sum_le_card_nsmul (Finset.range 7) _
        (7 * (ptdC1 * ptdBud α A f MA z θ)) hinner
      have h2 : (7:ℝ) * (7 * (ptdC1 * ptdBud α A f MA z θ))
          = 49 * (ptdC1 * ptdBud α A f MA z θ) := by ring
      simpa [Finset.card_range, nsmul_eq_mul, h2] using h
    rw [HkIntegrand]
    calc _ ≤ 7 * (ptdC1 * ptdBud α A f MA z θ) + 49 * (ptdC1 * ptdBud α A f MA z θ) :=
          add_le_add hZ hM
      _ = 56 * ptdC1 * ptdBud α A f MA z θ := by ring
  have h56 : 56 * ptdC1 ≤ 10 ^ 14 * (CP + 1) + 1 := by
    have h1 := CP_pos
    rw [ptdC1, ptdK2]
    nlinarith
  calc HkIntegrand α 6 (fun z θ => A z θ * Dth f z θ) z θ
      ≤ 56 * ptdC1 * ptdBud α A f MA z θ := hLHS
    _ ≤ (10 ^ 14 * (CP + 1) + 1) * ptdBud α A f MA z θ :=
        mul_le_mul_of_nonneg_right h56 hbud0
    _ ≤ (10 ^ 14 * (CP + 1) + 1) * RHS :=
        mul_le_mul_of_nonneg_left hbud_le hKpos.le
    _ = (10 ^ 14 * (CP + 1) + 1) * MA ^ 2 * HkIntegrand α 7 f z θ
          + (10 ^ 14 * (CP + 1) + 1) * (1 + (gam α - 1)⁻¹ * (HkSq α 6 A + HkSq α 6 f))
            * (HkIntegrand α 6 A z θ + HkIntegrand α 6 f z θ)
          + (10 ^ 14 * (CP + 1) + 1) * (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2 := by
        rw [hRHS]; ring


end Work.FTS.StrongEps.E4R3.Nblock6.Tools
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.auxiliary.SlotSum_Fstar_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace Work.FTS.StrongEps.E4R3.Nblock6.aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## §1 The iterated operator `D_z = z ∂_z` on `z`-only profiles -/

/-- `DzdIter` is linear over multiplication by a constant.  (`deriv` of a constant multiple is
the constant multiple of the `deriv` also at the points where the function is not
differentiable, `Work.Spaces.deriv_const_mul'`.) -/
theorem DzdIter_const_mul (c : ℝ) (u : ℝ → ℝ) (k : ℕ) :
    Work.Elliptic.DzdIter k (fun z => c * u z) = fun z => c * Work.Elliptic.DzdIter k u z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext z
      show z * deriv (fun z' => Work.Elliptic.DzdIter k (fun z => c * u z) z') z
        = c * (z * deriv (fun z' => Work.Elliptic.DzdIter k u z') z)
      rw [ih, Work.Spaces.deriv_const_mul']
      ring

/-- If `r` is `C^n` on `(0,∞)` for every `n`, then so is every iterate `DzdIter b r`. -/
theorem contDiffOn_DzdIter (r : ℝ → ℝ) (hr : ∀ n : ℕ, ContDiffOn ℝ (n : ℕ∞ω) r (Set.Ioi 0)) :
    ∀ b (n : ℕ), ContDiffOn ℝ (n : ℕ∞ω) (Work.Elliptic.DzdIter b r) (Set.Ioi 0) := by
  intro b
  induction b with
  | zero => intro n; exact hr n
  | succ b ih =>
      intro n
      have hder : ContDiffOn ℝ (n : ℕ∞ω) (deriv (Work.Elliptic.DzdIter b r)) (Set.Ioi 0) :=
        (ih (n + 1)).deriv_of_isOpen isOpen_Ioi (m := (n : ℕ∞ω))
          (n := ((n + 1 : ℕ) : ℕ∞ω)) le_rfl
      have hid : ContDiffOn ℝ (n : ℕ∞ω) (fun z : ℝ => z) (Set.Ioi 0) := contDiffOn_id
      exact hid.mul hder

/-- `F_* = 2z/(1+z)²` is `C^n` on `(0,∞)` for every `n` (rational, with denominator `(1+z)²`
nonvanishing there). -/
theorem contDiffOn_Fstar (n : ℕ) : ContDiffOn ℝ (n : ℕ∞ω) Work.FM.Fstar (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ (n : ℕ∞ω) (fun z : ℝ => 2 * z) (Set.Ioi 0) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ (n : ℕ∞ω) (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have hz0 : 0 < z := hz
    exact pow_ne_zero 2 (by linarith : (1 : ℝ) + z ≠ 0)
  exact hnum.div hden hne

/-- The iterates of `F_*` up to order five are differentiable on `(0,∞)` (this is what the
Leibniz rule `DzdIter_mul_of_diff` at order six needs). -/
theorem differentiableOn_DzdIter_Fstar (b : ℕ) (hb : b ≤ 5) :
    DifferentiableOn ℝ (Work.Elliptic.DzdIter b Work.FM.Fstar) (Set.Ioi 0) :=
  (contDiffOn_DzdIter Work.FM.Fstar contDiffOn_Fstar b 1).differentiableOn (by norm_num)

/-! ## §2 The Leibniz bound for the jets of `F_*²` -/

/-- **The Leibniz bound.**  If the jets of `F_*` are dominated by `K · F_*` up to order six,
then the jets of `F_*²` are dominated by `448 · K² · F_*²`.

(`448 = 7 · 2⁶`: the Leibniz sum has `q + 1 ≤ 7` terms, each with binomial coefficient
`q.choose b ≤ 2^q ≤ 2⁶`, and each of the two factors costs one `K F_*`.) -/
theorem DzdIter_Fstar_mul_Fstar_le {K : ℝ} (hKpos : 0 < K)
    (hK : ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b Work.FM.Fstar z| ≤ K * Work.FM.Fstar z) :
    ∀ q ≤ 6, ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter q (fun z => Work.FM.Fstar z * Work.FM.Fstar z) z|
        ≤ 448 * K ^ 2 * (Work.FM.Fstar z) ^ 2 := by
  intro q hq z hz
  have hz0 : 0 < z := hz
  have hFnn : 0 ≤ Work.FM.Fstar z := by
    rw [Work.FM.Fstar]; positivity
  have hexp := Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff q Work.FM.Fstar Work.FM.Fstar
    (fun b _ => differentiableOn_DzdIter_Fstar b (by omega))
    (fun b _ => differentiableOn_DzdIter_Fstar b (by omega))
    z (Set.mem_Ioi.mpr hz0)
  rw [hexp]
  have hterm : ∀ b ∈ Finset.range (q + 1),
      |(q.choose b : ℝ) * (Work.Elliptic.DzdIter b Work.FM.Fstar z
        * Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z)|
        ≤ 64 * (K ^ 2 * (Work.FM.Fstar z) ^ 2) := by
    intro b hb
    have hbq : b ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have h1 : |Work.Elliptic.DzdIter b Work.FM.Fstar z| ≤ K * Work.FM.Fstar z :=
      hK b (by omega) z hz0
    have h2 : |Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z| ≤ K * Work.FM.Fstar z :=
      hK (q - b) (by omega) z hz0
    have hch : (q.choose b : ℝ) ≤ 64 := by
      have h1 : q.choose b ≤ 2 ^ q := Nat.choose_le_two_pow q b
      have h2 : (2 : ℕ) ^ q ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hq
      have h3 : q.choose b ≤ 64 := by omega
      exact_mod_cast h3
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (q.choose b))]
    have hprod : |Work.Elliptic.DzdIter b Work.FM.Fstar z|
          * |Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z|
        ≤ K ^ 2 * (Work.FM.Fstar z) ^ 2 := by
      have hmul := mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (le_of_lt hKpos) hFnn)
      calc |Work.Elliptic.DzdIter b Work.FM.Fstar z|
              * |Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z|
          ≤ (K * Work.FM.Fstar z) * (K * Work.FM.Fstar z) := hmul
        _ = K ^ 2 * (Work.FM.Fstar z) ^ 2 := by ring
    exact mul_le_mul hch hprod (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
  calc |∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
          * (Work.Elliptic.DzdIter b Work.FM.Fstar z
            * Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z)|
      ≤ ∑ b ∈ Finset.range (q + 1), |(q.choose b : ℝ)
          * (Work.Elliptic.DzdIter b Work.FM.Fstar z
            * Work.Elliptic.DzdIter (q - b) Work.FM.Fstar z)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b ∈ Finset.range (q + 1), (64 * (K ^ 2 * (Work.FM.Fstar z) ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = ((q + 1 : ℕ) : ℝ) * (64 * (K ^ 2 * (Work.FM.Fstar z) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 7 * (64 * (K ^ 2 * (Work.FM.Fstar z) ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast (by omega : q + 1 ≤ 7)
    _ = 448 * K ^ 2 * (Work.FM.Fstar z) ^ 2 := by ring

/-! ## §3 The exact radial weight identity and the `z`-integral -/

/-- `F_*⁴ · w² = 16/(1+z)⁴`: with `F_* z = 2z/(1+z)²` and `w z = (1+z)²/z²` the `z`-powers
cancel exactly. -/
theorem Fstar_pow_four_mul_w_sq (z : ℝ) (hz : 0 < z) :
    (Work.FM.Fstar z) ^ 4 * (Work.Spaces.w z) ^ 2 = 16 * (1 + z) ^ (-4 : ℝ) := by
  have hrw : (1 + z) ^ (-4 : ℝ) = 1 / (1 + z) ^ 4 := by
    rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 + z),
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  rw [Work.FM.Fstar, Work.Spaces.w, hrw]
  field_simp
  ring_nf

/-- `(1+z)^{-4}` is integrable on `(0,∞)` (it is `(z+1)^a` with `a = -4 < -1`). -/
theorem integrableOn_one_add_rpow_neg_four :
    IntegrableOn (fun z : ℝ => (1 + z) ^ (-4 : ℝ)) (Set.Ioi 0) := by
  have h := integrableOn_add_rpow_Ioi_of_lt (a := (-4 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ))
    (by norm_num) (by norm_num)
  simpa [add_comm] using h

/-- `∫_0^∞ (1+z)^{-4} dz = 1/3`, by the fundamental theorem with the antiderivative
`-(1/3)(1+z)^{-3} → 0` at `+∞`. -/
theorem integral_one_add_rpow_neg_four :
    (∫ z in Set.Ioi (0 : ℝ), (1 + z) ^ (-4 : ℝ)) = 1 / 3 := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => (-(1 / 3)) * (1 + t) ^ (-3 : ℝ)) ((1 + x) ^ (-4 : ℝ)) x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    have h1 : (1 : ℝ) + x ≠ 0 := by linarith
    have h2 : HasDerivAt (fun t : ℝ => (1 : ℝ) + t) 1 x := Work.FM.hasDerivAt_add_const 1 x
    have h3 := (h2.rpow_const (p := (-3 : ℝ)) (Or.inl h1)).const_mul (-(1 / 3))
    have h4 : (1 * (-3 : ℝ) * (1 + x) ^ ((-3 : ℝ) - 1)) = ((-3 : ℝ)) * (1 + x) ^ (-4 : ℝ) := by
      rw [show (-3 : ℝ) - 1 = -4 by norm_num]; ring
    have h5 : -(1 / 3) * (((-3 : ℝ)) * (1 + x) ^ (-4 : ℝ)) = (1 + x) ^ (-4 : ℝ) := by ring
    rw [h4, h5] at h3
    exact h3
  have htend : Tendsto (fun t : ℝ => (-(1 / 3)) * (1 + t) ^ (-3 : ℝ)) atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => (1 + t)) atTop atTop := by
      simpa [add_comm] using Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
    have h2 : Tendsto (fun t : ℝ => (1 + t) ^ (-3 : ℝ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp h
    have h3 := h2.const_mul (-(1 / 3))
    rw [mul_zero] at h3
    exact h3
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    integrableOn_one_add_rpow_neg_four htend
  simpa using hmain

/-! ## §4 The main theorem -/

/-- **The radial slot sum of `α² F_*²` is `O(K⁴ α⁴)`.**

The `z`-integral of the slot sum of the profile `z ↦ α² F_*(z)²` is bounded by `C K⁴ α⁴`
whenever `K` dominates the jets of `F_* = 2z/(1+z)²` up to order six; `C = 10⁷` is universal.
The exponent `4` is exactly the square of the two `K`'s of the two-factor Leibniz expansion of
`D_z^q (F_*²)`; the `α⁴` is `(α²)²`. -/
theorem SlotSum_Fstar_sq_le : ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 0 < K →
    (∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter b Work.FM.Fstar z| ≤ K * Work.FM.Fstar z) →
    ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2)) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) ≤ C * K ^ 4 * α ^ 4 := by
  refine ⟨10000000, by norm_num, ?_⟩
  intro K hKpos hK α hα
  have hα0 : 0 < α := hα.1
  -- the unfolding of `SlotSum` into the `DzdIter`-sum
  have hEq : Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2)
      = fun z => ∑ q ∈ Finset.range 7,
          (Work.Elliptic.DzdIter q (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by
    funext z
    rw [Work.FTS.StrongPersist.SlotSum]
    exact Finset.sum_congr rfl fun q _ => by rw [Work.Elliptic.DzIter_rad]
  -- the pointwise bound on the slots
  have hslot : ∀ z : ℝ, 0 < z → ∀ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ α ^ 4 * K ^ 4 * (3211264 * (1 + z) ^ (-4 : ℝ)) := by
    intro z hz0 q hq
    have hq6 : q ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
    have hlin : Work.Elliptic.DzdIter q (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z
        = α ^ 2 * Work.Elliptic.DzdIter q
            (fun z => Work.FM.Fstar z * Work.FM.Fstar z) z := by
      have h1 : (fun z' : ℝ => α ^ 2 * (Work.FM.Fstar z') ^ 2)
          = fun z' => α ^ 2 * (Work.FM.Fstar z' * Work.FM.Fstar z') := by
        funext z'; ring
      rw [h1,
        congrFun (DzdIter_const_mul (α ^ 2)
          (fun z' => Work.FM.Fstar z' * Work.FM.Fstar z') q) z]
    rw [hlin]
    have hb := DzdIter_Fstar_mul_Fstar_le hKpos hK q hq6 z hz0
    have hXs : (Work.Elliptic.DzdIter q (fun z => Work.FM.Fstar z * Work.FM.Fstar z) z) ^ 2
        ≤ (448 * K ^ 2 * (Work.FM.Fstar z) ^ 2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    calc (α ^ 2 * Work.Elliptic.DzdIter q (fun z => Work.FM.Fstar z * Work.FM.Fstar z) z) ^ 2
            * (Work.Spaces.w z) ^ 2
        = α ^ 4 * (Work.Elliptic.DzdIter q (fun z => Work.FM.Fstar z * Work.FM.Fstar z) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by ring
      _ ≤ α ^ 4 * (448 * K ^ 2 * (Work.FM.Fstar z) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXs (by positivity))
            (by positivity)
      _ = α ^ 4 * K ^ 4 * (200704 * ((Work.FM.Fstar z) ^ 4 * (Work.Spaces.w z) ^ 2)) := by ring
      _ = α ^ 4 * K ^ 4 * (3211264 * (1 + z) ^ (-4 : ℝ)) := by
          rw [Fstar_pow_four_mul_w_sq z hz0]; ring
  have hpt : ∀ z : ℝ, 0 < z →
      Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z
        ≤ α ^ 4 * K ^ 4 * (22478848 * (1 + z) ^ (-4 : ℝ)) := by
    intro z hz0
    rw [hEq]
    calc ∑ q ∈ Finset.range 7,
          (Work.Elliptic.DzdIter q (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) ^ 2
            * (Work.Spaces.w z) ^ 2
        ≤ ∑ _q ∈ Finset.range 7, α ^ 4 * K ^ 4 * (3211264 * (1 + z) ^ (-4 : ℝ)) :=
          Finset.sum_le_sum (hslot z hz0)
      _ = 7 * (α ^ 4 * K ^ 4 * (3211264 * (1 + z) ^ (-4 : ℝ))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      _ = α ^ 4 * K ^ 4 * (22478848 * (1 + z) ^ (-4 : ℝ)) := by ring
  -- measurability of the slot sum
  have hBsm : ∀ n : ℕ, ContDiffOn ℝ (n : ℕ∞ω)
      (fun z : ℝ => α ^ 2 * (Work.FM.Fstar z) ^ 2) (Set.Ioi 0) :=
    fun n => contDiffOn_const.mul ((contDiffOn_Fstar n).pow 2)
  have hcont_q : ∀ q : ℕ, ContinuousOn
      (fun z : ℝ => (Work.Elliptic.DzdIter q (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) ^ 2)
      (Set.Ioi 0) :=
    fun q => (contDiffOn_DzdIter _ hBsm q 1).continuousOn.pow 2
  have hcont_w : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have hnum : ContinuousOn (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
      (continuousOn_const.add continuousOn_id).pow 2
    have hden : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Ioi 0) := continuousOn_id.pow 2
    have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
      convert hnum.div hden (fun z hz => by
        have hz0 : 0 < z := hz
        exact pow_ne_zero 2 (ne_of_gt hz0)) using 1
      funext z
      rw [Work.Spaces.w, Pi.div_apply]
    exact hw.pow 2
  have hmeas : AEStronglyMeasurable
      (Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2))
      (volume.restrict (Set.Ioi 0)) := by
    rw [hEq]
    exact (continuousOn_finsetSum (Finset.range 7)
      (fun q _ => (hcont_q q).mul hcont_w)).aestronglyMeasurable measurableSet_Ioi
  -- the dominator
  have hdom_int : IntegrableOn
      (fun z : ℝ => α ^ 4 * K ^ 4 * (22478848 * (1 + z) ^ (-4 : ℝ))) (Set.Ioi 0) :=
    MeasureTheory.Integrable.const_mul
      (MeasureTheory.Integrable.const_mul integrableOn_one_add_rpow_neg_four 22478848)
      (α ^ 4 * K ^ 4)
  have hint_ioi : IntegrableOn
      (Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2))
      (Set.Ioi 0) := by
    refine hdom_int.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.FTS.StrongPersist.SlotSum_nonneg _ z)]
    exact hpt z hz
  -- transfer from `(0,∞)` to `[0,∞) = Iz`
  have hmes_eq : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict (Set.Ici (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  have hint : IntegrableOn
      (Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2))
      Work.Spaces.Iz := by
    show Integrable (Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2))
      (volume.restrict (Set.Ici (0 : ℝ)))
    rw [← hmes_eq]
    exact hint_ioi
  refine ⟨hint, ?_⟩
  have hIntEq : (∫ z in Work.Spaces.Iz,
        Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z)
      = ∫ z in Set.Ioi (0 : ℝ),
        Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z := by
    show (∫ z in Set.Ici (0 : ℝ),
        Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z) = _
    exact MeasureTheory.integral_Ici_eq_integral_Ioi
  rw [hIntEq]
  have hae : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z
        ≤ α ^ 4 * K ^ 4 * (22478848 * (1 + z) ^ (-4 : ℝ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact hpt z hz
  calc ∫ z in Set.Ioi (0 : ℝ),
        Work.FTS.StrongPersist.SlotSum (fun z => α ^ 2 * (Work.FM.Fstar z) ^ 2) z
      ≤ ∫ z in Set.Ioi (0 : ℝ), α ^ 4 * K ^ 4 * (22478848 * (1 + z) ^ (-4 : ℝ)) :=
        MeasureTheory.integral_mono_ae hint_ioi hdom_int hae
    _ = α ^ 4 * K ^ 4 * (22478848 * (∫ z in Set.Ioi (0 : ℝ), (1 + z) ^ (-4 : ℝ))) := by
        simp only [MeasureTheory.integral_const_mul]
    _ = α ^ 4 * K ^ 4 * (22478848 * (1 / 3)) := by rw [integral_one_add_rpow_neg_four]
    _ ≤ α ^ 4 * K ^ 4 * 10000000 :=
        mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    _ = 10000000 * K ^ 4 * α ^ 4 := by ring

end Work.FTS.StrongEps.E4R3.Nblock6.aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.L12_Jeps_slice_tendsto_of_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux3

set_option autoImplicit false

/-- **`hl12` from the vanishing of the unmollified zero mode.**  For a sequence of profiles `X k`
which are `SmoothOpen` with honest `ℋ⁵`-membership and a common `ℋ⁵`-bound `B`, and whose
`L₁₂`-zero mode vanishes, the zero modes of the mollified profiles `J_{ε k} X k` tend to `0`
along any sequence `ε k ∈ (0,1]` with `ε k → 0`. -/
theorem L12_Jeps_slice_tendsto_of_zero {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℕ → ℝ}
    {X : ℕ → Work.FTS.Galerkin.Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : ∀ k : ℕ, ε k ∈ Set.Ioc 0 1)
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ k : ℕ, Work.FTS.EllipticEst.SmoothOpen (X k))
    (hmem : ∀ k : ℕ, Work.Spaces.HkMem α 5 (X k))
    (hB : ∀ k : ℕ, Work.Spaces.HkNorm α 5 (X k) ≤ B)
    (h0 : ∀ k : ℕ, Work.Construction.L12 (X k) 0 = 0) :
    Filter.Tendsto (fun k : ℕ =>
        Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (ε k) (X k)) 0)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.L12_Jeps_sub_le ρ hρ
  have hmain : ∀ k : ℕ,
      |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (ε k) (X k)) 0| ≤ (C * B) * ε k := by
    intro k
    have h := hC α hα (X k) (hsm k) (hmem k) (ε k) (hε k)
    rw [h0 k, sub_zero] at h
    calc |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (ε k) (X k)) 0|
        ≤ C * ε k * Work.Spaces.HkNorm α 5 (X k) := h
      _ ≤ C * ε k * B :=
          mul_le_mul_of_nonneg_left (hB k) (le_of_lt (mul_pos hCpos (hε k).1))
      _ = (C * B) * ε k := by ring
  have habs : Filter.Tendsto
      (fun k : ℕ => |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (ε k) (X k)) 0|)
      Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall hmain) (by simpa using hε0.const_mul (C * B))
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr (by simpa [Function.comp_def] using habs)

end Work.FTS.StrongEps.E5Aux3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5L12Datum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`EpsDatum` forces the vanishing zero mode.**  If the datum `g₀` is a regular datum of the
scheme at every small `ε` (`EpsDatum α ρ ε g₀`, whose class-`C` clause gives
`L₁₂ (J_ε g₀) 0 = 0`), then `L₁₂ g₀ 0 = 0` — the missing conjunct of `EpsUniformMem`. -/
theorem l12_zero_of_epsDatum {α : ℝ} {ρ : ℝ × ℝ → ℝ} {g₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hd : ∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀) :
    Work.Construction.L12 g₀ 0 = 0 := by
  obtain ⟨C, hCpos, hC⟩ := L12_Jeps_sub_le ρ hρ
  have hsm : Work.FTS.EllipticEst.SmoothOpen g₀ := (hd 1 one_pos).1
  have hmem6 : Work.Spaces.HkMem α 6 g₀ := (hd 1 one_pos).2.1
  have hmem5 : Work.Spaces.HkMem α 5 g₀ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 5 (by norm_num) hmem6
  -- the bound `|L₁₂ g₀ 0| ≤ C ε ‖g₀‖_{ℋ⁵}` for every `ε ∈ Ioc 0 1`
  have hbound : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      |Work.Construction.L12 g₀ 0| ≤ C * ε * Work.Spaces.HkNorm α 5 g₀ := by
    intro ε hε
    have hcl : Work.FTS.ClassC.ClassC α (Jeps ρ ε g₀) := (hd ε hε.1).2.2
    have h0 : Work.Construction.L12 (Jeps ρ ε g₀) 0 = 0 := hcl.l12
    have h := hC α hα g₀ hsm hmem5 ε hε
    rw [h0, zero_sub, abs_neg] at h
    exact h
  -- an explicit small `ε` gives the contradiction unless the value is zero
  by_contra hne
  have hpos : 0 < |Work.Construction.L12 g₀ 0| := by
    refine lt_of_le_of_ne (abs_nonneg _) fun h => hne (abs_eq_zero.mp h.symm)
  set N : ℝ := Work.Spaces.HkNorm α 5 g₀ with hN
  have hNnn : 0 ≤ N := Work.Spaces.HkNorm_nonneg α 5 g₀
  set ε : ℝ := min 1 (|Work.Construction.L12 g₀ 0| / (2 * (C * N + 1))) with hεdef
  have hεpos : 0 < ε := lt_min one_pos (div_pos hpos (by positivity))
  have hεle : ε ≤ 1 := min_le_left _ _
  have hlt : C * ε * N < |Work.Construction.L12 g₀ 0| := by
    have hε2 : ε ≤ |Work.Construction.L12 g₀ 0| / (2 * (C * N + 1)) := min_le_right _ _
    have hCN : 0 ≤ C * N := mul_nonneg hCpos.le hNnn
    have hstep : C * ε * N ≤ C * (|Work.Construction.L12 g₀ 0| / (2 * (C * N + 1))) * N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε2 hCpos.le) hNnn
    refine lt_of_le_of_lt hstep ?_
    have hden : (2 : ℝ) * (C * N + 1) ≠ 0 := by positivity
    have hEq : C * (|Work.Construction.L12 g₀ 0| / (2 * (C * N + 1))) * N
        = |Work.Construction.L12 g₀ 0| * (C * N / (2 * (C * N + 1))) := by
      field_simp
    rw [hEq]
    have hfrac : C * N / (2 * (C * N + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    simpa using mul_lt_mul_of_pos_left hfrac hpos
  exact absurd (hbound ε ⟨hεpos, hεle⟩) (not_le.mpr hlt)

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsCorrTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.PiecesAClassC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.GalFields.RHS (P1 P2 P3 P4 P5 TOf kA1 kA2 kA3 kA4 kA5)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The `ℋ⁴`-honesty, size and smoothness of the pieces `P₁` -- `P₅` of the `N₀`-difference.

`hprod`/`hwprod` are the two product rules of the `ℋ⁴`-calculus (`prod_field`,
`wprod_field_winf`) at the (single) constant `Ci` dominating all the package constants. -/
theorem PiecesAClassC {α Ci : ℝ} {g g' h : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hCi : 0 < Ci)
    (hprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    (hwprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g)
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hg'sm : Work.FTS.EllipticEst.SmoothOpen g')
    (hhsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hg'mem : Work.Spaces.HkMem α 4 g')
    (hhmem : Work.Spaces.HkMem α 4 h)
    (hLgSm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z))
    (hLhSm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 h z))
    (hLgMem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z))
    (hLhMem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 h z))
    (hLgXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
      ≤ Ci * Work.FTS.Nonlin.Xn α g)
    (hLhXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
      ≤ Ci * Work.FTS.GalFields.Xn5 α h)
    (hXg5 : Work.FTS.Nonlin.Xn α g ≤ Work.FTS.GalFields.Xn5 α g)
    (hXh5 : Work.FTS.Nonlin.Xn α h ≤ Work.FTS.GalFields.Xn5 α h)
    (hXg'5 : Work.FTS.Nonlin.Xn α g' ≤ Work.FTS.GalFields.Xn5 α g')
    (hDthhSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth h))
    (hDthhMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth h))
    (hDthhXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h) ≤ Work.FTS.GalFields.Xn5 α h)
    (hDthg'Sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g'))
    (hDthg'Mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g'))
    (hDthg'Xn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth g') ≤ Work.FTS.GalFields.Xn5 α g')
    (CF : ℝ) (hCF : 0 < CF)
    (hDthFstarSm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)))
    (hFstarW : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ CF * α ^ 2)
    (hZh0 : 0 ≤ Work.FTS.GalFields.Xn5 α h) :
    (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P1 α g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P1 α g h)
          ≤ Work.FTS.GalFields.RHS.kA1 α Ci * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P2 α g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P2 α g' h)
          ≤ Work.FTS.GalFields.RHS.kA2 α Ci * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P3 α h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P3 α h)
          ≤ Work.FTS.GalFields.RHS.kA3 α Ci CF * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P4 α g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P4 α g h)
          ≤ Work.FTS.GalFields.RHS.kA4 α Ci * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P5 α g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P5 α g' h)
          ≤ Work.FTS.GalFields.RHS.kA5 α Ci * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P1 α g h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P2 α g' h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P3 α h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P4 α g h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P5 α g' h) := by
  have h0g : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have h0g' : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  -- ## the five pieces: smoothness, honesty, size
  have hs1 : Work.FTS.EllipticEst.SmoothOpen (P1 α g h) := by
    unfold P1
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / α)
      (Work.FTS.NonlinRows.smoothOpen_mul hLgSm hhsm)
  have h1 : Work.Spaces.HkMem α 4 (P1 α g h) ∧
      Work.FTS.Nonlin.Xn α (P1 α g h) ≤ kA1 α Ci * TOf α g g' h := by
    have hp := hprod (fun z θ => Work.Construction.L12 g z) h
      ⟨hLgSm, hLgMem⟩ ⟨hhsm, hhmem⟩
    refine ⟨?_, ?_⟩
    · unfold P1
      exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α) hp.1
    · unfold P1
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / α)]
      have hstep : (1 / α) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.L12 g z * h z θ)
          ≤ kA1 α Ci * (Work.FTS.Nonlin.Xn α g * Work.FTS.GalFields.Xn5 α h) := by
        rw [kA1]
        calc (1 / α) * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z * h z θ)
            ≤ (1 / α) * (Ci * α ^ (-(1 / 2 : ℝ))
                * (Ci * Work.FTS.Nonlin.Xn α g) * Work.FTS.GalFields.Xn5 α h) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
              refine le_trans hp.2 ?_
              calc Ci * α ^ (-(1 / 2 : ℝ))
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
                    * Work.FTS.Nonlin.Xn α h
                  ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
                    * Work.FTS.Nonlin.Xn α h :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hLgXn hA0) (le_refl _)
                      (Work.Spaces.HkNorm_nonneg α 4 h)
                      (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi)
                        (Work.Spaces.HkNorm_nonneg α 4 g)))
                _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
                    * Work.FTS.GalFields.Xn5 α h :=
                    mul_le_mul_of_nonneg_left hXh5
                      (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi)
                        (Work.Spaces.HkNorm_nonneg α 4 g)))
            _ = (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci
                * (Work.FTS.Nonlin.Xn α g * Work.FTS.GalFields.Xn5 α h) := by ring
      refine le_trans hstep ?_
      rw [TOf]
      refine mul_le_mul_of_nonneg_left ?_
        (le_of_lt (show (0 : ℝ) < kA1 α Ci by rw [kA1]; positivity))
      have h1' : Work.FTS.Nonlin.Xn α g ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h1' hZh0]
  have hs2 : Work.FTS.EllipticEst.SmoothOpen (P2 α g' h) := by
    unfold P2
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / α)
      (Work.FTS.NonlinRows.smoothOpen_mul hLhSm hg'sm)
  have h2 : Work.Spaces.HkMem α 4 (P2 α g' h) ∧
      Work.FTS.Nonlin.Xn α (P2 α g' h) ≤ kA2 α Ci * TOf α g g' h := by
    have hp := hprod (fun z θ => Work.Construction.L12 h z) g'
      ⟨hLhSm, hLhMem⟩ ⟨hg'sm, hg'mem⟩
    refine ⟨?_, ?_⟩
    · unfold P2
      exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α) hp.1
    · unfold P2
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / α)]
      have hstep : (1 / α) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.L12 h z * g' z θ)
          ≤ kA2 α Ci * (Work.FTS.GalFields.Xn5 α h * Work.FTS.GalFields.Xn5 α g') := by
        rw [kA2]
        calc (1 / α) * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z * g' z θ)
            ≤ (1 / α) * (Ci * α ^ (-(1 / 2 : ℝ))
                * (Ci * Work.FTS.GalFields.Xn5 α h) * Work.FTS.GalFields.Xn5 α g') := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
              refine le_trans hp.2 ?_
              calc Ci * α ^ (-(1 / 2 : ℝ))
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
                    * Work.FTS.Nonlin.Xn α g'
                  ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
                    * Work.FTS.Nonlin.Xn α g' :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hLhXn hA0) (le_refl _)
                      (Work.Spaces.HkNorm_nonneg α 4 g') (mul_nonneg hA0 (by positivity))
                _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
                    * Work.FTS.GalFields.Xn5 α g' :=
                    mul_le_mul_of_nonneg_left hXg'5 (mul_nonneg hA0 (by positivity))
            _ = (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci
                * (Work.FTS.GalFields.Xn5 α h * Work.FTS.GalFields.Xn5 α g') := by ring
      refine le_trans hstep ?_
      rw [TOf]
      refine mul_le_mul_of_nonneg_left ?_
        (le_of_lt (show (0 : ℝ) < kA2 α Ci by rw [kA2]; positivity))
      have h1' : Work.FTS.GalFields.Xn5 α g' ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h1' hZh0]
  have hs3 : Work.FTS.EllipticEst.SmoothOpen (P3 α h) := by
    unfold P3
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hDthFstarSm hLhSm)
  have h3 : Work.Spaces.HkMem α 4 (P3 α h) ∧
      Work.FTS.Nonlin.Xn α (P3 α h) ≤ kA3 α Ci CF * TOf α g g' h := by
    have hw := hwprod (Work.Spaces.Dth (Work.Construction.Fstar α))
      (fun z θ => Work.Construction.L12 h z) hDthFstarSm (hFstarW).1
      ⟨hLhSm, hLhMem⟩
    refine ⟨?_, ?_⟩
    · unfold P3
      exact Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hw.1
    · unfold P3
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / (2 * α))]
      have hstep : (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
              * Work.Construction.L12 h z)
          ≤ kA3 α Ci CF * Work.FTS.GalFields.Xn5 α h := by
        rw [kA3]
        calc (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
              (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
                * Work.Construction.L12 h z)
            ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
                * (Ci * Work.FTS.GalFields.Xn5 α h)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
              refine le_trans hw.2 ?_
              calc Ci * α ^ (-(1 / 2 : ℝ))
                    * Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
                  ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z) :=
                    mul_le_mul (mul_le_mul_of_nonneg_left (hFstarW).2 hA0) (le_refl _)
                      (Work.Spaces.HkNorm_nonneg α 4 (fun z θ => Work.Construction.L12 h z))
                      (mul_nonneg hA0 (by positivity))
                _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
                    * (Ci * Work.FTS.GalFields.Xn5 α h) :=
                    mul_le_mul_of_nonneg_left hLhXn (mul_nonneg hA0 (by positivity))
            _ = (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci)
                * Work.FTS.GalFields.Xn5 α h := by ring
      refine le_trans hstep ?_
      rw [TOf]
      refine mul_le_mul_of_nonneg_left ?_
        (le_of_lt (show (0 : ℝ) < kA3 α Ci CF by rw [kA3]; positivity))
      have h1' : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      simpa using mul_le_mul_of_nonneg_right h1' hZh0
  have hs4 : Work.FTS.EllipticEst.SmoothOpen (P4 α g h) := by
    unfold P4
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hLgSm hDthhSm)
  have h4 : Work.Spaces.HkMem α 4 (P4 α g h) ∧
      Work.FTS.Nonlin.Xn α (P4 α g h) ≤ kA4 α Ci * TOf α g g' h := by
    have hp := hprod (fun z θ => Work.Construction.L12 g z) (Work.Spaces.Dth h)
      ⟨hLgSm, hLgMem⟩ ⟨hDthhSm, hDthhMem⟩
    refine ⟨?_, ?_⟩
    · unfold P4
      exact Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hp.1
    · unfold P4
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / (2 * α))]
      have hstep : (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.L12 g z * Work.Spaces.Dth h z θ)
          ≤ kA4 α Ci * (Work.FTS.Nonlin.Xn α g * Work.FTS.GalFields.Xn5 α h) := by
        rw [kA4]
        calc (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
              (fun z θ => Work.Construction.L12 g z * Work.Spaces.Dth h z θ)
            ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ))
                * (Ci * Work.FTS.Nonlin.Xn α g) * Work.FTS.GalFields.Xn5 α h) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
              refine le_trans hp.2 ?_
              calc Ci * α ^ (-(1 / 2 : ℝ))
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
                    * Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h)
                  ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
                    * Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h) :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hLgXn hA0) (le_refl _)
                      (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dth h))
                      (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi)
                        (Work.Spaces.HkNorm_nonneg α 4 g)))
                _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
                    * Work.FTS.GalFields.Xn5 α h :=
                    mul_le_mul_of_nonneg_left hDthhXn
                      (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi)
                        (Work.Spaces.HkNorm_nonneg α 4 g)))
            _ = (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)
                * (Work.FTS.Nonlin.Xn α g * Work.FTS.GalFields.Xn5 α h) := by ring
      refine le_trans hstep ?_
      rw [TOf]
      refine mul_le_mul_of_nonneg_left ?_
        (le_of_lt (show (0 : ℝ) < kA4 α Ci by rw [kA4]; positivity))
      have h1' : Work.FTS.Nonlin.Xn α g ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h1' hZh0]
  have hs5 : Work.FTS.EllipticEst.SmoothOpen (P5 α g' h) := by
    unfold P5
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hLhSm hDthg'Sm)
  have h5 : Work.Spaces.HkMem α 4 (P5 α g' h) ∧
      Work.FTS.Nonlin.Xn α (P5 α g' h) ≤ kA5 α Ci * TOf α g g' h := by
    have hp := hprod (fun z θ => Work.Construction.L12 h z) (Work.Spaces.Dth g')
      ⟨hLhSm, hLhMem⟩ ⟨hDthg'Sm, hDthg'Mem⟩
    refine ⟨?_, ?_⟩
    · unfold P5
      exact Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hp.1
    · unfold P5
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / (2 * α))]
      have hstep : (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.L12 h z * Work.Spaces.Dth g' z θ)
          ≤ kA5 α Ci * (Work.FTS.GalFields.Xn5 α h * Work.FTS.GalFields.Xn5 α g') := by
        rw [kA5]
        calc (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
              (fun z θ => Work.Construction.L12 h z * Work.Spaces.Dth g' z θ)
            ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ))
                * (Ci * Work.FTS.GalFields.Xn5 α h) * Work.FTS.GalFields.Xn5 α g') := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
              refine le_trans hp.2 ?_
              calc Ci * α ^ (-(1 / 2 : ℝ))
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
                    * Work.FTS.Nonlin.Xn α (Work.Spaces.Dth g')
                  ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
                    * Work.FTS.Nonlin.Xn α (Work.Spaces.Dth g') :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hLhXn hA0) (le_refl _)
                      (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dth g'))
                      (mul_nonneg hA0 (by positivity))
                _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
                    * Work.FTS.GalFields.Xn5 α g' :=
                    mul_le_mul_of_nonneg_left hDthg'Xn (mul_nonneg hA0 (by positivity))
            _ = (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)
                * (Work.FTS.GalFields.Xn5 α h * Work.FTS.GalFields.Xn5 α g') := by ring
      refine le_trans hstep ?_
      rw [TOf]
      refine mul_le_mul_of_nonneg_left ?_
        (le_of_lt (show (0 : ℝ) < kA5 α Ci by rw [kA5]; positivity))
      have h1' : Work.FTS.GalFields.Xn5 α g' ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h1' hZh0]
  exact ⟨h1, h2, h3, h4, h5, hs1, hs2, hs3, hs4, hs5⟩

end

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.PiecesBClassCRow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.GalFields.RHS (P6 P7 P8 P9 TOf kA6 kA7 kA8 kA9)

namespace Work.FTS.StrongEps.EpsRLX

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The `ℋ⁴`-honesty, size and smoothness of the pieces `P₆` -- `P₉` of the `N₀`-difference.

`hprod`/`hwprod` are the two product rules of the `ℋ⁴`-calculus at the single constant `Ci`;
the `c2m`-multiplication is priced by the fixed constant `Cangdef` (`c2m_mul_HkSq_le`). -/
theorem PiecesBClassCRow {α Ci : ℝ} {g g' h : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hCi : 0 < Ci)
    (hprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    (hwprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g)
    (hLgSm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z))
    (hLhSm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 h z))
    (hLgMem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z))
    (hLhMem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 h z))
    (hLgXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
      ≤ Ci * Work.FTS.Nonlin.Xn α g)
    (hLhXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
      ≤ Ci * Work.FTS.GalFields.Xn5 α h)
    (hXg5 : Work.FTS.Nonlin.Xn α g ≤ Work.FTS.GalFields.Xn5 α g)
    (hXg'5 : Work.FTS.Nonlin.Xn α g' ≤ Work.FTS.GalFields.Xn5 α g')
    (hDzhSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz h))
    (hDzhMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz h))
    (hDzhXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h) ≤ Work.FTS.GalFields.Xn5 α h)
    (hDz'hSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g'))
    (hDz'hMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g'))
    (hDz'hXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz g') ≤ Work.FTS.GalFields.Xn5 α g')
    (hLFstarSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z))
    (hDzFstarSm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)))
    (hc2mSm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ))
    (Cdz Cw : ℝ) (hCdz : 0 < Cdz) (hCw : 0 < Cw)
    (hDzstarW : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ Cdz * α)
    (hWstar : Work.Spaces.WlInfMem α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ∧
      Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ Cw * α)
    (hZh0 : 0 ≤ Work.FTS.GalFields.Xn5 α h) :
    (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P6 α h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P6 α h)
          ≤ Work.FTS.GalFields.RHS.kA6 α Ci Cdz * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P7 α g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P7 α g h)
          ≤ Work.FTS.GalFields.RHS.kA7 α Ci * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P8 α g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P8 α g' h)
          ≤ Work.FTS.GalFields.RHS.kA8 α Ci * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P9 α h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P9 α h)
          ≤ Work.FTS.GalFields.RHS.kA9 α Ci Cw * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P6 α h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P7 α g h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P8 α g' h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P9 α h) := by
  have h0g : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have h0g' : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  -- ## `P₆ = -c2m·(D_zF_*·L₁₂h)`
  have hs6 : Work.FTS.EllipticEst.SmoothOpen (P6 α h) := by
    unfold P6
    exact Work.FTS.GalFields.RHS.smoothOpen_neg' (Work.FTS.NonlinRows.smoothOpen_mul hc2mSm
      (Work.FTS.NonlinRows.smoothOpen_mul hDzFstarSm hLhSm))
  have h6 : Work.Spaces.HkMem α 4 (P6 α h) ∧
      Work.FTS.Nonlin.Xn α (P6 α h) ≤ kA6 α Ci Cdz * TOf α g g' h := by
    have hw := hwprod (Work.Spaces.Dz (Work.Construction.Fstar α))
      (fun z θ => Work.Construction.L12 h z) hDzFstarSm (hDzstarW).1
      ⟨hLhSm, hLhMem⟩
    have huSm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * Work.Construction.L12 h z) :=
      Work.FTS.NonlinRows.smoothOpen_mul hDzFstarSm hLhSm
    have hang6 := Work.FTS.GalFields.RHS.Cangdef_spec.2 α
      (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        * Work.Construction.L12 h z) hα hα1 huSm hw.1
    refine ⟨?_, ?_⟩
    · unfold P6
      exact Work.FTS.StrongPersist.L3Rhs.HkMem_neg α 4 hang6.1
    · have hnegXn : Work.FTS.Nonlin.Xn α (P6 α h) = Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Construction.c2m θ * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ
            * Work.Construction.L12 h z)) := by
        unfold P6
        show Work.Spaces.HkNorm α 4 (-(fun z θ => Work.Construction.c2m θ
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ
              * Work.Construction.L12 h z))) = _
        rw [Work.FTS.EllipticEst.HkNorm_neg]
      rw [hnegXn]
      have hC0 : (0 : ℝ) ≤ Work.FTS.GalFields.RHS.Cangdef :=
        Work.FTS.GalFields.RHS.Cangdef_pos.le
      have hstep : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.c2m θ
            * (Work.Spaces.Dz (Work.Construction.Fstar α) z θ * Work.Construction.L12 h z))
          ≤ Real.sqrt Work.FTS.GalFields.RHS.Cangdef
              * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α)
                * (Ci * Work.FTS.GalFields.Xn5 α h)) := by
        have h1 := Work.FTS.GalFields.RHS.Xn_le_of_HkSq_le hC0 hang6.2
        refine le_trans h1 ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
        refine le_trans hw.2 ?_
        calc Ci * α ^ (-(1 / 2 : ℝ))
              * Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
              * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
            ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α)
              * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hDzstarW).2 hA0) (le_refl _)
                (Work.Spaces.HkNorm_nonneg α 4 (fun z θ => Work.Construction.L12 h z))
                (mul_nonneg hA0 (by positivity))
          _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α)
              * (Ci * Work.FTS.GalFields.Xn5 α h) :=
              mul_le_mul_of_nonneg_left hLhXn (mul_nonneg hA0 (by positivity))
      refine le_trans hstep ?_
      rw [kA6, TOf]
      have h1' : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      exact Work.FTS.GalFields.RHS.tof_mul_left_le'
        (Real.sqrt_nonneg Work.FTS.GalFields.RHS.Cangdef) (by positivity)
        (le_of_lt hCi) hZh0 h1'
  -- ## `P₇ = -c2m·(L₁₂g·D_zh)`
  have hs7 : Work.FTS.EllipticEst.SmoothOpen (P7 α g h) := by
    unfold P7
    exact Work.FTS.GalFields.RHS.smoothOpen_neg' (Work.FTS.NonlinRows.smoothOpen_mul hc2mSm
      (Work.FTS.NonlinRows.smoothOpen_mul hLgSm hDzhSm))
  have h7 : Work.Spaces.HkMem α 4 (P7 α g h) ∧
      Work.FTS.Nonlin.Xn α (P7 α g h) ≤ kA7 α Ci * TOf α g g' h := by
    have hp := hprod (fun z θ => Work.Construction.L12 g z) (Work.Spaces.Dz h)
      ⟨hLgSm, hLgMem⟩ ⟨hDzhSm, hDzhMem⟩
    have hang7 := Work.FTS.GalFields.RHS.Cangdef_spec.2 α
      (fun z θ => Work.Construction.L12 g z * Work.Spaces.Dz h z θ) hα hα1
      (Work.FTS.NonlinRows.smoothOpen_mul hLgSm hDzhSm) hp.1
    refine ⟨?_, ?_⟩
    · unfold P7
      exact Work.FTS.StrongPersist.L3Rhs.HkMem_neg α 4 hang7.1
    · have hnegXn : Work.FTS.Nonlin.Xn α (P7 α g h) = Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 g z * Work.Spaces.Dz h z θ)) := by
        unfold P7
        show Work.Spaces.HkNorm α 4 (-(fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 g z * Work.Spaces.Dz h z θ))) = _
        rw [Work.FTS.EllipticEst.HkNorm_neg]
      rw [hnegXn]
      have hC0 : (0 : ℝ) ≤ Work.FTS.GalFields.RHS.Cangdef :=
        Work.FTS.GalFields.RHS.Cangdef_pos.le
      have hstep : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 g z * Work.Spaces.Dz h z θ))
          ≤ Real.sqrt Work.FTS.GalFields.RHS.Cangdef
              * (Ci * α ^ (-(1 / 2 : ℝ))
                * (Ci * Work.FTS.Nonlin.Xn α g) * Work.FTS.GalFields.Xn5 α h) := by
        have h1 := Work.FTS.GalFields.RHS.Xn_le_of_HkSq_le hC0 hang7.2
        refine le_trans h1 ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
        refine le_trans hp.2 ?_
        calc Ci * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h)
            ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hLgXn hA0) (le_refl _)
                (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dz h))
                (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi)
                  (Work.Spaces.HkNorm_nonneg α 4 g)))
          _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
              * Work.FTS.GalFields.Xn5 α h :=
              mul_le_mul_of_nonneg_left hDzhXn
                (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi)
                  (Work.Spaces.HkNorm_nonneg α 4 g)))
      refine le_trans hstep ?_
      rw [kA7, TOf]
      have h1' : Work.FTS.Nonlin.Xn α g ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      exact Work.FTS.GalFields.RHS.tof_mul_mix_le
        (Real.sqrt_nonneg Work.FTS.GalFields.RHS.Cangdef) (by positivity)
        (le_of_lt hCi) hZh0 h1'
  -- ## `P₈ = -c2m·(L₁₂h·D_zg')`
  have hs8 : Work.FTS.EllipticEst.SmoothOpen (P8 α g' h) := by
    unfold P8
    exact Work.FTS.GalFields.RHS.smoothOpen_neg' (Work.FTS.NonlinRows.smoothOpen_mul hc2mSm
      (Work.FTS.NonlinRows.smoothOpen_mul hLhSm hDz'hSm))
  have h8 : Work.Spaces.HkMem α 4 (P8 α g' h) ∧
      Work.FTS.Nonlin.Xn α (P8 α g' h) ≤ kA8 α Ci * TOf α g g' h := by
    have hp := hprod (fun z θ => Work.Construction.L12 h z) (Work.Spaces.Dz g')
      ⟨hLhSm, hLhMem⟩ ⟨hDz'hSm, hDz'hMem⟩
    have hang8 := Work.FTS.GalFields.RHS.Cangdef_spec.2 α
      (fun z θ => Work.Construction.L12 h z * Work.Spaces.Dz g' z θ) hα hα1
      (Work.FTS.NonlinRows.smoothOpen_mul hLhSm hDz'hSm) hp.1
    refine ⟨?_, ?_⟩
    · unfold P8
      exact Work.FTS.StrongPersist.L3Rhs.HkMem_neg α 4 hang8.1
    · have hnegXn : Work.FTS.Nonlin.Xn α (P8 α g' h) = Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 h z * Work.Spaces.Dz g' z θ)) := by
        unfold P8
        show Work.Spaces.HkNorm α 4 (-(fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 h z * Work.Spaces.Dz g' z θ))) = _
        rw [Work.FTS.EllipticEst.HkNorm_neg]
      rw [hnegXn]
      have hC0 : (0 : ℝ) ≤ Work.FTS.GalFields.RHS.Cangdef :=
        Work.FTS.GalFields.RHS.Cangdef_pos.le
      have hstep : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.c2m θ
            * (Work.Construction.L12 h z * Work.Spaces.Dz g' z θ))
          ≤ Real.sqrt Work.FTS.GalFields.RHS.Cangdef
              * (Ci * α ^ (-(1 / 2 : ℝ))
                * (Ci * Work.FTS.GalFields.Xn5 α h) * Work.FTS.GalFields.Xn5 α g') := by
        have h1 := Work.FTS.GalFields.RHS.Xn_le_of_HkSq_le hC0 hang8.2
        refine le_trans h1 ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
        refine le_trans hp.2 ?_
        calc Ci * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz g')
            ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz g') :=
              mul_le_mul (mul_le_mul_of_nonneg_left hLhXn hA0) (le_refl _)
                (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dz g'))
                (mul_nonneg hA0 (by positivity))
          _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
              * Work.FTS.GalFields.Xn5 α g' :=
              mul_le_mul_of_nonneg_left hDz'hXn (mul_nonneg hA0 (by positivity))
      refine le_trans hstep ?_
      rw [kA8, TOf]
      have h1' : Work.FTS.GalFields.Xn5 α g' ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      exact Work.FTS.GalFields.RHS.tof_mul_mix_le'
        (Real.sqrt_nonneg Work.FTS.GalFields.RHS.Cangdef) (by positivity)
        (le_of_lt hCi) hZh0 h1'
  -- ## `P₉ = -(c2m·L₁₂F_*)·D_zh`
  have hs9 : Work.FTS.EllipticEst.SmoothOpen (P9 α h) := by
    unfold P9
    exact Work.FTS.GalFields.RHS.smoothOpen_neg' (Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_mul hc2mSm hLFstarSm) hDzhSm)
  have h9 : Work.Spaces.HkMem α 4 (P9 α h) ∧
      Work.FTS.Nonlin.Xn α (P9 α h) ≤ kA9 α Ci Cw * TOf α g g' h := by
    have hw := hwprod
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z)
      (Work.Spaces.Dz h)
      (Work.FTS.NonlinRows.smoothOpen_mul hc2mSm hLFstarSm) (hWstar).1
      ⟨hDzhSm, hDzhMem⟩
    refine ⟨?_, ?_⟩
    · unfold P9
      exact Work.FTS.StrongPersist.L3Rhs.HkMem_neg α 4 hw.1
    · have hnegXn : Work.FTS.Nonlin.Xn α (P9 α h) = Work.FTS.Nonlin.Xn α
          (fun z θ => (Work.Construction.c2m θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z)
            * Work.Spaces.Dz h z θ) := by
        unfold P9
        show Work.Spaces.HkNorm α 4 (-(fun z θ => (Work.Construction.c2m θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z)
            * Work.Spaces.Dz h z θ)) = _
        rw [Work.FTS.EllipticEst.HkNorm_neg]
      rw [hnegXn]
      have hstep : Work.FTS.Nonlin.Xn α (fun z θ => (Work.Construction.c2m θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z)
            * Work.Spaces.Dz h z θ)
          ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) * Work.FTS.GalFields.Xn5 α h := by
        have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
        refine le_trans hw.2 ?_
        calc Ci * α ^ (-(1 / 2 : ℝ))
              * Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
                * Work.Construction.L12 (Work.Construction.Fstar α) z)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h)
            ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α)
              * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hWstar).2 hA0) (le_refl _)
                (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dz h))
                (mul_nonneg hA0 (by positivity))
          _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) * Work.FTS.GalFields.Xn5 α h :=
              mul_le_mul_of_nonneg_left hDzhXn (mul_nonneg hA0 (by positivity))
      refine le_trans hstep ?_
      rw [kA9, TOf]
      have h1' : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      exact Work.FTS.GalFields.RHS.tof_mul_left_le_plain (by positivity) hZh0 h1'
  exact ⟨h6, h7, h8, h9, hs6, hs7, hs8, hs9⟩

end Work.FTS.StrongEps.EpsRLX
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.RadBound.diffDzd_ampA_mul_L12f_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX.RadBound

/-- **Differentiability of the `D_z`-iterates of `ampA α · L₁₂ f`.**

`ampA α z = 2z/(c(α)(1+z)²)` is a rational function, hence `C^5` on `(0,∞)`
(`E2pkg.contDiffOn_ampA_five`), so every `D_z`-iterate of it up to order `4` is differentiable
there (`E2pkg.differentiableAt_dzdIter_of_contDiffOn_general`).  With the hypothesis that the
iterates of `L₁₂ f` up to order `3` are differentiable on `(0,∞)`, the Leibniz rule for
`D_z = z ∂_z` (`E2pkg.differentiableAt_dzdIter_mul_of`, whose proof is the finite expansion
`Nonlinear.Pieces.dzdIter_mul_leibniz`) gives the differentiability of every iterate of the
product up to order `3`. -/
theorem diffDzd_ampA_mul_L12f_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : Work.FTS.Galerkin.Fn)
    (hL12diff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z) :
    ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z)) z := by
  intro b hb z hz
  -- `ampA α` is `C^5` on `(0,∞)`
  have hA5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_ampA_five α
  -- hence each of its iterates up to order `b` is differentiable there
  have hAdiff : ∀ c ≤ b, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c
        (Work.FTS.CoercivityFix.Transfer.ampA α)) z' := by
    intro c hc z' hz'
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_of_contDiffOn_general
      (N := 5) (hu := hA5) (c := c) (by omega) hz'
  -- the iterates of `L₁₂ f` up to order `b ≤ 3` are differentiable by hypothesis
  have hLdiff : ∀ c ≤ b, ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f)) z' :=
    fun c hc z' hz' => hL12diff c (by omega) z' hz'
  exact Work.FTS.CoercivityFix.Transfer.E2pkg.differentiableAt_dzdIter_mul_of hAdiff hLdiff hz

end Work.FTS.StrongEps.EpsRLX.RadBound
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.RadBound.radA_dzdIter_expansion_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.RadBound

set_option maxHeartbeats 1000000

/-! ## Smoothness of the two profile coefficients on `(0,∞)` -/

/-- `ampA α z = 2z/(c(α)(1+z)²)` is `C^5` on `(0,∞)`. -/
theorem contDiffOn_ampA_five_open (α : ℝ) :
    ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) := by
  rcases eq_or_ne (Work.Spaces.c α) 0 with hc | hc
  · have h0 : Work.FTS.CoercivityFix.Transfer.ampA α = fun _ : ℝ => (0 : ℝ) := by
      funext z
      simp only [Work.FTS.CoercivityFix.Transfer.ampA, hc, zero_mul, div_zero]
    rw [h0]
    exact contDiffOn_const
  · have hnum : ContDiffOn ℝ 5 (fun z : ℝ => 2 * z) (Set.Ioi (0 : ℝ)) :=
      contDiffOn_const.mul contDiffOn_id
    have hden : ContDiffOn ℝ 5 (fun z : ℝ => Work.Spaces.c α * (1 + z) ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      contDiffOn_const.mul ((contDiffOn_const.add contDiffOn_id).pow 2)
    have hne : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
      intro z hz
      have h1 : (0 : ℝ) < z := hz
      exact mul_ne_zero hc (pow_ne_zero 2 (by linarith))
    show ContDiffOn ℝ 5
      (fun z : ℝ => 2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) (Set.Ioi (0 : ℝ))
    exact hnum.div hden hne

/-- `ampB α z = 2z²/(1+z)³` is `C^5` on `(0,∞)`. -/
theorem contDiffOn_ampB_five_open (α : ℝ) :
    ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi (0 : ℝ)) := by
  have hnum : ContDiffOn ℝ 5 (fun z : ℝ => 2 * z ^ 2) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_const.mul (contDiffOn_id.pow 2)
  have hden : ContDiffOn ℝ 5 (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_const.add contDiffOn_id).pow 3
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have h1 : (0 : ℝ) < z := hz
    exact pow_ne_zero 3 (by linarith)
  show ContDiffOn ℝ 5 (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) (Set.Ioi (0 : ℝ))
  exact hnum.div hden hne

/-- Every `D_z`-iterate of order `b` of a `C^5`-function on `(0,∞)` is differentiable there. -/
theorem differentiableAt_dzdIter_of_contDiffOn_five {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 5 u (Set.Ioi (0 : ℝ))) {b : ℕ} (hb : b + 1 ≤ 5) {z : ℝ}
    (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z := by
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
  exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
    (hu := hu.of_le (by exact_mod_cast hb)) hz

/-! ## The expansion -/

theorem radA_dzdIter_expansion_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : Work.FTS.Galerkin.Fn)
    (hL12diff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z)
    (hAdiff : ∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
          * Work.Coercivity.L12f f z)) z) :
    ∀ q : ℕ, q ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z
        = -(∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
              * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
              * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
          + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
              * Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.ampB α) z := by
  intro q hq z hz
  have hA5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_ampA_five_open α
  have hB5 : ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampB α) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_ampB_five_open α
  -- differentiability of the iterates of the two factors of `ampA · L₁₂ f`
  have hAdiffA : ∀ b : ℕ, b < q → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (Work.FTS.CoercivityFix.Transfer.ampA α)) z' := by
    intro b hb z' hz'
    exact differentiableAt_dzdIter_of_contDiffOn_five hA5 (by omega) hz'
  have hLdiff : ∀ b : ℕ, b < q → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z' := by
    intro b hb z' hz'
    exact hL12diff b (by omega) z' hz'
  -- the Leibniz expansion of the first summand `-1 * (ampA · L₁₂ f)`
  have hU1z : Work.Elliptic.DzdIter q (fun w : ℝ => -1
        * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w)) z
      = -1 * ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
          * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
              * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z) := by
    have h1 : Work.Elliptic.DzdIter q (fun w : ℝ => -1
          * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w))
        = fun w : ℝ => -1 * Work.Elliptic.DzdIter q (fun z : ℝ =>
            Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z) w := by
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
        Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul,
        ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter q
          (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
            * Work.Coercivity.L12f f z)]
    rw [h1]
    change -1 * Work.Elliptic.DzdIter q (fun z : ℝ =>
        Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z) z
      = -1 * ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
          * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
              * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z)
    rw [Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz q
      (Work.FTS.CoercivityFix.Transfer.ampA α) (Work.Coercivity.L12f f) hAdiffA hLdiff z hz]
  -- the second summand is a constant multiple of `ampB`
  have hU2fun : ∀ j : ℕ, Work.Elliptic.DzdIter j (fun w : ℝ =>
        (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
      = fun w : ℝ => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
          * Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) w := by
    intro j
    have hfun : (fun w : ℝ => (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
        = fun w : ℝ => (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
            * Work.FTS.CoercivityFix.Transfer.ampB α w := by
      funext w
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hfun, Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
      Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul,
      ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j
        (Work.FTS.CoercivityFix.Transfer.ampB α)]
  have hU2z := congrFun (hU2fun q) z
  -- differentiability of the iterates of the two summands of the split
  have hdiff1 : ∀ b : ℕ, b < q → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun w : ℝ => -1
        * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w))) z' := by
    intro b hb z' hz'
    have h1 : Work.Elliptic.DzdIter b (fun w : ℝ => -1
          * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w))
        = fun w : ℝ => -1 * Work.Elliptic.DzdIter b (fun z : ℝ =>
            Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z) w := by
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
        Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul,
        ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b
          (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.ampA α z
            * Work.Coercivity.L12f f z)]
    rw [h1]
    exact (hAdiff b (by omega) z' hz').const_mul (-1)
  have hdiff2 : ∀ b : ℕ, b < q → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun w : ℝ =>
        (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z' := by
    intro b hb z' hz'
    have hd : DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (Work.FTS.CoercivityFix.Transfer.ampB α)) z' :=
      differentiableAt_dzdIter_of_contDiffOn_five hB5 (by omega) hz'
    rw [hU2fun b]
    exact hd.const_mul _
  -- additivity of the `D_z`-iterates on the split
  have hadd : Work.Elliptic.DzdIter q (fun w : ℝ =>
        -1 * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w)
        + (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
          * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z
      = Work.Elliptic.DzdIter q (fun w : ℝ => -1
          * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w)) z
        + Work.Elliptic.DzdIter q (fun w : ℝ =>
            (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff q _ _ hdiff1 hdiff2 z hz
  -- the pointwise split of `radA`
  have hsplit : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.FTS.CoercivityFix.Transfer.radA α f w
        = -1 * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w)
          + (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
    intro w _
    simp only [Work.FTS.CoercivityFix.Transfer.radA]
    ring
  have hcongr : Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z
      = Work.Elliptic.DzdIter q (fun w : ℝ =>
          -1 * (Work.FTS.CoercivityFix.Transfer.ampA α w * Work.Coercivity.L12f f w)
          + (Work.FTS.CoercivityFix.Transfer.ampB α w / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hsplit q z hz
  -- reassociate the summands to match the Leibniz output
  have hsum : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
            * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z))
      = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
        * Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z
        * Work.Elliptic.DzdIter (q - b) (Work.Coercivity.L12f f) z :=
    Finset.sum_congr rfl (fun b _ => by ring)
  rw [hcongr, hadd, hU1z, hU2z, hsum]
  ring

end Work.FTS.StrongEps.EpsRLX.RadBound
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.L12_Pz_Jeps_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools.LinAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The `ε`-membership as a product-measure integrability -/

/-- The product of the two restricted measures is the restriction of the planar Lebesgue measure
to the closed quadrant `Iz ×ˢ Iθ`. -/
theorem quadrant_restrict_prod :
    (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]

/-- `EpsMem` reformulated as `Integrable` for the product of the two restricted measures. -/
theorem EpsMem_integrable {α : ℝ} {f : ℝ → ℝ → ℝ} (h : Work.FTS.StrongEps.EpsMem α f) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, quadrant_restrict_prod] at h
  exact h

/-- **The angular slice of the `ε`-weighted square is integrable for a.e. radial variable.**
This is Tonelli (`Integrable.prod_right_ae`) applied to `EpsMem`. -/
theorem ae_integrable_slice_epsW_sq {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.StrongEps.EpsMem α f) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.Integrable
        (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := by
  rw [← Work.FTS.StrongEps.JepsHkMem.restrict_Iz_eq]
  exact (EpsMem_integrable h).prod_right_ae

/-! ## The AM–GM bound of the `L₁₂`-density integrand -/

/-- The weight `w` is positive on the open half-line. -/
theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

/-- **The pointwise AM–GM bound of the `L₁₂`-density integrand by the `ε`-weighted square.**
On the *open* angular interval (where `epsW` does not degenerate),

  `|K θ · g θ / s| ≤ (3/(2s)) · ((g θ · epsW α s θ)² + (1/w s)²)`. -/
theorem abs_K_mul_div_le {α s : ℝ} (hs : 0 < s) (hgam : 0 ≤ Work.Spaces.gam α / 2)
    {g : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.K θ * g θ / s|
      ≤ (3 / (2 * s)) * ((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2 + (1 / Work.Spaces.w s) ^ 2) := by
  have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hw : 0 < Work.Spaces.w s := w_pos_of_pos hs
  have hSpow : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hsin _
  have hK3 : |Work.Spaces.K θ| ≤ 3 := by
    rw [abs_of_nonneg (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hIθ)]
    exact Work.FTS.GalBasis.cc.K_le_three_of_mem_Iθ hIθ
  -- `|g θ|` expressed through the `ε`-weighted square
  have hident : |g θ * Work.FTS.StrongEps.epsW α s θ|
      * (Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s) = |g θ| := by
    have heps : Work.FTS.StrongEps.epsW α s θ
        = Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := rfl
    rw [heps, abs_mul, abs_of_pos (div_pos hw hSpow)]
    field_simp
  have hbound : |g θ| ≤ ((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2
      + (1 / Work.Spaces.w s) ^ 2) / 2 := by
    have hwnn : 0 ≤ Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s :=
      div_nonneg (Real.rpow_nonneg hsin.le _) hw.le
    have hamgm : |g θ * Work.FTS.StrongEps.epsW α s θ|
        * (Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s)
        ≤ ((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2
            + (Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|g θ * Work.FTS.StrongEps.epsW α s θ|
          - Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s),
        sq_abs (g θ * Work.FTS.StrongEps.epsW α s θ)]
    have hsincmp : Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s
        ≤ 1 / Work.Spaces.w s :=
      div_le_div_of_nonneg_right (Real.rpow_le_one hsin.le (Real.sin_le_one _) hgam) hw.le
    have hsinsq : (Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s) ^ 2
        ≤ (1 / Work.Spaces.w s) ^ 2 := by
      have h := mul_self_le_mul_self hwnn hsincmp
      simpa [pow_two] using h
    rw [hident] at hamgm
    linarith [hamgm, hsinsq]
  have hstep1 : |Work.Spaces.K θ * g θ / s| = |Work.Spaces.K θ| * |g θ| / s := by
    rw [abs_div, abs_mul, abs_of_pos hs]
  have hstep2 : |Work.Spaces.K θ| * |g θ| / s ≤ 3 * |g θ| / s := by
    rw [div_le_div_iff_of_pos_right hs]
    exact mul_le_mul_of_nonneg_right hK3 (abs_nonneg _)
  have hstep3 : 3 * |g θ| / s
      ≤ 3 * (((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2
          + (1 / Work.Spaces.w s) ^ 2) / 2) / s := by
    rw [div_le_div_iff_of_pos_right hs]
    exact mul_le_mul_of_nonneg_left hbound (by norm_num)
  rw [hstep1]
  refine le_trans hstep2 (le_trans hstep3 ?_)
  exact le_of_eq (by ring)

/-- The constant majorant `(3/(2s))(1/w s)²` is integrable on the angular interval. -/
theorem integrableOn_const_majorant (s : ℝ) :
    MeasureTheory.IntegrableOn
      (fun _ : ℝ => (3 / (2 * s)) * (1 / Work.Spaces.w s) ^ 2) Work.Spaces.Iθ := by
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ := by
    refine MeasureTheory.integrableOn_const (C := (1 : ℝ)) ?_ ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]
      simp
    · simp
  have h2 : MeasureTheory.Integrable
      (fun _ : ℝ => (3 / (2 * s)) * (1 / Work.Spaces.w s) ^ 2 * 1)
      (volume.restrict Work.Spaces.Iθ) := h1.const_mul _
  exact h2.congr (Filter.Eventually.of_forall fun _ => by ring)

/-- **The `L₁₂`-density integrand is integrable as soon as the `ε`-weighted square is.** -/
theorem integrableOn_K_mul_div_of_integrable_epsW_sq {α s : ℝ} (hs : 0 < s)
    (hgam : 0 ≤ Work.Spaces.gam α / 2) {g : ℝ → ℝ}
    (hg : MeasureTheory.Integrable
      (fun θ => (g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ))
    (haesm : AEStronglyMeasurable (fun θ => Work.Spaces.K θ * g θ / s)
      (volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.Integrable (fun θ => Work.Spaces.K θ * g θ / s)
      (volume.restrict Work.Spaces.Iθ) := by
  have hmaj : MeasureTheory.Integrable
      (fun θ => (3 / (2 * s)) * ((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2
        + (1 / Work.Spaces.w s) ^ 2)) (volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.Integrable
        (fun θ => (3 / (2 * s)) * (g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := hg.const_mul _
    have h2 : MeasureTheory.Integrable
        (fun θ => (3 / (2 * s)) * (1 / Work.Spaces.w s) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := integrableOn_const_majorant s
    have hsum : MeasureTheory.Integrable
        ((fun θ : ℝ => (3 / (2 * s)) * (g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2)
          + fun θ : ℝ => (3 / (2 * s)) * (1 / Work.Spaces.w s) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := h1.add h2
    have heq : ((fun θ : ℝ => (3 / (2 * s)) * (g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2)
          + fun θ : ℝ => (3 / (2 * s)) * (1 / Work.Spaces.w s) ^ 2)
        = fun θ : ℝ => (3 / (2 * s)) * ((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2
            + (1 / Work.Spaces.w s) ^ 2) := by
      funext θ
      simp only [Pi.add_apply]
      ring
    rwa [heq] at hsum
  refine hmaj.mono' haesm ?_
  have hIoo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
    rw [Work.FTS.StrongEps.JepsHkMem.restrict_Iθ_eq]
    exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo
  filter_upwards [hIoo] with θ hθ
  simpa only [Real.norm_eq_abs] using abs_K_mul_div_le (α := α) hs hgam hθ

/-! ## Almost-everywhere integrability of the angular slice of `J_ε δ` -/

/-- The slices of `J_ε f` at `z > 0` are a.e. strongly measurable. -/
theorem ae_aesm_slice_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ → ℝ → ℝ}
    (hδ : ContinuousOn (Function.uncurry δ) Work.FTS.StrongEps.Quad) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      AEStronglyMeasurable (fun θ => Work.FTS.StrongEps.Jeps ρ ε δ z θ)
        (volume.restrict Work.Spaces.Iθ) := by
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
  exact Work.FTS.StrongEps.JepsHkMem.aestronglyMeasurable_Jeps_slice hρ hε hδ hz

/-! ## The theorem -/

theorem L12_Pz_Jeps_zero (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α ε : ℝ} (hα : α ∈ Set.Ioc 0 1) (hε : ε ∈ Set.Ioc 0 1) {δ : ℝ → ℝ → ℝ}
    (hδ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry δ) Work.FTS.EllipticEst.Q0)
    (hδmem : Work.FTS.StrongEps.EpsMem α δ) :
    Work.Construction.L12 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε δ)) 0 = 0 := by
  set J : ℝ → ℝ → ℝ := Work.FTS.StrongEps.Jeps ρ ε δ with hJ
  set B : ℝ → ℝ → ℝ := Work.FTS.StrongEps.bump with hB
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry δ) Work.FTS.StrongEps.Quad :=
    fun n => hδ n
  have hδc : ContinuousOn (Function.uncurry δ) Work.FTS.StrongEps.Quad := (hδ 0).continuousOn
  have hgam : 0 ≤ Work.Spaces.gam α / 2 := by rw [Work.Spaces.gam]; linarith [hα.1]
  -- The normalising constant is non-zero
  have hpz : Work.FTS.StrongEps.pzNorm ≠ 0 :=
    ne_of_gt Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  -- `EpsMem` of the mollified profile
  obtain ⟨C, _hCpos, hC⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 ρ hρ
  have hEpsJ : Work.FTS.StrongEps.EpsMem α J :=
    (hC α hα ε hε.1 hε.2 δ hsm hδmem).1
  -- The angular slice of the density of `J` is integrable for a.e. radial variable
  have hJslice : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * J s θ / s) Work.Spaces.Iθ := by
    have h1 := ae_integrable_slice_epsW_sq (α := α) hEpsJ
    have h2 := ae_aesm_slice_Jeps (ρ := ρ) hρ.moll hε.1 hδc
    have h3 : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 < s :=
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi
    have hKc : Continuous Work.Spaces.K := by
      show Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
      fun_prop
    filter_upwards [h1, h2, h3] with s hs1 hs2 hs3
    have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.K θ * J s θ / s)
        (volume.restrict Work.Spaces.Iθ) :=
      ((hKc.div_const s).aestronglyMeasurable.mul hs2).congr
        (Filter.Eventually.of_forall fun θ => by
          simp only [Pi.mul_apply, hJ]
          ring)
    exact integrableOn_K_mul_div_of_integrable_epsW_sq hs3 hgam hs1 haesm
  -- The projection, as a functional identity
  set c : ℝ := Work.Construction.L12 J 0 / Work.FTS.StrongEps.pzNorm with hc
  have hPz : Work.FTS.StrongEps.Pz J = fun z θ => J z θ + (-c) * B z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply, hc, hJ, hB]
    ring
  -- The correction has integrable angular slices and integrable density
  have hBslice : ∀ s : ℝ, 0 < s →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * B s θ / s) Work.Spaces.Iθ := by
    intro s hs
    have h := Work.FTS.StrongEps.PZeroAux.integrableOn_slice_bump (s := s) hs
    exact h.congr_fun (fun θ _ => by rw [hB]) measurableSet_Icc
  have hBdens : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K B s)
      (Set.Ioi 0) := by
    have h := Work.FTS.StrongEps.PZeroAux.integrableOn_L12dens_bump
    rw [← hB] at h
    exact h
  -- The density identity, a.e. in the radial variable
  have hden : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Work.FM.L12dens Work.Spaces.K (fun z θ => J z θ + (-c) * B z θ) s
        = Work.FM.L12dens Work.Spaces.K J s + (-c) * Work.FM.L12dens Work.Spaces.K B s := by
    have h4 : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 < s :=
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi
    filter_upwards [hJslice, h4] with s hsJ hs
    have hBint : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * ((-c) * B s θ) / s) Work.Spaces.Iθ := by
      have h := hBslice s hs
      have h2 : MeasureTheory.IntegrableOn
          (fun θ => (-c) * (Work.Spaces.K θ * B s θ / s)) Work.Spaces.Iθ :=
        MeasureTheory.Integrable.const_mul h (-c)
      exact MeasureTheory.IntegrableOn.congr_fun h2 (fun θ _ => by ring) measurableSet_Icc
    have hlin := Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
      (a := J) (b := fun z θ => (-c) * B z θ) (s := s) hsJ hBint
    have hscale := Work.FTS.LocData.L12dens_const_mul Work.Spaces.K (-c) B s
    rw [hlin, hscale]
  -- The values of the two densities
  have hBval : (∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K B s)
      = Work.FTS.StrongEps.pzNorm := by
    rw [hB, Work.FTS.StrongEps.pzNorm, Work.Construction.L12, Work.FM.L12]
  have hJval : (∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K J s)
      = c * Work.FTS.StrongEps.pzNorm := by
    rw [hc]
    have h : Work.Construction.L12 J 0
        = ∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K J s := by
      rw [Work.Construction.L12, Work.FM.L12]
    rw [h, div_mul_cancel₀ (∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K J s) hpz]
  -- The goal, unfolded
  rw [hPz, Work.Construction.L12, Work.FM.L12]
  by_cases hZint : MeasureTheory.IntegrableOn
      (fun s => Work.FM.L12dens Work.Spaces.K (fun z θ => J z θ + (-c) * B z θ) s)
      (Set.Ioi 0)
  · -- The density of the projected profile is integrable: the outer integral splits
    have hae : (fun s => Work.FM.L12dens Work.Spaces.K (fun z θ => J z θ + (-c) * B z θ) s)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun s => Work.FM.L12dens Work.Spaces.K J s
          - c * Work.FM.L12dens Work.Spaces.K B s := by
      filter_upwards [hden] with s hs
      rw [hs]; ring
    have hYc : MeasureTheory.IntegrableOn
        (fun s => c * Work.FM.L12dens Work.Spaces.K B s) (Set.Ioi 0) :=
      MeasureTheory.Integrable.const_mul hBdens c
    have hJmem : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K J s)
        (Set.Ioi 0) := by
      have h1 : MeasureTheory.Integrable
          (fun s => Work.FM.L12dens Work.Spaces.K (fun z θ => J z θ + (-c) * B z θ) s
            + c * Work.FM.L12dens Work.Spaces.K B s) (volume.restrict (Set.Ioi (0 : ℝ))) :=
        MeasureTheory.Integrable.add hZint hYc
      refine h1.congr ?_
      filter_upwards [hae] with s hs
      rw [hs]; ring
    have hsplit : (∫ s in Set.Ioi (0 : ℝ),
          Work.FM.L12dens Work.Spaces.K (fun z θ => J z θ + (-c) * B z θ) s)
        = ∫ s in Set.Ioi (0 : ℝ),
            (Work.FM.L12dens Work.Spaces.K J s
              - c * Work.FM.L12dens Work.Spaces.K B s) := by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp hae] with s hs
      intro hs'
      exact hs hs'
    rw [hsplit]
    rw [MeasureTheory.integral_sub hJmem hYc]
    rw [MeasureTheory.integral_const_mul, hJval, hBval]
    ring
  · exact MeasureTheory.integral_undef hZint

end Work.FTS.StrongEps.EpsSqTools.LinAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.L5AtomsW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

/-- **The `L5` data of the three `w`-atoms.**  `L5 α f a` (defined in
`Submission/Work/FTS/StrongEps/H5/Data.lean`) is the bundle `HQo α 4 f`, `HQo α 4 (Dz f)`,
`HQo α 4 (Dth f)` with the single bound `a` on the three level-four norms
`Xn α f, Xn α (Dz f), Xn α (Dth f)` (`Xn α = HkNorm α 4`).

For a `ClassC` datum `w` with `Xn α w ≤ C₀ α²` and `HkNorm α 6 w ≤ B` there is `a > 0`
(depending on `α, C₀, B` but not on `w`) with `L5 α w a`, `L5 α (Dz w) a`, `L5 α (Dth w) a`.

Route: `ClassC α w` gives `SmoothOpen w` and `HkMem α 7 w`.  Iterate
`Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm` (level-general) with
`Work.FTS.StrongPersist.q0Sm_of_smoothOpen` to get `HkMem α 4` of `w`, `Dz w`, `Dth w`,
`Dz (Dz w)`, `Dz (Dth w)`, `Dth (Dz w)`, `Dth (Dth w)`; the norm bounds come from the sub-sum
comparisons `HkSq_Dz_le_Q0Sm` / `HkSq_Dth_le` iterated from level four to level six (e.g.
`HkSq α 4 (Dz (Dz w)) ≤ HkSq α 6 w`), hence every `Xn`-bound is `≤ HkNorm α 6 w ≤ B` (or
`≤ C₀ α²` for `w` itself).  A safe choice of the constant is
`a := max (max (C₀ * α ^ 2) B) 0 + 1` (the bound hypotheses are then vacuous for negative
`C₀`/`B`, which is harmless). -/
theorem L5AtomsW : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.FTS.StrongEps.H5.L5 α w a ∧
      Work.FTS.StrongEps.H5.L5 α (Work.Spaces.Dz w) a ∧
      Work.FTS.StrongEps.H5.L5 α (Work.Spaces.Dth w) a := by
  intro α hα C₀ B
  have hα0 : 0 < α := hα.1
  have hα10 : -(1 / 10 : ℝ) ≤ α := by linarith [hα.1]
  refine ⟨max (max (C₀ * α ^ 2) B) 0 + 1, ?_, ?_⟩
  · have h := le_max_right (max (C₀ * α ^ 2) B) (0 : ℝ)
    linarith
  · intro w hw _hXn hB
    have hreg : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
    -- ### the level-five memberships of the atom and of its two first derivatives
    have h6 : Work.Spaces.HkMem α 6 w :=
      Work.FTS.OpenPkg.HkMem_mono_open hreg 6 (by norm_num) hw.mem
    have h5 : Work.Spaces.HkMem α 5 w :=
      Work.FTS.OpenPkg.HkMem_mono_open hreg 5 (by norm_num) hw.mem
    have h5Dz : Work.Spaces.HkMem α 5 (Work.Spaces.Dz w) :=
      Work.FTS.IPGen.HkMem_Dz_le hreg h6
    have h5Dth : Work.Spaces.HkMem α 5 (Work.Spaces.Dth w) :=
      Work.FTS.IPGen.HkMem_Dth_le hα10 hreg h6
    -- ### the level-five norm bounds, all dominated by `HkNorm α 6 w ≤ B`
    have haB : B ≤ max (max (C₀ * α ^ 2) B) 0 + 1 := by
      have h1 : B ≤ max (C₀ * α ^ 2) B := le_max_right _ _
      have h2 : max (C₀ * α ^ 2) B ≤ max (max (C₀ * α ^ 2) B) 0 := le_max_left _ _
      linarith
    have hb6 : Work.Spaces.HkNorm α 6 w ≤ max (max (C₀ * α ^ 2) B) 0 + 1 :=
      le_trans hB haB
    have hb5w : Work.Spaces.HkNorm α 5 w ≤ max (max (C₀ * α ^ 2) B) 0 + 1 :=
      le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 5) (by norm_num) h6) hb6
    have hb5Dz : Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w)
        ≤ max (max (C₀ * α ^ 2) B) 0 + 1 :=
      calc Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w)
          = Real.sqrt (Work.Spaces.HkSq α 5 (Work.Spaces.Dz w)) := rfl
        _ ≤ Real.sqrt (Work.Spaces.HkSq α 6 w) :=
            Real.sqrt_le_sqrt
              (Work.FTS.StrongPersist.H6Aux.HkSq_Dz_le_succ' α 5 hreg h6)
        _ = Work.Spaces.HkNorm α 6 w := rfl
        _ ≤ max (max (C₀ * α ^ 2) B) 0 + 1 := hb6
    have hb5Dth : Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w)
        ≤ max (max (C₀ * α ^ 2) B) 0 + 1 :=
      calc Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w)
          = Real.sqrt (Work.Spaces.HkSq α 5 (Work.Spaces.Dth w)) := rfl
        _ ≤ Real.sqrt (Work.Spaces.HkSq α 6 w) :=
            Real.sqrt_le_sqrt
              (Work.FTS.StrongPersist.H6Aux.HkSq_Dth_le_succ' α hα10 5 h6)
        _ = Work.Spaces.HkNorm α 6 w := rfl
        _ ≤ max (max (C₀ * α ^ 2) B) 0 + 1 := hb6
    exact ⟨Work.FTS.StrongEps.H5.L5_of_HQo5 hα0 ⟨hreg, h5⟩ hb5w,
      Work.FTS.StrongEps.H5.L5_of_HQo5 hα0 ⟨hreg.Dz, h5Dz⟩ hb5Dz,
      Work.FTS.StrongEps.H5.L5_of_HQo5 hα0 ⟨hreg.Dth, h5Dth⟩ hb5Dth⟩

end Work.FTS.StrongEps.H5.Atoms
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.L5C2mL12W =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## The two pointwise multiplier identities

`D_z` and `D_θ` applied to a product of an angular factor with a second factor: since `D_z` is
`z∂_z` and the angular factor does not depend on `z`, the derivative only hits the second factor;
for a *radial* second factor the surviving derivative falls on the angular factor alone.  Both
identities are consequences of `deriv_const_mul_field` and hold *everywhere*, not merely on the
open quadrant. -/

/-- `D_z (a(θ)·g(z,θ)) = a(θ)·D_z g(z,θ)`. -/
theorem Dz_ang_mul (a : ℝ → ℝ) (g : Work.FTS.Galerkin.Fn) :
    Work.Spaces.Dz (fun z θ => a θ * g z θ)
      = fun z θ => a θ * Work.Spaces.Dz g z θ := by
  funext z θ
  show z * deriv (fun z' => a θ * g z' θ) z = a θ * (z * deriv (fun z' => g z' θ) z)
  rw [deriv_const_mul_field (a θ)]
  ring

/-- `D_θ (a(θ)·r(z)) = (D_θ a)(θ)·r(z)`, where `Work.Spaces.dthU a θ = sin(2θ)·a'(θ)` is the
one-variable avatar of `D_θ` on a `θ`-only profile. -/
theorem Dth_ang_radial_mul (a : ℝ → ℝ) (r : ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => a θ * r z)
      = fun z θ => Work.Spaces.dthU a θ * r z := by
  funext z θ
  show Real.sin (2 * θ) * deriv (fun θ' => a θ' * r z) θ
      = Real.sin (2 * θ) * deriv a θ * r z
  have h : (fun θ' => a θ' * r z) = fun θ' => r z * a θ' := by funext θ'; ring
  rw [h, deriv_const_mul_field (r z)]
  ring

/- The angular data of the derivative profile `D_θ c₂m` — `D_θ c₂m = -3 sin(2θ)²` is `C^∞`
and its `D_θ`-iterates of orders `1..4` are the orders `2..5` of `c₂m`, hence decay like
`sin(2θ)` — is proved in the sibling module
`Submission.Work.FTS.StrongEps.H5.Atoms.DthUC2mProfileData` (imported above), as
`Work.FTS.StrongEps.H5.Atoms.DthUC2mProfileData`. -/

/-- **The `L5` data of the angular atom `c₂(θ)·L₁₂(w)(z)`**, conditional on the `L5`-data of
`L₁₂(w)` (lemma `L5L12W`, passed as the hypothesis `hL12`).

Route: on the open quadrant `Dz (fun z θ => c₂(θ)·L₁₂(w)(z)) = c₂(θ) · Dz (fun z θ => L₁₂(w)(z))`
and `Dth (fun z θ => c₂(θ)·L₁₂(w)(z)) = (Dth c₂)(θ) · L₁₂(w)(z)` (`H5.Dz_mul_eqOn_Q0` /
`H5.Dth_mul_eqOn_Q0` plus `Dth` of a radial function is `0`).  Both are products of an angular
factor with an `HQo α 4` factor, so `Work.FTS.OpenPkg.angmul_field` (the level-four
angular-multiplication rule, which asks for `|a θ| ≤ B` and `|DthIter i a 0 θ| ≤ B · sin(2θ)`,
`1 ≤ i ≤ 4`, on `Iθ`) applies with `a = c₂`
(`Work.FTS.GalFields.RHS.smoothOpen_c2m_ang`, `Work.FTS.Nonlinear.Pieces.abs_c2m_le_two`,
`Work.FTS.Nonlinear.Pieces.DthIter_c2m_le`) — for the `D_θ`-derivative of the atom the angular
factor is `Dth c₂`, whose iterates `DthIter i (Dth c₂) = DthIter (i+1) c₂` need the same
pointwise bound at angular orders `≤ 5` (`Work.FTS.StrongPersist.dthU_c2m_bound6`).  The norms of
`c₂·L₁₂(w)` and of `c₂·Dz(L₁₂(w))` are bounded by `Cang · 1000 · Xn α (L₁₂ w)` resp.
`Cang · 1000 · Xn α (Dz (L₁₂ w))`, with `Cang` the constant of `angmul_field`; use the `L5`-bound
`a` of `hL12` for both. -/
theorem L5C2mL12W
    (hL12 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
      ∃ a : ℝ, 0 < a ∧ ∀ {w : Work.FTS.Galerkin.Fn},
        Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
        Work.Spaces.HkNorm α 6 w ≤ B →
        Work.FTS.StrongEps.H5.L5 α (fun z θ => Work.Construction.L12 w z) a) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.FTS.StrongEps.H5.L5 α
        (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) a := by
  intro α hαI C₀ B
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  -- the two universal constants
  obtain ⟨Cang, hCangpos, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨Cd, hCdpos, hCdSm, hCdB, hCdIt⟩ := DthUC2mProfileData
  -- the `L5`-data of the radial atom
  obtain ⟨aL, haLpos, hLdat⟩ := hL12 hαI (C₀ := C₀) (B := B)
  -- the common constant of the answer
  set A : ℝ := Cang * 1000 * aL + Cang * Cd * aL + 1 with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hle1 : Cang * 1000 * aL ≤ A := by
    rw [hAdef]; linarith [show (0 : ℝ) ≤ Cang * Cd * aL by positivity]
  have hle2 : Cang * Cd * aL ≤ A := by
    rw [hAdef]; linarith [show (0 : ℝ) ≤ Cang * 1000 * aL by positivity]
  refine ⟨A, hApos, ?_⟩
  intro w hw hXnw hX6
  -- the `L5`-data of `L₁₂(w)`
  have hLw : Work.FTS.StrongEps.H5.L5 α (fun z θ => Work.Construction.L12 w z) aL :=
    hLdat hw hXnw hX6
  have hgsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z) := hLw.qo.1
  have hgmem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z) := hLw.qo.2
  have hgX : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z) ≤ aL := hLw.bd
  -- the angular data of `c₂m`
  have hc2mSm : Work.FTS.EllipticEst.SmoothOpen
      (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    Work.FTS.GalFields.RHS.smoothOpen_c2m_ang
  have hc2mB : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ 1000 :=
    fun θ _ => Work.FTS.GalFields.RHS.abs_c2m_le_thousand θ
  have hc2mIt : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ 1000 * Real.sin (2 * θ) :=
    fun i hi hi4 => Work.FTS.GalFields.RHS.DthIter_c2m_le_sin i hi hi4
  -- the three applications of the angular-multiplication rule
  have hA1 := hang α hα hα1 (fun θ => Work.Construction.c2m θ)
    (fun z θ => Work.Construction.L12 w z) 1000 hc2mSm hc2mB hc2mIt hgsm hgmem
  have hA2 := hang α hα hα1 (fun θ => Work.Construction.c2m θ)
    (Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z)) 1000 hc2mSm hc2mB hc2mIt
    hLw.qoDz.1 hLw.qoDz.2
  have hA3 := hang α hα hα1 (fun θ => Work.Spaces.dthU Work.Construction.c2m θ)
    (fun z θ => Work.Construction.L12 w z) Cd hCdSm hCdB hCdIt hgsm hgmem
  -- smoothness of the atom and of its two derivatives
  have hfsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hc2mSm hgsm
  -- the `D_z`-slot
  have hDzmem : Work.Spaces.HkMem α 4
      (Work.Spaces.Dz (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hA2.1 (fun z _ θ _ => by
      rw [Dz_ang_mul (fun θ => Work.Construction.c2m θ)
        (fun z θ => Work.Construction.L12 w z)])
  have hDzb : Work.FTS.Nonlin.Xn α
      (Work.Spaces.Dz (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)) ≤ A := by
    rw [Dz_ang_mul (fun θ => Work.Construction.c2m θ)
      (fun z θ => Work.Construction.L12 w z)]
    exact le_trans hA2.2 (le_trans (mul_le_mul_of_nonneg_left hLw.bdDz (by positivity)) hle1)
  -- the `D_θ`-slot
  have hDthmem : Work.Spaces.HkMem α 4
      (Work.Spaces.Dth (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hA3.1 (fun z _ θ _ => by
      rw [Dth_ang_radial_mul (fun θ => Work.Construction.c2m θ)
        (fun z => Work.Construction.L12 w z)])
  have hDthb : Work.FTS.Nonlin.Xn α
      (Work.Spaces.Dth (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)) ≤ A := by
    rw [Dth_ang_radial_mul (fun θ => Work.Construction.c2m θ)
      (fun z => Work.Construction.L12 w z)]
    exact le_trans hA3.2 (le_trans (mul_le_mul_of_nonneg_left hgX (by positivity)) hle2)
  -- the six fields of `L5`
  refine ⟨⟨hfsm, hA1.1⟩,
    le_trans hA1.2 (le_trans (mul_le_mul_of_nonneg_left hgX (by positivity)) hle1),
    ⟨hfsm.Dz, hDzmem⟩, hDzb,
    ⟨hfsm.Dth, hDthmem⟩, hDthb⟩

end

end Work.FTS.StrongEps.H5.Atoms
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.W5C2mL12Fstar =====
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

/-! ## Elementary derivative facts

The two functions that occur as the *radial* factor of the two derivatives of
`f_α(z,θ) = c₂(θ)·L₁₂(F_*)(z)` are

* `invH α = z ↦ 2α/(1+z)` (the radial factor of `f_α` and of `D_θf_α`), and
* `z ↦ -2α z/(1+z)² = -2α·hKer z` (the radial factor of `D_zf_α`).

Their weighted `z`-derivatives are controlled by the two ready-made bounds
`FstarPkg.c2mInv_radial` and `Spaces.pzIter_hKer_bound`; the only derivative actually
computed by hand is `d/dz (2α/(1+z))` (and, through `deriv_iter_const_mul`, the passage to
`-2α·hKer`). -/

/-- `deriv (z ↦ 2α/(1+z)) z = -2α/(1+z)²` for `z ≠ -1`. -/
private theorem deriv_invH (α z : ℝ) (hz : 1 + z ≠ 0) :
    deriv (fun z : ℝ => 2 * α / (1 + z)) z = -2 * α / (1 + z) ^ 2 := by
  have hd : deriv (fun z : ℝ => 1 + z) z = 1 := by
    rw [deriv_const_add, deriv_id'']
  rw [deriv_const_div (2 * α) (by fun_prop) hz, hd]
  ring

/-- The iterated `deriv` of a constant multiple: `deriv^[k] (c·b) = c·deriv^[k] b`. -/
private theorem deriv_iter_const_mul (c : ℝ) (k : ℕ) :
    ∀ b : ℝ → ℝ, deriv^[k] (fun z => c * b z) = fun z => c * deriv^[k] b z := by
  induction k with
  | zero => intro b; rfl
  | succ k ih =>
      intro b
      have h1 : deriv^[k+1] (fun z => c * b z) = deriv^[k] (deriv (fun z => c * b z)) :=
        Function.iterate_succ_apply deriv k (fun z => c * b z)
      rw [h1, show deriv (fun z => c * b z) = fun z => c * deriv b z from
        funext fun z => Work.Spaces.deriv_const_mul' c z b, ih (deriv b),
        show deriv^[k+1] b = deriv^[k] (deriv b) from Function.iterate_succ_apply deriv k b]

/-- The weighted `z`-derivative bound for `hKer z = z/(1+z)²`. -/
private theorem hKer_weighted_bound (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) :=
  Work.Spaces.pzIter_hKer_bound k z hz

/-! ## Separable products: the radial and mixed `SupFinite` slots

Every slot of `WlInfMem` of a separable product `(z,θ) ↦ a(θ)·b(z)` is, after
`pzIter_decomp` / `DthIter_decomp`, the product of an iterate of `a` with a weighted
`z`-derivative of `b` (times the angular weight `sin(2θ)^{-α/5}/(α+sin 2θ)` in the mixed
case).  The `SupFinite` requirement of `WlInfMem` is therefore discharged by pointwise
bounds, the only non-trivial step being the elementary `sin²(2θ)·sin(2θ)^{-α/5}/(α+sin 2θ) ≤ 1`
(`FstarPkg.sinWeight_le_one`). -/

/-- The radial `SupFinite` slots of a separable product. -/
private theorem supFinite_sep_radial {a b : ℝ → ℝ} {k : ℕ} {A B : ℝ}
    (hA : ∀ θ, |a θ| ≤ A) (hB : ∀ z, 0 ≤ z → |(z + 1) ^ k * deriv^[k] b z| ≤ B) :
    Work.Spaces.SupFinite
      (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => a θ * b z) z θ) := by
  have hAnn : 0 ≤ A := le_trans (abs_nonneg (a 0)) (hA 0)
  refine ⟨A * B, ?_⟩
  rintro y ⟨z, hz, θ, hθ, rfl⟩
  show |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => a θ * b z) z θ| ≤ A * B
  rw [Work.Spaces.pzIter_decomp k a b z θ]
  rw [show (z + 1) ^ k * (a θ * deriv^[k] b z)
      = a θ * ((z + 1) ^ k * deriv^[k] b z) by ring, abs_mul]
  exact mul_le_mul (hA θ) (hB z hz) (abs_nonneg _) hAnn

/-- The mixed `SupFinite` slots of a separable product. -/
private theorem supFinite_sep_mixed {a b : ℝ → ℝ} {α : ℝ} {j k : ℕ} {C B : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hCnn : 0 ≤ C)
    (hC : ∀ θ, |(Work.Spaces.dthU^[j]) a θ| ≤ C * Real.sin (2 * θ) ^ 2)
    (hB : ∀ z, 0 ≤ z → |(z + 1) ^ k * deriv^[k] b z| ≤ B) :
    Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k *
      Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => a θ * b z)) z θ
      * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
  refine ⟨C * B, ?_⟩
  rintro y ⟨z, hz, θ, hθ, rfl⟩
  show |(z + 1) ^ k * Work.Spaces.pzIter k
      (Work.Spaces.DthIter j (fun z θ => a θ * b z)) z θ
      * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * B
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 le_rfl)
  have h1 : Work.Spaces.DthIter j (fun z θ => a θ * b z)
      = fun z θ => (Work.Spaces.dthU^[j]) a θ * b z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp j a b z θ
  rw [h1, Work.Spaces.pzIter_decomp k ((Work.Spaces.dthU^[j]) a) b z θ]
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hden : (0 : ℝ) < α + Real.sin (2 * θ) := by linarith
  have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    div_nonneg (Real.rpow_nonneg hs0 _) hden.le
  have hsinw : (Real.sin (2 * θ)) ^ 2
      * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 := by
    have h := Work.FTS.Nonlinear.FstarPkg.sinWeight_le_one α (Real.sin (2 * θ)) hα hα1 hs0 hs1
    rwa [mul_div_assoc] at h
  rw [show (z + 1) ^ k * ((Work.Spaces.dthU^[j]) a θ * deriv^[k] b z)
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      = (Work.Spaces.dthU^[j]) a θ * ((z + 1) ^ k * deriv^[k] b z)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hw]
  calc |(Work.Spaces.dthU^[j]) a θ| * |(z + 1) ^ k * deriv^[k] b z|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ (C * (Real.sin (2 * θ)) ^ 2) * B
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
        refine mul_le_mul_of_nonneg_right ?_ hw
        exact mul_le_mul (hC θ) (hB z hz) (abs_nonneg _) (mul_nonneg hCnn (sq_nonneg _))
    _ = C * B * ((Real.sin (2 * θ)) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
    _ ≤ C * B * 1 := mul_le_mul_of_nonneg_left hsinw (mul_nonneg hCnn hBnn)
    _ = C * B := by ring

/-- `WlInfMem` of a separable product `a(θ)·b(z)` from a uniform angular bound on `a`, a
`sin(2θ)²`-bound on its `D_θ`-iterates and uniform weighted `z`-derivative bounds on `b`. -/
private theorem WlInfMem_sep {α : ℝ} {a b : ℝ → ℝ} {l : ℕ} {A C : ℝ} {Bf : ℕ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hCnn : 0 ≤ C)
    (hA : ∀ θ, |a θ| ≤ A)
    (hC : ∀ j, 1 ≤ j → j ≤ l → ∀ θ, |(Work.Spaces.dthU^[j]) a θ| ≤ C * Real.sin (2 * θ) ^ 2)
    (hB : ∀ k ≤ l, ∀ z, 0 ≤ z → |(z + 1) ^ k * deriv^[k] b z| ≤ Bf k) :
    Work.Spaces.WlInfMem α l (fun z θ => a θ * b z) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    exact supFinite_sep_radial (hA := hA) (hB := hB k hk)
  · intro j hj k hk hj1 hjk
    exact supFinite_sep_mixed (j := j) (k := k) (C := C) (B := Bf k) hα hα1 hCnn
      (hC j hj1 hj) (hB k hk)

/-! ## `SmoothOpen` of the atom -/

/-- `c₂(θ)·L₁₂(F_*)(z)` is `C^∞` on the open quadrant (it is the explicit separated product
`c₂(θ)·2α/(1+z)` there). -/
private theorem c2mL12Fstar_smoothOpen {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z) := by
  have hexp : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      ((fun p : ℝ × ℝ => Work.Construction.c2m p.2) *
        (fun p : ℝ × ℝ => 2 * α / (1 + p.1))) Work.FTS.EllipticEst.Q0
    refine ContDiffOn.mul ?_ ?_
    · have hc : ContDiff ℝ Work.Stability.smoothOrder
          (fun θ : ℝ => Work.Construction.c2m θ) := by
        rw [show (fun θ : ℝ => Work.Construction.c2m θ)
            = fun θ => Real.cos (2 * θ) - Real.sin θ ^ 2 from by
              funext θ; rw [Work.Construction.c2m_eq]]
        fun_prop
      exact hc.comp_contDiffOn contDiffOn_snd
    · have hden : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => 1 + p.1) Work.FTS.EllipticEst.Q0 := by fun_prop
      have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, 1 + p.1 ≠ 0 := by
        intro p hp
        have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
        linarith
      have hinv := hden.inv hne
      have hmul : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun p : ℝ × ℝ => (2 * α) * (1 + p.1)⁻¹) Work.FTS.EllipticEst.Q0 :=
        ContDiffOn.mul contDiffOn_const hinv
      refine hmul.congr ?_
      intro p _
      simp only [div_eq_mul_inv]
  refine ContDiffOn.congr hexp ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry]
  rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 (by linarith)]

/-! ## The `D_z`- and `D_θ`-slots of the atom

Both `D_zf` and `D_θf` are separable products on `(-1,∞) × ℝ`:

* `D_zf_α(z,θ) = c₂(θ)·(-2α·hKer z)` (since `L₁₂(F_*)` agrees with `2α/(1+z)` on `(-1,∞)`),
* `D_θf_α(z,θ) = (dthU c₂)(θ)·invH α z`.

`WlInfMem` (and the `𝒲`-norm) only depend on the values on the right half-plane
(`FstarPkg.WlInf_congr`), so the two membership statements reduce to `WlInfMem_sep` applied
to these separable products. -/

/-- `WlInfMem α 4` of `D_z(c₂·L₁₂(F_*))`. -/
private theorem c2mL12Fstar_Dz_WlInfMem {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z)) := by
  have hpt : ∀ z, -1 < z → ∀ θ,
      Work.Spaces.Dz (fun z θ => Work.Construction.c2m θ *
        Work.Construction.L12 (Work.Construction.Fstar α) z) z θ
      = Work.Construction.c2m θ * (-(2 * α) * Work.Spaces.hKer z) := by
    intro z hz θ
    show z * deriv (fun z' => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z') z
      = Work.Construction.c2m θ * (-(2 * α) * Work.Spaces.hKer z)
    rw [Work.Spaces.deriv_const_mul']
    have hder : deriv (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z
        = deriv (Work.FTS.Nonlinear.FstarPkg.invH α) z :=
      Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hz)
        fun z' hz' => Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH α hα hα1 hz')
    have hd : deriv (Work.FTS.Nonlinear.FstarPkg.invH α) z = -2 * α / (1 + z) ^ 2 := by
      show deriv (fun z : ℝ => 2 * α / (1 + z)) z = -2 * α / (1 + z) ^ 2
      exact deriv_invH α z (by linarith)
    rw [hder, hd]
    show z * (Work.Construction.c2m θ * (-2 * α / (1 + z) ^ 2))
      = Work.Construction.c2m θ * (-(2 * α) * (z / (1 + z) ^ 2))
    ring
  refine (Work.FTS.Nonlinear.FstarPkg.WlInf_congr (f := Work.Spaces.Dz (fun z θ =>
      Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z))
    (g := fun z θ => Work.Construction.c2m θ * (-(2 * α) * Work.Spaces.hKer z)) hpt α 4).2.mpr ?_
  refine WlInfMem_sep (a := Work.Construction.c2m)
    (b := fun z => -(2 * α) * Work.Spaces.hKer z) (l := 4) (A := 2) (C := 1000)
    (Bf := fun k => 2 * α * (k.factorial : ℝ) * (k + 1)) hα hα1 (by norm_num) ?_ ?_ ?_
  · exact Work.FTS.Nonlinear.FstarPkg.abs_c2m_le_two
  · intro j hj1 hj4 θ
    exact Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound j hj1 hj4 θ
  · intro k hk z hz
    have h := hKer_weighted_bound k z hz
    rw [deriv_iter_const_mul (-(2 * α)) k Work.Spaces.hKer]
    rw [show (z + 1) ^ k * ((-(2 * α)) * deriv^[k] Work.Spaces.hKer z)
        = (-(2 * α)) * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z) by ring]
    rw [abs_mul,
      show |(-(2 * α) : ℝ)| = 2 * α from by rw [abs_neg, abs_of_pos (by linarith : (0:ℝ) < 2 * α)]]
    calc 2 * α * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
        ≤ 2 * α * ((k.factorial : ℝ) * (k + 1)) :=
          mul_le_mul_of_nonneg_left h (by linarith)
      _ = 2 * α * (k.factorial : ℝ) * (k + 1) := by ring

/-- `WlInfMem α 4` of `D_θ(c₂·L₁₂(F_*))`. -/
private theorem c2mL12Fstar_Dth_WlInfMem {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (fun z θ => Work.Construction.c2m θ *
      Work.Construction.L12 (Work.Construction.Fstar α) z)) := by
  obtain ⟨C6, hC6pos, hC6⟩ := Work.FTS.StrongPersist.dthU_c2m_bound6
  have hpt : ∀ z, -1 < z → ∀ θ,
      Work.Spaces.Dth (fun z θ => Work.Construction.c2m θ *
        Work.Construction.L12 (Work.Construction.Fstar α) z) z θ
      = (Work.Spaces.dthU Work.Construction.c2m) θ * Work.FTS.Nonlinear.FstarPkg.invH α z := by
    intro z hz θ
    show Real.sin (2 * θ) * deriv (fun θ' => Work.Construction.c2m θ' *
      Work.Construction.L12 (Work.Construction.Fstar α) z) θ
      = (Work.Spaces.dthU Work.Construction.c2m) θ * Work.FTS.Nonlinear.FstarPkg.invH α z
    rw [show (fun θ' => Work.Construction.c2m θ' *
          Work.Construction.L12 (Work.Construction.Fstar α) z)
        = (fun θ' => Work.Construction.c2m θ' * Work.FTS.Nonlinear.FstarPkg.invH α z) from
        funext fun θ' => congrArg (fun y => Work.Construction.c2m θ' * y)
          (Work.FTS.Nonlinear.FstarPkg.eqOn_L12_invH α hα hα1 hz)]
    rw [Work.Spaces.deriv_mul_const']
    show Real.sin (2 * θ) * (deriv Work.Construction.c2m θ *
        Work.FTS.Nonlinear.FstarPkg.invH α z)
      = (Work.Spaces.dthU Work.Construction.c2m) θ * Work.FTS.Nonlinear.FstarPkg.invH α z
    rw [Work.Spaces.dthU_apply]
    ring
  refine (Work.FTS.Nonlinear.FstarPkg.WlInf_congr (f := Work.Spaces.Dth (fun z θ =>
      Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z))
    (g := fun z θ => (Work.Spaces.dthU Work.Construction.c2m) θ *
      Work.FTS.Nonlinear.FstarPkg.invH α z) hpt α 4).2.mpr ?_
  refine WlInfMem_sep (a := Work.Spaces.dthU Work.Construction.c2m)
    (b := Work.FTS.Nonlinear.FstarPkg.invH α) (l := 4) (A := 1000) (C := C6)
    (Bf := fun k => 2 * α * (k.factorial : ℝ)) hα hα1 hC6pos.le ?_ ?_ ?_
  · intro θ
    have h := Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound 1 le_rfl (by norm_num) θ
    have hsin : Real.sin (2 * θ) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (2 * θ), sq_nonneg (Real.cos (2 * θ))]
    have h1 : (Work.Spaces.dthU Work.Construction.c2m) θ
        = Work.Spaces.dthU^[1] Work.Construction.c2m θ := by rw [Function.iterate_one]
    rw [h1]
    calc |Work.Spaces.dthU^[1] Work.Construction.c2m θ|
        ≤ 1000 * Real.sin (2 * θ) ^ 2 := h
      _ ≤ 1000 * 1 := by nlinarith
      _ = 1000 := by ring
  · intro j hj1 hj4 θ
    have h := hC6 (j + 1) (by omega) (by omega) θ
    rw [show (Work.Spaces.dthU^[j]) (Work.Spaces.dthU Work.Construction.c2m)
        = Work.Spaces.dthU^[j+1] Work.Construction.c2m from
        (Function.iterate_succ_apply Work.Spaces.dthU j Work.Construction.c2m).symm]
    exact h
  · intro k hk z hz
    exact Work.FTS.Nonlinear.FstarPkg.c2mInv_radial α hα k z hz

/-- **The `W5` data of the fixed profile `c₂(θ)·L₁₂(F_*)(z)`** (note `L₁₂(F_*)(z) = 2α/(1+z)`,
`Work.Construction.L12_Fstar_eq`).  `W5 α F a` is `SmoothOpen` + `WlInfMem α 4` +
`WlInf α 4 (·) ≤ a` for `F`, `Dz F`, `Dth F`; the `F`-part is available from
`Work.FTS.StrongPersist.c2m_L12Fstar_W6` (which gives `WlInfMem α 6` with norm `≤ Cα`, hence the
level-4 data by monotonicity), so the new facts are `WlInfMem α 4` of
`Dz (c₂·L₁₂(F_*))` and of `Dth (c₂·L₁₂(F_*))`, plus their two `WlInf`-bounds.

Route.  On the open quadrant, `Dz (c₂·L₁₂(F_*)) = c₂ · Dz (L₁₂(F_*))` and
`Dth (c₂·L₁₂(F_*)) = (Dth c₂) · L₁₂(F_*)`.  After the Leibniz-type identities for `pzIter` and
`DthIter`, every slot of the two `WlInf α 4` sums is a product of a `DthIter`-iterate of `c₂`
(bounded by `Work.FTS.Nonlinear.Pieces.DthIter_c2m_le` / `Work.FTS.StrongPersist.dthU_c2m_bound6`)
with a `pzIter`-iterate of `z ↦ L₁₂(F_*)(z) = 2α/(1+z)` — an explicit rational function whose
`(z+1)^k ∂_z^k` are uniformly bounded — multiplied by the single weight
`sin(2θ)^{-α/5}/(α + sin 2θ)`; bound the slots directly and conclude with `Work.Spaces.supAbs_le`.
`a` may depend on `α`. -/
theorem W5C2mL12Fstar : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
    Work.FTS.StrongEps.H5.W5 α (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) a := by
  intro α hαIoc
  obtain ⟨hα, hα1⟩ := hαIoc
  obtain ⟨_, _, hFacts⟩ := Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
  have hFmem : Work.Spaces.WlInfMem α 4 (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) := (hFacts α hα hα1).1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) := c2mL12Fstar_smoothOpen hα hα1
  have hDzmem := c2mL12Fstar_Dz_WlInfMem hα hα1
  have hDthmem := c2mL12Fstar_Dth_WlInfMem hα hα1
  set A : ℝ := Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
    * Work.Construction.L12 (Work.Construction.Fstar α) z) with hAdef
  set B : ℝ := Work.Spaces.WlInf α 4 (Work.Spaces.Dz (fun z θ => Work.Construction.c2m θ
    * Work.Construction.L12 (Work.Construction.Fstar α) z)) with hBdef
  set C : ℝ := Work.Spaces.WlInf α 4 (Work.Spaces.Dth (fun z θ => Work.Construction.c2m θ
    * Work.Construction.L12 (Work.Construction.Fstar α) z)) with hCdef
  refine ⟨|A| + |B| + |C| + 1, by positivity, ?_⟩
  refine ⟨hsm, hFmem, ?_, hsm.Dz, hDzmem, ?_, hsm.Dth, hDthmem, ?_⟩
  · have h0 := le_abs_self A
    have h1 := abs_nonneg B
    have h2 := abs_nonneg C
    linarith
  · have h0 := le_abs_self B
    have h1 := abs_nonneg A
    have h2 := abs_nonneg C
    linarith
  · have h0 := le_abs_self C
    have h1 := abs_nonneg A
    have h2 := abs_nonneg B
    linarith

end Work.FTS.StrongEps.H5.Atoms
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.W5DthFstar =====
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

open Work.Spaces
open Work.FTS.Nonlinear.FstarPkg (Hz HB Hz_deriv_bound Hz_eq_mul_deriv)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The angular weight `sin(2θ)^{-α/5}/(α+sin 2θ)` of the `𝒲`-norm (the `Wt` of
`Work.FTS.Nonlinear.FstarPkg.DthAux`). -/
local notation "wθ" => Work.FTS.Nonlinear.FstarPkg.DthAux.Wt

/-! ## Separated products

Every function treated below is, on `z > -1`, a *separated product* `A(θ)·H(z)`: the angular
factor `A` is a `D_θ`-iterate of `Γ` (multiplied by a constant), and the radial factor `H` is
one of the explicit rational functions `hKer`, `Hz`.  The two slot sums of the `𝒲^{l,∞}`-norm
of such a product are then estimated by the two hypotheses `hA0`/`hAj` (angular) and `hH`
(radial), using `pzIter_decomp`/`DthIter_decomp` for the separation of variables. -/

/-- The universal constant of the separated-product estimate. -/
noncomputable def sepBnd (l : ℕ) (A0 : ℝ) (Aj B : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range (l + 1), A0 * B k)
    + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then Aj j * B k else 0)

/-- **The `𝒲^{l,∞}`-estimate for a separated product** `(z,θ) ↦ A θ · H z`.

If the angular factor `A` is bounded by `A0` on `Iθ`, if its `D_θ`-iterates satisfy the weighted
bounds `|D_θ^j A θ| · sin(2θ)^{-α/5}/(α+sin 2θ) ≤ Aj j`, and if the radial factor satisfies
`|(z+1)^k H^{(k)}(z)| ≤ B k` for `z ≥ 0`, then

`WlInfMem α l (A ⊗ H)` and `WlInf α l (A ⊗ H) ≤ sepBnd l A0 Aj B`.

This is `Work.FTS.Nonlinear.FstarPkg.WlInf_Gamma_radial` with the angular input `Γ`
(`Gam_bounds`, `dthU_Gam_le`, `Gam_mul_weight_le`) replaced by the two general hypotheses. -/
lemma WlInf_sep {α : ℝ} {l : ℕ} {A H : ℝ → ℝ} {A0 : ℝ} {Aj B : ℕ → ℝ}
    (hA0 : ∀ θ ∈ Iθ, |A θ| ≤ A0)
    (hAj : ∀ j : ℕ, 1 ≤ j → j ≤ l → ∀ θ ∈ Iθ, |dthU^[j] A θ * wθ α θ| ≤ Aj j)
    (hH : ∀ k : ℕ, k ≤ l → ∀ z : ℝ, 0 ≤ z → |(z + 1) ^ k * deriv^[k] H z| ≤ B k) :
    WlInfMem α l (fun z θ => A θ * H z) ∧
      WlInf α l (fun z θ => A θ * H z) ≤ sepBnd l A0 Aj B := by
  -- separation of variables for the two families of slots
  have hDth : ∀ j : ℕ, DthIter j (fun z θ => A θ * H z) = fun z θ => dthU^[j] A θ * H z := by
    intro j
    funext z θ
    exact DthIter_decomp j A H z θ
  have hpt1 : ∀ k : ℕ, k ≤ l → ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      |(z + 1) ^ k * pzIter k (fun z θ => A θ * H z) z θ| ≤ A0 * B k := by
    intro k hk z hz θ hθ
    rw [pzIter_decomp k A H z θ]
    rw [show (z + 1) ^ k * (A θ * deriv^[k] H z)
          = A θ * ((z + 1) ^ k * deriv^[k] H z) from by ring,
      abs_mul]
    exact mul_le_mul (hA0 θ hθ) (hH k hk z hz) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hA0 θ hθ))
  have hpt2 : ∀ j : ℕ, 1 ≤ j → ∀ k : ℕ, k + j ≤ l → ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      |(z + 1) ^ k * pzIter k (DthIter j (fun z θ => A θ * H z)) z θ
          * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ Aj j * B k := by
    intro j hj1 k hkj z hz θ hθ
    have hjl : j ≤ l := by omega
    have hkl : k ≤ l := by omega
    rw [hDth j, pzIter_decomp k (dthU^[j] A) H z θ]
    rw [show (z + 1) ^ k * (dthU^[j] A θ * deriv^[k] H z)
          * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
        = (dthU^[j] A θ * (Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
          * ((z + 1) ^ k * deriv^[k] H z) from by ring,
      abs_mul]
    exact mul_le_mul (hAj j hj1 hjl θ hθ) (hH k hkl z hz) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hAj j hj1 hjl θ hθ))
  constructor
  · rw [WlInfMem]
    exact ⟨fun k hk => Work.FTS.Nonlinear.FstarPkg.supFinite_of_pointwise_bound (hpt1 k hk),
      fun j hj k hk hj1 hjk =>
        Work.FTS.Nonlinear.FstarPkg.supFinite_of_pointwise_bound (hpt2 j hj1 k hjk)⟩
  · rw [WlInf, sepBnd]
    refine add_le_add ?_ ?_
    · refine Finset.sum_le_sum fun k hk => supAbs_le fun z hz θ hθ =>
        hpt1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) z hz θ hθ
    · refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
      by_cases h : 1 ≤ j ∧ k + j ≤ l
      · rw [if_pos h, if_pos h]
        exact supAbs_le fun z hz θ hθ => hpt2 j h.1 k h.2 z hz θ hθ
      · rw [if_neg h, if_neg h]

/-! ## The separated forms of the profiles -/

/-- `D_θF_*` is the separated product `((2α/c)·D_θΓ) ⊗ hKer`. -/
lemma DthFstar_sep {α : ℝ} :
    Work.Spaces.Dth (Work.Construction.Fstar α)
      = fun z θ => (2 * α / Work.Spaces.c α
          * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ) * Work.Spaces.hKer z := by
  rw [show Work.Spaces.Dth (Work.Construction.Fstar α)
      = Work.Spaces.DthIter 1 (Work.Construction.Fstar α) from rfl,
    Work.FTS.Nonlinear.FstarPkg.DthAux.Fstar_eq α]
  funext z θ
  rw [Work.Spaces.DthIter_decomp 1
      (fun t => 2 * α / Work.Spaces.c α * Work.Spaces.Gam α t) Work.Spaces.hKer z θ,
    Work.Spaces.dthU_iter_const_mul 1 (2 * α / Work.Spaces.c α)
      (fun t => Work.Spaces.Gam α t)]

/-- `D_θD_θF_*` is the separated product `((2α/c)·D_θ²Γ) ⊗ hKer`. -/
lemma DthDthFstar_sep {α : ℝ} :
    ∀ z : ℝ, -1 < z → ∀ θ : ℝ,
      Work.Spaces.DthIter 2 (Work.Construction.Fstar α) z θ
        = (2 * α / Work.Spaces.c α
            * Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ) * Work.Spaces.hKer z := by
  intro z hz θ
  rw [Work.FTS.Nonlinear.FstarPkg.DthAux.Fstar_eq α,
    Work.Spaces.DthIter_decomp 2
      (fun t => 2 * α / Work.Spaces.c α * Work.Spaces.Gam α t) Work.Spaces.hKer z θ,
    Work.Spaces.dthU_iter_const_mul 2 (2 * α / Work.Spaces.c α)
      (fun t => Work.Spaces.Gam α t)]

/-- `D_zD_θF_*` is the separated product `((α/c)·D_θΓ) ⊗ Hz` on `z > -1`. -/
lemma DzDthFstar_sep {α : ℝ} :
    ∀ z : ℝ, -1 < z → ∀ θ : ℝ,
      Work.Spaces.Dz (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ
        = (α / Work.Spaces.c α
            * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ) * Hz z := by
  intro z hz θ
  -- the `z`-slice of `D_θF_*` is a constant multiple of `hKer`
  have hslice : (fun z' : ℝ => Work.Spaces.Dth (Work.Construction.Fstar α) z' θ)
      = fun z' : ℝ => (2 * α / Work.Spaces.c α
          * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ) * Work.Spaces.hKer z' :=
    funext fun z' => congrFun (congrFun (DthFstar_sep (α := α)) z') θ
  show z * deriv (fun z' : ℝ => Work.Spaces.Dth (Work.Construction.Fstar α) z' θ) z
      = (α / Work.Spaces.c α
          * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ) * Hz z
  rw [hslice]
  have hd : DifferentiableAt ℝ Work.Spaces.hKer z := by
    have hz2 : (1 + z) ^ 2 ≠ 0 := by
      have h1 : (1 : ℝ) + z ≠ 0 := by linarith
      exact pow_ne_zero 2 h1
    have hden : DifferentiableAt ℝ (fun y : ℝ => (1 + y) ^ 2) z :=
      ((differentiableAt_const (1 : ℝ)).add differentiableAt_id).pow 2
    exact (differentiableAt_id (x := z)).div hden hz2
  rw [deriv_const_mul _ hd, Hz_eq_mul_deriv hz]
  ring

/-! ## The target -/

/-- **The `W5` data of the fixed profile `D_θF_*`.**  `W5 α F a` (defined in
`Submission/Work/FTS/StrongEps/H5/DataW.lean`) is the bundle `SmoothOpen` + `WlInfMem α 4` +
`WlInf α 4 (·) ≤ a` for `F`, `Dz F` and `Dth F`.

All nine facts are about the explicit profile `F_* α z θ = α·(Γ(θ)/c)·2z/(1+z)²` and its
`D_θ`/`D_z`-derivatives.  Known: `Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat` gives
`SmoothOpen` and `WlInfMem α 6` of `F_*`, `Dth F_*`, `Dz F_*` with norms `≤ Cα`, together with the
pointwise slot bounds `|mixed j i A z θ| ≤ C α (z/(1+z)²)·(if 1 ≤ i then sin(2θ)^{α/3} else 1)`
for `j + i ≤ 6` and `A` one of those three.

Concretely the new facts are `WlInfMem α 4 (Dz (Dth F_*))`, `WlInfMem α 4 (Dth (Dth F_*))` (with
`Dth (Dth F_*) = DthIter 2 F_*`) and the corresponding two `WlInf`-bounds.

Direct slot route (recommended): every slot occurring in `WlInf α 4` of these two derivative
functions is, after the elementary calculus identities
`pzIter k (Dz g) = z·pzIter (k+1) g + k·pzIter k g` and `DthIter j (Dz g) = Dz (DthIter j g)`,
a `pzIter`-iterate of `mixed b a F_*` with `a + b ≤ 6`, hence dominated pointwise by a constant
times the `fstarDat` slot bound; finish with `Work.Spaces.supAbs_le` and the definition of
`WlInfMem`/`WlInf`.  `a` may depend on `α`. -/
theorem W5DthFstar : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∃ a : ℝ, 0 < a ∧
    Work.FTS.StrongEps.H5.W5 α (Work.Spaces.Dth (Work.Construction.Fstar α)) a := by
  obtain ⟨C, hCpos, hdat⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
  obtain ⟨K, hKpos, hKgam⟩ := Work.FTS.StrongPersist.W6Aux.dthGamWeightLe7
  intro α hαIoc
  obtain ⟨hα, hα1⟩ := hαIoc
  obtain ⟨hsmF, hsmDth, hsmDz, hFmem, hFle, hDthmem, hDthle, hDzmem, hDzle, hslot⟩ :=
    hdat α ⟨hα, hα1⟩
  -- ### the level-`4` data of `D_θF_*`
  have hDthmem4 : WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    (WlInfMem_mono (α := α) (l := 6) (l' := 4) (by norm_num) hDthmem).1
  have hDthle4 : WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α :=
    le_trans (WlInfMem_mono (α := α) (l := 6) (l' := 4) (by norm_num) hDthmem).2 hDthle
  -- ### the two coefficient bounds
  have hc1 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef1 : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  have hcoef2 : |2 * α / Work.Spaces.c α| ≤ 20 * α :=
    Work.FTS.Nonlinear.FstarPkg.DthAux.Fstar_coef_leD' α hα hα1
  -- ### the angular factors
  set A1 : ℝ → ℝ := fun θ => α / Work.Spaces.c α
    * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ with hA1def
  set A2 : ℝ → ℝ := fun θ => 2 * α / Work.Spaces.c α
    * Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ with hA2def
  have hcomp1 : ∀ j : ℕ, Work.Spaces.dthU^[j]
        (Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t))
      = Work.Spaces.dthU^[j + 1] (fun t => Work.Spaces.Gam α t) :=
    fun j => (Function.iterate_add_apply Work.Spaces.dthU j 1
      (fun t => Work.Spaces.Gam α t)).symm
  have hcomp2 : ∀ j : ℕ, Work.Spaces.dthU^[j]
        (Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t))
      = Work.Spaces.dthU^[j + 2] (fun t => Work.Spaces.Gam α t) :=
    fun j => (Function.iterate_add_apply Work.Spaces.dthU j 2
      (fun t => Work.Spaces.Gam α t)).symm
  have hA1iter : ∀ (j : ℕ) (θ : ℝ), Work.Spaces.dthU^[j] A1 θ
      = α / Work.Spaces.c α
          * Work.Spaces.dthU^[j + 1] (fun t => Work.Spaces.Gam α t) θ := by
    intro j θ
    rw [hA1def, Work.Spaces.dthU_iter_const_mul j (α / Work.Spaces.c α)
      (Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t)), hcomp1 j]
  have hA2iter : ∀ (j : ℕ) (θ : ℝ), Work.Spaces.dthU^[j] A2 θ
      = 2 * α / Work.Spaces.c α
          * Work.Spaces.dthU^[j + 2] (fun t => Work.Spaces.Gam α t) θ := by
    intro j θ
    rw [hA2def, Work.Spaces.dthU_iter_const_mul j (2 * α / Work.Spaces.c α)
      (Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t)), hcomp2 j]
  -- ### the angular hypotheses
  have hA1_0 : ∀ θ ∈ Iθ, |A1 θ| ≤ 10 * α * (α * Work.Spaces.tBound 0 0) := by
    intro θ hθ
    have hgoal : |α / Work.Spaces.c α
        * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ 10 * α * (α * Work.Spaces.tBound 0 0) := by
      rw [abs_mul]
      have h1 := Work.Spaces.dthU_Gam_le 1 (by norm_num) α hα hα1 θ hθ
      have h2 := Work.Spaces.Gam_bounds α θ hα hθ
      calc |α / Work.Spaces.c α| * |Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
          ≤ (10 * α) * (α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ) :=
            mul_le_mul hcoef1 h1 (abs_nonneg _) (by positivity)
        _ ≤ (10 * α) * (α * Work.Spaces.tBound 0 0) := by
            have ht : 0 ≤ α * Work.Spaces.tBound 0 0 :=
              mul_nonneg hα.le (Work.Spaces.tBound_nonneg 0 0)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ
                ≤ α * Work.Spaces.tBound 0 0 * 1 :=
                  mul_le_mul_of_nonneg_left h2.2 ht
              _ = α * Work.Spaces.tBound 0 0 := by ring
        _ = 10 * α * (α * Work.Spaces.tBound 0 0) := by ring
    simpa only [hA1def] using hgoal
  have hA1_j : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ θ ∈ Iθ,
      |Work.Spaces.dthU^[j] A1 θ * wθ α θ| ≤ 10 * α * (K * α) := by
    intro j hj1 hj4 θ hθ
    have hw := Work.FTS.Nonlinear.FstarPkg.DthAux.Wt_nonneg hα hθ
    have hg := hKgam (j + 1) (by omega) (by omega) α hα hα1 θ hθ
    have h2 : |Work.Spaces.dthU^[j + 1] (fun t => Work.Spaces.Gam α t) θ * wθ α θ|
        ≤ K * α := by
      rw [abs_mul, abs_of_nonneg hw]
      exact hg
    rw [show Work.Spaces.dthU^[j] A1 θ * wθ α θ
        = (α / Work.Spaces.c α) * (Work.Spaces.dthU^[j + 1]
            (fun t => Work.Spaces.Gam α t) θ * wθ α θ) from by
          rw [hA1iter j θ]; ring,
      abs_mul]
    exact mul_le_mul hcoef1 h2 (abs_nonneg _) (by positivity)
  have hA2_0 : ∀ θ ∈ Iθ, |A2 θ| ≤ 20 * α * (α * Work.Spaces.tBound 1 0) := by
    intro θ hθ
    have hgoal : |2 * α / Work.Spaces.c α
        * Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ|
        ≤ 20 * α * (α * Work.Spaces.tBound 1 0) := by
      rw [abs_mul]
      have h1 := Work.Spaces.dthU_Gam_le 2 (by norm_num) α hα hα1 θ hθ
      have h2 := Work.Spaces.Gam_bounds α θ hα hθ
      calc |2 * α / Work.Spaces.c α| * |Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ|
          ≤ (20 * α) * (α * Work.Spaces.tBound 1 0 * Work.Spaces.Gam α θ) :=
            mul_le_mul hcoef2 h1 (abs_nonneg _) (by positivity)
        _ ≤ (20 * α) * (α * Work.Spaces.tBound 1 0) := by
            have ht : 0 ≤ α * Work.Spaces.tBound 1 0 :=
              mul_nonneg hα.le (Work.Spaces.tBound_nonneg 1 0)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc α * Work.Spaces.tBound 1 0 * Work.Spaces.Gam α θ
                ≤ α * Work.Spaces.tBound 1 0 * 1 :=
                  mul_le_mul_of_nonneg_left h2.2 ht
              _ = α * Work.Spaces.tBound 1 0 := by ring
        _ = 20 * α * (α * Work.Spaces.tBound 1 0) := by ring
    simpa only [hA2def] using hgoal
  have hA2_j : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ θ ∈ Iθ,
      |Work.Spaces.dthU^[j] A2 θ * wθ α θ| ≤ 20 * α * (K * α) := by
    intro j hj1 hj4 θ hθ
    have hw := Work.FTS.Nonlinear.FstarPkg.DthAux.Wt_nonneg hα hθ
    have hg := hKgam (j + 2) (by omega) (by omega) α hα hα1 θ hθ
    have h2 : |Work.Spaces.dthU^[j + 2] (fun t => Work.Spaces.Gam α t) θ * wθ α θ|
        ≤ K * α := by
      rw [abs_mul, abs_of_nonneg hw]
      exact hg
    rw [show Work.Spaces.dthU^[j] A2 θ * wθ α θ
        = (2 * α / Work.Spaces.c α) * (Work.Spaces.dthU^[j + 2]
            (fun t => Work.Spaces.Gam α t) θ * wθ α θ) from by
          rw [hA2iter j θ]; ring,
      abs_mul]
    exact mul_le_mul hcoef2 h2 (abs_nonneg _) (by positivity)
  -- ### the two separated-product estimates
  set sb1 : ℝ := sepBnd 4 (10 * α * (α * Work.Spaces.tBound 0 0))
    (fun _ => 10 * α * (K * α)) HB with hsb1
  set sb2 : ℝ := sepBnd 4 (20 * α * (α * Work.Spaces.tBound 1 0))
    (fun _ => 20 * α * (K * α)) (fun k => (k.factorial : ℝ) * (k + 1)) with hsb2
  have hsep1 : WlInfMem α 4 (fun z θ => A1 θ * Hz z) ∧
      WlInf α 4 (fun z θ => A1 θ * Hz z) ≤ sb1 := by
    rw [hsb1]
    exact WlInf_sep hA1_0 hA1_j (fun k _ z hz => Hz_deriv_bound k z hz)
  have hsep2 : WlInfMem α 4 (fun z θ => A2 θ * Work.Spaces.hKer z) ∧
      WlInf α 4 (fun z θ => A2 θ * Work.Spaces.hKer z) ≤ sb2 := by
    rw [hsb2]
    exact WlInf_sep hA2_0 hA2_j (fun k _ z hz => Work.Spaces.pzIter_hKer_bound k z hz)
  -- ### transfer along the separated forms
  have hcongr1 := Work.FTS.Nonlinear.FstarPkg.WlInf_congr (α := α) (l := 4)
    (f := Work.Spaces.Dz (Work.Spaces.Dth (Work.Construction.Fstar α)))
    (g := fun z θ => A1 θ * Hz z)
    (fun z hz θ => DzDthFstar_sep (α := α) z hz θ)
  have hcongr2 := Work.FTS.Nonlinear.FstarPkg.WlInf_congr (α := α) (l := 4)
    (f := Work.Spaces.DthIter 2 (Work.Construction.Fstar α))
    (g := fun z θ => A2 θ * Work.Spaces.hKer z)
    (fun z hz θ => DthDthFstar_sep (α := α) z hz θ)
  -- ### the constant
  refine ⟨max 1 (max (C * α) (max sb1 sb2)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  refine ⟨hsmDth, hDthmem4, ?_, hsmDth.Dz, hcongr1.2.mpr hsep1.1, ?_,
    hsmDth.Dth, hcongr2.2.mpr hsep2.1, ?_⟩
  · calc WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α := hDthle4
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_left (C * α) (max sb1 sb2))
            (le_max_right 1 (max (C * α) (max sb1 sb2)))
  · calc WlInf α 4 (Work.Spaces.Dz (Work.Spaces.Dth (Work.Construction.Fstar α)))
        = WlInf α 4 (fun z θ => A1 θ * Hz z) := hcongr1.1
      _ ≤ sb1 := hsep1.2
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_left sb1 sb2)
            (le_trans (le_max_right (C * α) (max sb1 sb2))
              (le_max_right 1 (max (C * α) (max sb1 sb2))))
  · calc WlInf α 4 (Work.Spaces.Dth (Work.Spaces.Dth (Work.Construction.Fstar α)))
        = WlInf α 4 (fun z θ => A2 θ * Work.Spaces.hKer z) := hcongr2.1
      _ ≤ sb2 := hsep2.2
      _ ≤ max 1 (max (C * α) (max sb1 sb2)) :=
          le_trans (le_max_right sb1 sb2)
            (le_trans (le_max_right (C * α) (max sb1 sb2))
              (le_max_right 1 (max (C * α) (max sb1 sb2))))

end Work.FTS.StrongEps.H5.Atoms
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.ProdWrappers5 =====
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

/-- **The level-`5` product of two `ℋ⁵`-honest factors.** -/
theorem prodHH5 {α Cprod : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCprod : 0 < Cprod)
    (hfield : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    {C G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : Work.FTS.VocabO.HQo α 5 C) (hCb : Work.Spaces.HkNorm α 5 C ≤ a)
    (hG : Work.FTS.VocabO.HQo α 5 G) (hGb : Work.Spaces.HkNorm α 5 G ≤ b) :
    Work.Spaces.HkMem α 5 (fun z θ => c * (C z θ * G z θ)) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => c * (C z θ * G z θ))
        ≤ |c| * (3 * (Cprod * α ^ (-(1 / 2 : ℝ)) * a * b)) :=
  L5_mul (α := α) (Cprod := Cprod) (c := c) (a := a) (b := b) hα hα1 hCprod hfield ha hb
    (L5_of_HQo5 hα hC hCb) (L5_of_HQo5 hα hG hGb)

/-- **The level-`5` product of a `𝒲^{5,∞}`-priced factor with an `ℋ⁵`-honest factor.** -/
theorem prodWH5 {α Cw : ℝ} (hα : 0 < α) (hCw : 0 < Cw)
    (hfield : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 5 f →
      Work.FTS.VocabO.HQo α 5 g →
      Work.Spaces.HkMem α 5 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 5 f * Work.Spaces.HkNorm α 5 g)
    {F G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F) (hFw : Work.Spaces.WlInfMem α 5 F)
    (hFb : Work.Spaces.WlInf α 5 F ≤ a) (hG : Work.FTS.VocabO.HQo α 5 G)
    (hGb : Work.Spaces.HkNorm α 5 G ≤ b) :
    Work.Spaces.HkMem α 5 (fun z θ => c * (F z θ * G z θ)) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => c * (F z θ * G z θ))
        ≤ |c| * (Cw * α ^ (-(1 / 2 : ℝ)) * a * b) := by
  obtain ⟨hmem, hbd⟩ := hfield F G hFsm hFw hG
  have hAr : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 5 F := Work.Spaces.WlInf_nonneg α 5 F hFw
  have hXnG : 0 ≤ Work.Spaces.HkNorm α 5 G := Work.Spaces.HkNorm_nonneg α 5 G
  set P : ℝ := Cw * α ^ (-(1 / 2 : ℝ)) * a * b with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact mul_nonneg (mul_nonneg hAr ha) hb
  have hXn : Work.Spaces.HkNorm α 5 (fun z θ => F z θ * G z θ) ≤ P :=
    le_trans hbd (Pd_le hAr ha hb hFb hGb hWnn hXnG)
  refine ⟨Work.FTS.LocData.HkMem_const_mul α 5 c hmem, ?_⟩
  have hsq : Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))
      = c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ) :=
    Work.FTS.StrongEps.HkSq_const_mul α 5 c (fun z θ => F z θ * G z θ)
  have hbd2 : c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ) ≤ (|c| * P) ^ 2 := by
    have h1 : Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ) ≤ P ^ 2 := by
      have hsqrt : Work.Spaces.HkNorm α 5 (fun z θ => F z θ * G z θ)
          = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ)) := rfl
      rw [hsqrt] at hXn
      calc Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ)
          = (Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ))) ^ 2 :=
            (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 5 _)).symm
        _ ≤ P ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hXn 2
    calc c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ)
        ≤ c ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
      _ = (|c| * P) ^ 2 := by
          rw [← sq_abs c]
          ring
  calc Work.Spaces.HkNorm α 5 (fun z θ => c * (F z θ * G z θ))
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => c * (F z θ * G z θ))) := rfl
    _ = Real.sqrt (c ^ 2 * Work.Spaces.HkSq α 5 (fun z θ => F z θ * G z θ)) := by rw [hsq]
    _ ≤ Real.sqrt ((|c| * P) ^ 2) := Real.sqrt_le_sqrt hbd2
    _ = |c| * P := Real.sqrt_sq (by positivity)
    _ = |c| * (Cw * α ^ (-(1 / 2 : ℝ)) * a * b) := by rw [hPdef]

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.E2Facts =====
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

set_option autoImplicit false

/-- `Ê₂ h` as the product of the bounded radial profile `z/(1+z)²` with `2h + 3D_θh`. -/
theorem E2hat_eq_prod (h : Fn) (z θ : ℝ) :
    Work.FTS.CoercivityFix.E2hat h z θ
      = (z / (1 + z) ^ 2) * (2 * h z θ + 3 * Work.Spaces.Dth h z θ) := by
  rw [Work.FTS.CoercivityFix.E2hat_eq]
  ring

/-- The profile `z ↦ z/(1+z)²` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_zdiv (n : ℕ) :
    ContDiffOn ℝ n (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi (-1)) := by
  have hden : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  exact contDiffOn_id.div hden (fun z hz => by
    simp only [Set.mem_Ioi] at hz
    exact pow_ne_zero 2 (by linarith))

/-- `2h + 3D_θh` is smooth on the open quadrant whenever `h` is. -/
theorem smoothOpen_two_mul_add (h : Fn) (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) :=
  Work.FTS.EllipticEst.smoothOpen_add
    (Work.FTS.StrongPersist.linMem_const_mul 2 hs)
    (Work.FTS.StrongPersist.linMem_const_mul 3 (hs.Dth))

/-- `Ê₂ h` is smooth on the open quadrant whenever `h` is. -/
theorem smoothOpen_E2hat {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.E2hat h) := by
  have hprod : Work.FTS.CoercivityFix.E2hat h
      = fun z θ => (fun z : ℝ => z / (1 + z) ^ 2) z
          * (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) z θ := by
    funext z θ
    exact E2hat_eq_prod h z θ
  rw [hprod]
  exact Work.FTS.StrongPersist.linMem_mul
    (Work.FTS.StrongPersist.linMem_radial
      (contDiffOn_iff_forall_nat_le.mpr (fun n _ => contDiffOn_zdiv n)))
    (smoothOpen_two_mul_add h hs)

/-- A constant multiple of a smooth-open profile is smooth-open. -/
theorem smoothOpen_const_mul_h (c : ℝ) {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * h z θ) :=
  Work.FTS.StrongPersist.linMem_const_mul c hs

/-- **Pointwise integrand domination for `Ê₂`.** -/
theorem E2hat_HkIntegrand_le {m : ℕ} (hm : m ≤ 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), -(1 / 10 : ℝ) ≤ α → ∀ h : Fn,
      Work.FTS.EllipticEst.SmoothOpen h →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α m (Work.FTS.CoercivityFix.E2hat h) z θ
          ≤ C * Work.Spaces.HkIntegrand α (m + 1) h z θ := by
  obtain ⟨K, hK, hKb⟩ := Zop_zdiv_bound
  refine ⟨Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 * 26 + 1, by
    have h1 : 0 < Work.FTS.StrongPersist.L3Aux.zmulConst m :=
      Work.FTS.StrongPersist.L3Aux.zmulConst_pos m
    have h2 : 0 < (1 + K) ^ 2 := by positivity
    have h3 : 0 < Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 * 26 :=
      mul_pos (mul_pos h1 h2) (by norm_num)
    linarith, ?_⟩
  intro α hα h hs z hz θ hθ
  have hK0 : 0 ≤ K := le_of_lt hK
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
  have hθIθ : θ ∈ Work.Spaces.Iθ := by
    simp only [Work.Spaces.Iθ, Set.mem_Icc]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hprod : Work.FTS.CoercivityFix.E2hat h
      = fun z θ => (fun z : ℝ => z / (1 + z) ^ 2) z
          * (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) z θ := by
    funext z θ; exact E2hat_eq_prod h z θ
  rw [hprod]
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * h z θ) :=
    smoothOpen_const_mul_h 2 hs
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 3 * Work.Spaces.Dth h z θ) :=
    smoothOpen_const_mul_h 3 hs.Dth
  have hzm := Work.FTS.StrongPersist.L3Aux.zmul_open α m
    (fun z : ℝ => z / (1 + z) ^ 2) (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ)
    hK0 (fun b hb z hz' => le_trans (hKb b (by omega) z (le_of_lt hz')) le_rfl)
    (contDiffOn_iff_forall_nat_le.mpr (fun n _ => contDiffOn_zdiv n))
    (smoothOpen_two_mul_add h hs) z hz θ hθ
  have hadd := Work.FTS.EllipticEst.HkIntegrand_add_le_open α m
    (f := fun z θ => 2 * h z θ) (g := fun z θ => 3 * Work.Spaces.Dth h z θ)
    hsm1 hsm2 hzIz hθIθ
  have hcm1 := Work.FTS.LocData.HkIntegrand_const_mul α m 2 h z θ
  have hcm2 := Work.FTS.LocData.HkIntegrand_const_mul α m 3 (Work.Spaces.Dth h) z θ
  have hdth := Work.FTS.CoercivityFix.E2Bound.HkIntegrand_Dth_le_ge α hα m h z θ hzIz hθIθ
  have hmono : Work.Spaces.HkIntegrand α m h z θ ≤ Work.Spaces.HkIntegrand α (m + 1) h z θ :=
    Work.FTS.StrongPersist.HkIntegrand_le_of_le α (Nat.le_succ m) h z θ
  have hnn : 0 ≤ Work.Spaces.HkIntegrand α (m + 1) h z θ :=
    Work.Spaces.HkIntegrand_nonneg α (m + 1) h z θ
  calc Work.Spaces.HkIntegrand α m
        ((fun z θ => (fun z : ℝ => z / (1 + z) ^ 2) z
          * (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) z θ)) z θ
      ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 *
          Work.Spaces.HkIntegrand α m (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) z θ :=
        hzm
    _ ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 * 26 *
          Work.Spaces.HkIntegrand α (m + 1) h z θ := by
        have h26 : Work.Spaces.HkIntegrand α m (fun z θ => 2 * h z θ + 3 * Work.Spaces.Dth h z θ) z θ
            ≤ 26 * Work.Spaces.HkIntegrand α (m + 1) h z θ := by
          have e1 : Work.Spaces.HkIntegrand α m (fun z θ => 2 * h z θ) z θ
              = 4 * Work.Spaces.HkIntegrand α m h z θ := by
            rw [hcm1]; ring
          have e2 : Work.Spaces.HkIntegrand α m (fun z θ => 3 * Work.Spaces.Dth h z θ) z θ
              = 9 * Work.Spaces.HkIntegrand α m (Work.Spaces.Dth h) z θ := by
            rw [hcm2]; ring
          rw [e1, e2] at hadd
          linarith [hadd, hmono, hdth, hnn,
            Work.Spaces.HkIntegrand_nonneg α m h z θ,
            Work.Spaces.HkIntegrand_nonneg α m (Work.Spaces.Dth h) z θ]
        have hC0 : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 :=
          mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos m).le (sq_nonneg _)
        nlinarith [h26, hC0, hnn]
    _ ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 * 26 + 1)
          * Work.Spaces.HkIntegrand α (m + 1) h z θ := by nlinarith [hnn]

/-! ## The integrated and membership forms -/

/-- **The `ℋ^m`-norm of the defect `Ê₂ h`**, in the integrated form used by the induction. -/
theorem HkSq_E2hat_le {m : ℕ} (hm : m ≤ 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), -(1 / 10 : ℝ) ≤ α → ∀ h : Fn,
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.HkMem α (m + 1) h →
        Work.Spaces.HkSq α m (Work.FTS.CoercivityFix.E2hat h)
          ≤ C * Work.Spaces.HkSq α (m + 1) h := by
  obtain ⟨C, hC, hpt⟩ := E2hat_HkIntegrand_le hm
  refine ⟨C, hC, fun α hα h hs hmem => ?_⟩
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  -- the outer comparison, a.e. in `z`, where the slice inequality holds
  have hout : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m
          (Work.FTS.CoercivityFix.E2hat h) z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) h z θ) := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos] with z hz
    have hinner : (∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α (m + 1) h z θ)
        = C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) h z θ) :=
      MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) C _
    rw [← hinner]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α m
        (Work.FTS.CoercivityFix.E2hat h) z θ)
      ((hmem.1 z (le_of_lt hz)).const_mul C) ?_
    have hIoo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo
    filter_upwards [hIoo] with θ hθ
    exact hpt α hα h hs z hz θ hθ
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.CoercivityFix.E2hat h) z θ)
    (hmem.2.const_mul C) hout) ?_
  exact le_of_eq (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iz) C
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) h z θ))

/-- **`ℋ^m`-membership of the defect `Ê₂ h`.** -/
theorem HkMem_E2hat (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) (hα0 : 0 < α) {m : ℕ} (hm : m ≤ 6)
    {h : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen h) (hmem : Work.Spaces.HkMem α (m + 1) h) :
    Work.Spaces.HkMem α m (Work.FTS.CoercivityFix.E2hat h) := by
  obtain ⟨C, hC, hpt⟩ := E2hat_HkIntegrand_le hm
  refine Work.FTS.LocData.HkMem_of_majorant α m
    (f := Work.FTS.CoercivityFix.E2hat h)
    (M := fun z θ => C * Work.Spaces.HkIntegrand α (m + 1) h z θ)
    ((Work.FTS.StrongPersist.q0Sm_of_smoothOpen (smoothOpen_E2hat hs) m).continuousOn_HkIntegrand α)
    ?_ ?_ ?_
  · intro z hz
    exact (hmem.1 z hz).const_mul C
  · have hI2 : MeasureTheory.IntegrableOn (fun z => C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α (m + 1) h z θ)) Work.Spaces.Iz := hmem.2.const_mul C
    refine hI2.congr (Filter.Eventually.of_forall fun z => ?_)
    exact (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) C
      (fun θ => Work.Spaces.HkIntegrand α (m + 1) h z θ)).symm
  · intro z hz θ hθ
    by_cases hz0 : z = 0
    · rw [hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
      exact mul_nonneg hC.le (Work.Spaces.HkIntegrand_nonneg α (m + 1) h 0 θ)
    · have hzpos : 0 < z := lt_of_le_of_ne (show (0 : ℝ) ≤ z from hz) (Ne.symm hz0)
      by_cases hsin : Real.sin (2 * θ) = 0
      · rw [Work.FTS.StrongPersist.HkIntegrand_eq_zero_of_sin_zero
          (α := α) hα0 (k := m) hsin]
        exact mul_nonneg hC.le (Work.Spaces.HkIntegrand_nonneg α (m + 1) h z θ)
      · have hsinpos : 0 < Real.sin (2 * θ) :=
          lt_of_le_of_ne (Work.Elliptic.sin_two_nonneg_of_mem hθ) (Ne.symm hsin)
        have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
          Work.FTS.CoercivityFix.Coer1.mem_Ioo_of_mem_Iθ_of_sin_pos hθ hsinpos
        exact hpt α hα h hs z hzpos θ hθIoo

end Work.FTS.StrongPersist.H6Aux
end
end
