import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.T3Q.Msurv_abs_le_Q
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.t1SlotTermZ
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut.tendsto_terms_cut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts.TendstoTermsCut.tendsto_terms_cut`

The four `k → ∞` limits of the doubly truncated `I₁` identity, assembled from
`AeI1Fts.TendstoTermsCut.tendsto_AB`, `tendsto_dchi`, `tendsto_Vsq` and `tendsto_sig1`
(module `...TendstoTermsCut.TTAuxLimit`), whose `II`-forms are definitionally the statements
below (with `dk k = 1/((k:ℝ)+1)`).
-/

namespace Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut


end Work.FTS.EllipticEst.AeI1Fts.TendstoTermsCut
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `χ_n ↑ 1` limit** of the cut-off chain: from the per-`n` inequality
`κ·Pcut u n ≤ Dcut u n + Trcut u n − 2η·Acut u n` (the output of `Deleg.PairLimit`), the target's
`Vfull`-form follows.  The transfer term is bounded by `2√⟨U,U⟩√⟨B,B⟩`
(`H2W.SlotA.IP_cw_le`) and its cutoff band vanishes by `chiDerivLimit`. -/
theorem mixedLimitBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
    (∀ n : ℕ,
      kap * Work.FTS.EllipticEst.AeColl.Pcut u n
        ≤ Work.FTS.EllipticEst.AeColl.Dcut u n + Work.FTS.EllipticEst.AeColl.Trcut u n
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n) →
    kap * Work.FTS.EllipticEst.AeColl.Vfull u
      ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
            (Work.Spaces.pthIter 2 u)
        + C * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                (Work.FTS.EllipticEst.AeColl.Uz u)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                  (Work.FTS.EllipticEst.AeColl.Uz u))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))) := by
  refine ⟨2, by norm_num, ?_⟩
  intro α u G hAe hU hcut
  have heta2 : (0 : ℝ) ≤ 2 * Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have hkap : 0 ≤ kap := by
    rw [kap]
    apply div_nonneg <;> rw [Work.Spaces.eta] <;> norm_num
  have hmAB := Work.FTS.EllipticEst.AeColl.IPMem_rad2_ang2 hAe
  have hmUU := Work.FTS.EllipticEst.AeColl.IPMem_grad_self hAe hU
  have hmBB := Work.FTS.EllipticEst.AeColl.IPMem_ang2_self hAe
  have hmUB := Work.FTS.EllipticEst.AeColl.IPMem_grad_ang2 hAe hU
  -- ## the limit of `Acut`
  have hAcut_t : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.Acut u n) Filter.atTop
      (nhds (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
        (Work.FTS.EllipticEst.AeColl.Uz u))) := by
    set GU : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.AeColl.Uz u z θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ with hGU
    have hinner : ∀ z : ℝ,
        (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * (Work.FTS.EllipticEst.AeColl.Uz u z θ)^2)
        = ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.AeColl.Uz u z θ)^2
            * Work.FTS.EllipticEst.AngSecond.sig θ := by
      intro z
      rw [MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := Real.pi / 2))]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [Work.FTS.EllipticEst.AeColl.sigθ_eq]
      ring
    have hstep : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ
          * Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
        = Work.FTS.EllipticEst.AeColl.wt z * GU z := by
      intro z
      have h1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ
          * Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
          = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.w2 z
              * (Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
                * Work.FTS.EllipticEst.AngSecond.sig θ) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
      rw [h1, MeasureTheory.integral_const_mul]
      simp only [hGU, Work.FTS.EllipticEst.AeColl.wt_eq]
      congr 1
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    have hAcut_eq : ∀ n : ℕ, Work.FTS.EllipticEst.AeColl.Acut u n
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z
            * (Work.FTS.EllipticEst.AeColl.wt z * GU z) := by
      intro n
      rw [Work.FTS.EllipticEst.AeColl.Acut]
      rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
      rw [← MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      simp only [hGU]
      rw [hinner z]
      ring
    have hIP_eq : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
          (Work.FTS.EllipticEst.AeColl.Uz u)
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AeColl.wt z * GU z := by
      rw [Work.FTS.EllipticEst.AngSecond.IP]
      rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      exact hstep z
    have hGUint : MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.AeColl.wt z * GU z)
        Work.Spaces.Iz := hmUU.2.congr (Filter.Eventually.of_forall hstep)
    rw [funext hAcut_eq, hIP_eq]
    exact Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cut_mul hGUint
  -- ## the limit of `Trcut`
  have hTrcut_t : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.Trcut u n) Filter.atTop
      (nhds (Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
        (Work.Spaces.pthIter 2 u))) := by
    have hYI : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AeColl.YI u) Work.Spaces.Iz :=
      Work.FTS.EllipticEst.AeColl.YI_integrable hmUB
    have hcwf_cont : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AeColl.cwf z)
        Work.Spaces.Iz := by
      have h := Work.FTS.EllipticEst.H2W.SlotA.continuousOn_cw
      simpa [Work.FTS.EllipticEst.AeColl.cwf, Work.FTS.EllipticEst.AngSecond.cw] using h
    have hpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Set.Ioi (0:ℝ) := by
      rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      have hne : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), z ≠ (0:ℝ) := by
        rw [MeasureTheory.ae_iff]
        simp
      filter_upwards [hne] with z hz hzI
      exact lt_of_le_of_ne hzI (Ne.symm hz)
    have hmain : Filter.Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.AeColl.cfun n z * Work.FTS.EllipticEst.AeColl.YI u z) Filter.atTop
        (nhds (∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.AeColl.cwf z * Work.FTS.EllipticEst.AeColl.YI u z)) := by
      obtain ⟨K, hKpos, hKbd, hKcut, hKd⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
      have hdom : MeasureTheory.Integrable
          (fun z => (K + 2) * ‖Work.FTS.EllipticEst.AeColl.YI u z‖)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        (hYI.norm).const_mul (K + 2)
      have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
          (fun z => Work.FTS.EllipticEst.AeColl.cfun n z * Work.FTS.EllipticEst.AeColl.YI u z)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        intro n
        have hd : ContinuousOn (fun z : ℝ => deriv (Work.FTS.EllipticEst.cut n) z * z
            + Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.cwf z)
            Work.Spaces.Iz :=
          ((((Work.FTS.EllipticEst.cut_contDiff n).continuous_deriv (by simp)).continuousOn.mul
              continuousOn_id).add
            (((Work.FTS.EllipticEst.cut_contDiff n).continuous).continuousOn.mul hcwf_cont))
        refine (hd.aestronglyMeasurable measurableSet_Ici).mul hYI.aestronglyMeasurable |>.congr ?_
        filter_upwards with z
        simp only [Work.FTS.EllipticEst.AeColl.cfun, Pi.mul_apply]
      have hbnd : ∀ n : ℕ, ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          ‖Work.FTS.EllipticEst.AeColl.cfun n z * Work.FTS.EllipticEst.AeColl.YI u z‖
            ≤ (K + 2) * ‖Work.FTS.EllipticEst.AeColl.YI u z‖ := by
        intro n
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (Work.FTS.EllipticEst.AeColl.abs_cfun_le (fun z => hKbd n z) hz) (abs_nonneg _)
      have hlim : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.cfun n z
              * Work.FTS.EllipticEst.AeColl.YI u z)
            Filter.atTop (nhds (Work.FTS.EllipticEst.AeColl.cwf z
              * Work.FTS.EllipticEst.AeColl.YI u z)) := by
        filter_upwards [hpos] with z hz
        have h1 : Filter.Tendsto (fun n : ℕ => deriv (Work.FTS.EllipticEst.cut n) z * z)
            Filter.atTop (nhds 0) := by
          have hh := hKd z
          refine hh.congr' (Filter.Eventually.of_forall (fun n => ?_))
          ring
        have h2 : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z)
            Filter.atTop (nhds 1) := hKcut z hz
        have h3 : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z
            * Work.FTS.EllipticEst.AeColl.cwf z) Filter.atTop
            (nhds (Work.FTS.EllipticEst.AeColl.cwf z)) := by
          simpa using h2.mul_const (Work.FTS.EllipticEst.AeColl.cwf z)
        have h4 := (h1.add h3).mul_const (Work.FTS.EllipticEst.AeColl.YI u z)
        simpa [Work.FTS.EllipticEst.AeColl.cfun, mul_add, add_mul] using h4
      exact MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (F := fun n z => Work.FTS.EllipticEst.AeColl.cfun n z * Work.FTS.EllipticEst.AeColl.YI u z)
        (f := fun z => Work.FTS.EllipticEst.AeColl.cwf z * Work.FTS.EllipticEst.AeColl.YI u z)
        (fun z => (K + 2) * ‖Work.FTS.EllipticEst.AeColl.YI u z‖) hmeas hdom hbnd hlim
    have hIPcw : Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
          (Work.Spaces.pthIter 2 u)
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AeColl.cwf z
            * Work.FTS.EllipticEst.AeColl.YI u z := by
      rw [Work.FTS.EllipticEst.AngSecond.IP]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      rw [Work.FTS.EllipticEst.AeColl.YI]
      have hpt : (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.Spaces.pthIter 2 u z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
          = fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.cw z
            * (Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.Spaces.pthIter 2 u z θ
              * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
        funext θ; ring
      rw [hpt, MeasureTheory.integral_const_mul]
      rfl
    have hTrcut_Iz : ∀ n : ℕ, Work.FTS.EllipticEst.AeColl.Trcut u n
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AeColl.cfun n z
            * Work.FTS.EllipticEst.AeColl.YI u z := by
      intro n
      rw [Work.FTS.EllipticEst.AeColl.Trcut_eq_integral u n]
      exact MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))
    rw [hIPcw]
    exact hmain.congr' (Filter.Eventually.of_forall (fun n => (hTrcut_Iz n).symm))
  -- ## the limit of `Dcut`
  have hDcut_t : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.Dcut u n) Filter.atTop
      (nhds (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
        (Work.Spaces.pthIter 2 u))) := Work.FTS.EllipticEst.AeColl.Dcut_tendsto hmAB
  -- ## the limit of the right-hand side
  have hRHS : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.Dcut u n
        + Work.FTS.EllipticEst.AeColl.Trcut u n
        - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n) Filter.atTop
      (nhds (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
              (Work.Spaces.pthIter 2 u)
          + Work.FTS.EllipticEst.AngSecond.IP
              (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
              (Work.Spaces.pthIter 2 u)
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AeColl.Uz u) (Work.FTS.EllipticEst.AeColl.Uz u))) :=
    ((hDcut_t.add hTrcut_t).sub (hAcut_t.const_mul (2 * Work.Spaces.eta)))
  -- ## nonnegativity of the right-hand side
  have hPcut_nn : ∀ n : ℕ, 0 ≤ Work.FTS.EllipticEst.AeColl.Pcut u n := by
    intro n
    rw [Work.FTS.EllipticEst.AeColl.Pcut]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun z hz => ?_)
    refine mul_nonneg (mul_nonneg (Work.FTS.EllipticEst.cut_nonneg n z) ?_) ?_
    · rw [Work.FTS.EllipticEst.AeColl.wt]; positivity
    · refine MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun θ hθ => ?_)
      exact mul_nonneg (Work.FTS.EllipticEst.AeColl.sigθ_nonneg_of_mem
        ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (sq_nonneg _)
  have hnonneg : ∀ n : ℕ, (0:ℝ) ≤ Work.FTS.EllipticEst.AeColl.Dcut u n
      + Work.FTS.EllipticEst.AeColl.Trcut u n
      - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n := by
    intro n
    have h1 := hcut n
    have h2 : 0 ≤ kap * Work.FTS.EllipticEst.AeColl.Pcut u n :=
      mul_nonneg hkap (hPcut_nn n)
    linarith
  have hlim0 : (0:ℝ) ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
          (Work.Spaces.pthIter 2 u)
      + Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
          (Work.Spaces.pthIter 2 u)
      - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngSecond.IP
          (Work.FTS.EllipticEst.AeColl.Uz u) (Work.FTS.EllipticEst.AeColl.Uz u) :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hRHS hnonneg
  -- ## the transfer bound, and the resulting lower bound on the pairing
  have hcwle : Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
        (Work.Spaces.pthIter 2 u)
      ≤ 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
            (Work.FTS.EllipticEst.AeColl.Uz u))
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
            (Work.Spaces.pthIter 2 u)) :=
    Work.FTS.EllipticEst.H2W.SlotA.IP_cw_le _ _ hmUU hmBB hmUB
  have hUU0 : 0 ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
      (Work.FTS.EllipticEst.AeColl.Uz u) := Work.FTS.EllipticEst.AngSecond.IP_self_nonneg _
  have hD_lower : -(2 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
          (Work.FTS.EllipticEst.AeColl.Uz u)
        + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
              (Work.FTS.EllipticEst.AeColl.Uz u))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
              (Work.Spaces.pthIter 2 u))))
      ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
          (Work.Spaces.pthIter 2 u) := by
    have h2 : -(2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
            (Work.FTS.EllipticEst.AeColl.Uz u))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
              (Work.Spaces.pthIter 2 u)))
        ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
            (Work.Spaces.pthIter 2 u) := by
      nlinarith [hlim0, hcwle, hUU0, mul_nonneg heta2 hUU0,
        Real.sqrt_nonneg (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
          (Work.FTS.EllipticEst.AeColl.Uz u))]
    have hs : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
          (Work.FTS.EllipticEst.AeColl.Uz u))
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
            (Work.Spaces.pthIter 2 u))
        ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
            (Work.FTS.EllipticEst.AeColl.Uz u)
          + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
              (Work.FTS.EllipticEst.AeColl.Uz u))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                (Work.Spaces.pthIter 2 u)) := by linarith [hUU0]
    linarith [h2, hs]
  by_cases hint : MeasureTheory.Integrable
      (fun z => Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))
  · -- ## the honest case: `Pcut u n → Vfull u`
    have hGint : MeasureTheory.IntegrableOn
        (fun z => Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z)
        Work.Spaces.Iz := by
      show MeasureTheory.Integrable
        (fun z => Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz)
      rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
      rw [← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))]
      exact hint
    have hPcut_t : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.AeColl.Pcut u n)
        Filter.atTop (nhds (Work.FTS.EllipticEst.AeColl.Vfull u)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.cut n z
            * (Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z))
          Filter.atTop (nhds (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z)) :=
        Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cut_mul hGint
      have h2 : ∀ n : ℕ, Work.FTS.EllipticEst.AeColl.Pcut u n = ∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.cut n z
            * (Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z) := by
        intro n
        rw [Work.FTS.EllipticEst.AeColl.Pcut_eq_integral u n]
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))
      have h3 : Work.FTS.EllipticEst.AeColl.Vfull u = ∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.Gcut u z := by
        rw [Work.FTS.EllipticEst.AeColl.Vfull_eq_integral u]
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ)))
      rw [funext h2, h3]
      exact h1
    have hL : Filter.Tendsto (fun n : ℕ => kap * Work.FTS.EllipticEst.AeColl.Pcut u n)
        Filter.atTop (nhds (kap * Work.FTS.EllipticEst.AeColl.Vfull u)) :=
      hPcut_t.const_mul _
    have hle := le_of_tendsto_of_tendsto' hL hRHS hcut
    have hBB0 : 0 ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
        (Work.Spaces.pthIter 2 u) := Work.FTS.EllipticEst.AngSecond.IP_self_nonneg _
    have hfin : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
            (Work.Spaces.pthIter 2 u)
        + Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AeColl.Uz u z θ)
            (Work.Spaces.pthIter 2 u)
        - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AeColl.Uz u) (Work.FTS.EllipticEst.AeColl.Uz u)
        ≤ Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
            (Work.Spaces.pthIter 2 u)
          + 2 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                (Work.FTS.EllipticEst.AeColl.Uz u)
              + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                    (Work.FTS.EllipticEst.AeColl.Uz u))
                * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))) := by
      have h3 : 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
              (Work.FTS.EllipticEst.AeColl.Uz u))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                (Work.Spaces.pthIter 2 u))
          ≤ 2 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                (Work.FTS.EllipticEst.AeColl.Uz u)
              + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
                    (Work.FTS.EllipticEst.AeColl.Uz u))
                * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))) := by linarith [hUU0]
      have h4 : 0 ≤ 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AngSecond.IP
          (Work.FTS.EllipticEst.AeColl.Uz u) (Work.FTS.EllipticEst.AeColl.Uz u) :=
        mul_nonneg heta2 hUU0
      linarith [hcwle, h3, h4]
    linarith [hle, hfin]
  · -- ## the junk case: `Vfull u = 0`
    have hzero : Work.FTS.EllipticEst.AeColl.Vfull u = 0 := by
      rw [Work.FTS.EllipticEst.AeColl.Vfull_eq_integral]
      exact MeasureTheory.integral_undef hint
    rw [hzero, mul_zero]
    linarith [hD_lower]

end

end Work.FTS.EllipticEst.Deleg
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.HkIntegrand_sub_psiCut_le_sharp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

open scoped Real Topology
open MeasureTheory Set Filter

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1600000


end Work.FTS.GalBasis.cc.Subcut
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarPkgo2Aux.FbEV =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.StarPkgo2Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The constant supplied by `CoreAux.Fb_EV_bound` -/

/-- The constant of `CoreAux.Fb_EV_bound`, made explicit. -/
private noncomputable def FbEVc : ℝ := Classical.choose CoreAux.Fb_EV_bound

private theorem FbEVc_pos : 0 < FbEVc := (Classical.choose_spec CoreAux.Fb_EV_bound).1

/-- The shifted bound of `CoreAux.Fb_EV_bound` with the constant `FbEVc` made explicit. -/
private theorem FbEVc_spec (K A : ℝ) (Y : ℝ → ℝ → ℝ) (hK : 0 ≤ K) (hA : 1 ≤ A)
    (hYs : EllipticEst.SmoothOpen Y) (hphi : F0 6 A CoreAux.EVphi)
    (hsin : F0 6 A CoreAux.EVsin) (hrho : F0 6 A CoreAux.EVrho)
    (hY : Fb 6 (A * (K + 1)) Y) :
    Fb 4 (FbEVc * A ^ 4 * (K + 1)) (EVz Y) ∧ Fb 4 (FbEVc * A ^ 4 * (K + 1)) (EV Y) :=
  (Classical.choose_spec CoreAux.Fb_EV_bound).2 K A Y hK hA hYs hphi hsin hrho hY

/-! ## The flat classes are homogeneous -/

/-- **Scalar multiples in `Fb`.**  If `f` has flat constant `K`, then `c·f` has flat
constant `|c|·K`. -/
private theorem Fb_const_mul {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (c : ℝ) (h : Fb n K f) :
    Fb n (|c| * K) (fun z θ => c * f z θ) := by
  refine ⟨CoreAux.F0_const_mul c h.f0, ?_⟩
  rw [CoreAux.pth_const_mul c f]
  exact CoreAux.F0_const_mul c h.fd

/-- **Division by a non-zero constant in `F0`.**  If the scalar multiple `c·f` has flat
constant `D`, then `f` has flat constant `D/|c|`: every `pzIter`/`DthIter` is linear over the
constants. -/
private theorem F0_div_const {n : ℕ} {D : ℝ} {f : ℝ → ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : F0 n D (fun z θ => c * f z θ)) : F0 n (D / |c|) f := by
  have hcpos : 0 < |c| := abs_pos.mpr hc
  intro k i hki z θ hz hθ hθ'
  have h1 := h k i hki z θ hz hθ hθ'
  simp only [CoreAux.DthIter_const_mul, CoreAux.pzIter_const_mul] at h1
  have hkey : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ| * |c| ≤ D := by
    rw [← abs_mul]
    rw [show ((z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ) * c
        = (z + 1) ^ k * (c * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ) from by ring]
    exact h1
  rw [le_div_iff₀ hcpos]
  exact hkey

/-- **Division by a non-zero constant in `Fb`.** -/
private theorem Fb_div_const {n : ℕ} {D : ℝ} {f : ℝ → ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : Fb n D (fun z θ => c * f z θ)) : Fb n (D / |c|) f := by
  have hp : F0 n D (Work.Spaces.pth (fun z θ => c * f z θ)) := h.fd
  rw [CoreAux.pth_const_mul c f] at hp
  exact ⟨F0_div_const hc h.f0, F0_div_const hc hp⟩

/-- **Congruence of the pair `Fb` on the open quadrant.** -/
private theorem Fb_congr {n : ℕ} {K : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) (hg : Fb n K g) :
    Fb n K f :=
  ⟨CoreAux.F0_congr h hg.f0, CoreAux.F0_congr (CoreAux.pth_congr_Q0 h) hg.fd⟩

/-- **A bound whose constant can be made arbitrarily small is a bound with constant `0`.** -/
private theorem Fb_zero_of_forall_pos {n : ℕ} {D : ℝ} {f : ℝ → ℝ → ℝ} (hD : 0 < D)
    (h : ∀ c : ℝ, 0 < c → Fb n (D / c) f) : Fb n 0 f := by
  have hkey : ∀ X : ℝ, (∀ c : ℝ, 0 < c → X ≤ D / c) → X ≤ 0 := by
    intro X hX
    by_contra hcon
    rw [not_le] at hcon
    have hXpos : 0 < X := hcon
    have hXne : X ≠ 0 := ne_of_gt hXpos
    have hden : (0 : ℝ) < D / X + 1 := by positivity
    have h2 : D / (D / X + 1) < X := by
      rw [div_lt_iff₀ hden]
      have hexp : X * (D / X + 1) = D + X := by field_simp
      rw [hexp]
      linarith
    have h1 : X ≤ D / (D / X + 1) := hX (D / X + 1) hden
    linarith
  exact ⟨fun k i hki z θ hz hθ hθ' => hkey _ fun c hc => (h c hc).f0 k i hki z θ hz hθ hθ',
    fun k i hki z θ hz hθ hθ' => hkey _ fun c hc => (h c hc).fd k i hki z θ hz hθ hθ'⟩

/-! ## The scaling device -/

/-- **The `EV`-bounds with the flat constant of the hypothesis scaled.**  For every `c > 0`
with `c(A K) ≤ A(K+1)` one gets the shifted bound of an earlier chapter applied to the
*unscaled* datum `Y` at constant `FbEVc·A⁴(K+1)/c`: scale `Y` up by `c`, apply the shifted
bound, and divide the constant back down. -/
private theorem Fb_EV_scaled {A K : ℝ} {Y : ℝ → ℝ → ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hYs : EllipticEst.SmoothOpen Y) (hphi : F0 6 A CoreAux.EVphi)
    (hsin : F0 6 A CoreAux.EVsin) (hrho : F0 6 A CoreAux.EVrho) (hY : Fb 6 (A * K) Y)
    {c : ℝ} (hc : 0 < c) (hcK : c * (A * K) ≤ A * (K + 1)) :
    Fb 4 (FbEVc * A ^ 4 * (K + 1) / c) (EVz Y) ∧
      Fb 4 (FbEVc * A ^ 4 * (K + 1) / c) (EV Y) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  -- the scaled datum
  have hYc : Fb 6 (A * (K + 1)) (fun z θ => c * Y z θ) := by
    have h := Fb_const_mul c hY
    rw [abs_of_pos hc] at h
    exact h.mono le_rfl hcK
  have hsYc : EllipticEst.SmoothOpen (fun z θ => c * Y z θ) := CoreAux.SmoothOpen.const_mul hYs c
  have haux := FbEVc_spec K A (fun z θ => c * Y z θ) hK hA hsYc hphi hsin hrho hYc
  -- the two pointwise identities `field (c·Y) = c·(field Y)`
  have hzc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      EVz (fun z θ => c * Y z θ) z θ = c * EVz Y z θ := by
    intro z θ _ _ _
    have hp : Work.Spaces.pth (fun z θ => c * Y z θ) z θ = c * Work.Spaces.pth Y z θ :=
      congrFun (congrFun (CoreAux.pth_const_mul c Y) z) θ
    simp only [EVz, Tblk]
    rw [hp]
    ring
  have hevc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      EV (fun z θ => c * Y z θ) z θ = c * EV Y z θ := by
    intro z θ hz hθ hθ'
    simp only [EV]
    rw [hzc z θ hz hθ hθ']
    ring
  have h1 : Fb 4 (FbEVc * A ^ 4 * (K + 1)) (fun z θ => c * EVz Y z θ) :=
    Fb_congr (fun z θ hz hθ hθ' => (hzc z θ hz hθ hθ').symm) haux.1
  have h2 : Fb 4 (FbEVc * A ^ 4 * (K + 1)) (fun z θ => c * EV Y z θ) :=
    Fb_congr (fun z θ hz hθ hθ' => (hevc z θ hz hθ hθ').symm) haux.2
  exact ⟨by simpa [abs_of_pos hc] using Fb_div_const hcne h1,
    by simpa [abs_of_pos hc] using Fb_div_const hcne h2⟩

/-! ## The unshifted constant -/

/-- **The `EV`-bounds in the `K`-form.** -/
private theorem Fb_EV_lin {A K : ℝ} {Y : ℝ → ℝ → ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hYs : EllipticEst.SmoothOpen Y) (hphi : F0 6 A CoreAux.EVphi)
    (hsin : F0 6 A CoreAux.EVsin) (hrho : F0 6 A CoreAux.EVrho) (hY : Fb 6 (A * K) Y) :
    Fb 4 (FbEVc * A ^ 4 * K) (EVz Y) ∧ Fb 4 (FbEVc * A ^ 4 * K) (EV Y) := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · -- `K = 0`: the target constant is `0`, and the scaling device drives it there
    subst hK0
    have hD : (0 : ℝ) < FbEVc * A ^ 4 := by
      exact mul_pos FbEVc_pos (pow_pos (lt_of_lt_of_le zero_lt_one hA) 4)
    have key : ∀ c : ℝ, 0 < c → Fb 4 (FbEVc * A ^ 4 / c) (EVz Y) ∧
        Fb 4 (FbEVc * A ^ 4 / c) (EV Y) := by
      intro c hc
      have hcs := Fb_EV_scaled hA hK hYs hphi hsin hrho hY hc
        (by nlinarith [le_trans zero_le_one hA])
      simpa using hcs
    refine ⟨?_, ?_⟩
    · simpa using Fb_zero_of_forall_pos hD (fun c hc => (key c hc).1)
    · simpa using Fb_zero_of_forall_pos hD (fun c hc => (key c hc).2)
  · -- `K > 0`: scale by `c = (K+1)/K`, which turns the scaled constant into `C A⁴ K`
    have hKne : K ≠ 0 := ne_of_gt hKpos
    have hK1pos : (0 : ℝ) < K + 1 := by linarith
    have hK1ne : K + 1 ≠ 0 := ne_of_gt hK1pos
    have hcpos : (0 : ℝ) < (K + 1) / K := div_pos hK1pos hKpos
    have hcKeq : (K + 1) / K * (A * K) = A * (K + 1) := by
      field_simp
    have h := Fb_EV_scaled hA hK hYs hphi hsin hrho hY hcpos (le_of_eq hcKeq)
    have hconst : FbEVc * A ^ 4 * (K + 1) / ((K + 1) / K) = FbEVc * A ^ 4 * K := by
      field_simp
    rwa [hconst] at h

/-! ## The target -/

theorem FbEV : ∃ C : ℝ, 0 < C ∧ ∀ (α K A : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 1 ≤ A →
    Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) →
    Work.FTS.PhiStar.Fb 6 (A * K) Y →
    Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EVz Y) ∧
    Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EV Y) := by
  refine ⟨FbEVc + 1, by linarith [FbEVc_pos], ?_⟩
  intro α K A Y hα hK hA hYs hsinSq hphi hcos2 hsin2 hrho hrhoInv hY
  have hlin := Fb_EV_lin hA hK hYs hphi hsin2 hrho hY
  have hA4 : (0 : ℝ) ≤ A ^ 4 := pow_nonneg (le_trans zero_le_one hA) 4
  have hX : (0 : ℝ) ≤ FbEVc * A ^ 4 * K :=
    mul_nonneg (mul_nonneg FbEVc_pos.le hA4) hK
  have hle1 : FbEVc * A ^ 4 * K ≤ FbEVc * A ^ 4 * K * (α + 1) := by
    simpa using mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ α + 1) hX
  have hle2 : FbEVc * A ^ 4 * K * (α + 1) ≤ (FbEVc + 1) * A ^ 4 * K * (α + 1) := by
    have hα1 : (0 : ℝ) ≤ α + 1 := by linarith
    have hK4 : (0 : ℝ) ≤ A ^ 4 * K := mul_nonneg hA4 hK
    have h1 : FbEVc * (A ^ 4 * K) ≤ (FbEVc + 1) * (A ^ 4 * K) :=
      mul_le_mul_of_nonneg_right (by linarith) hK4
    calc FbEVc * A ^ 4 * K * (α + 1) = FbEVc * (A ^ 4 * K) * (α + 1) := by ring
      _ ≤ (FbEVc + 1) * (A ^ 4 * K) * (α + 1) := mul_le_mul_of_nonneg_right h1 hα1
      _ = (FbEVc + 1) * A ^ 4 * K * (α + 1) := by ring
  have hle : FbEVc * A ^ 4 * K ≤ (FbEVc + 1) * A ^ 4 * K * (α + 1) := hle1.trans hle2
  exact ⟨Fb.mono le_rfl hle hlin.1, Fb.mono le_rfl hle hlin.2⟩

end Work.FTS.PhiStar.StarPkgo2Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSq_Jeps_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-- **E1: the log-coordinate mollifier `J_ε` is bounded on the weighted spaces `ℋ^k` up to a
factor `e^{Cε}`.** -/
theorem HkSq_Jeps_le (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ f : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) →
        Work.Spaces.HkMem α k f → Work.Spaces.HkMem α k (Jeps ρ ε f) →
          Work.Spaces.HkSq α k (Jeps ρ ε f)
            ≤ Real.exp (C * ε) * Work.Spaces.HkSq α k f := by
  obtain ⟨cη, hcηpos, hWη0⟩ := HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγpos, hWγ0⟩ := HkSqAux.Wt_shift_le
  obtain ⟨δ, hδpos, hJac0⟩ := HkSqAux.logJac_shift_le
  refine ⟨4 * max cη cγ + 2 * δ, by positivity, ?_⟩
  intro α hα k ε hε _ f hf hF hFJ
  have hc0 : 0 ≤ max cη cγ := le_of_lt (lt_of_lt_of_le hcηpos (le_max_left _ _))
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2)) := by
    intro z θ hz hθ p
    refine (hWη0 z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact div_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2) := by
    intro z θ hz hθ p
    exact (hWγ0 α hα z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)))
  have hmain := HkSqAux.ofReal_HkSq_Jeps_le ρ hρ hα hε hf hF hFJ (c := max cη cγ) (δ := δ)
    hc0 (le_of_lt hδpos) hWη hWγ (fun s ζ p₁ p₂ => hJac0 s ζ p₁ p₂)
  have hconv : ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε)
        * Work.Spaces.HkSq α k f)
      = ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε))
        * ENNReal.ofReal (Work.Spaces.HkSq α k f) :=
    ENNReal.ofReal_mul (Real.exp_pos _).le
  rw [← hconv] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.exp_pos _).le (Work.Spaces.HkSq_nonneg α k f))).mp hmain

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsHkMem.AuxMeas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

namespace JepsHkMem

theorem restrict_Iz_eq : (MeasureTheory.volume.restrict Work.Spaces.Iz)
    = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show (Work.Spaces.Iz : Set ℝ) = Set.Ici 0 from rfl, Set.Ici_sdiff_Ioi, Set.Icc_self]
    exact measure_singleton 0
  · rw [show (Work.Spaces.Iz : Set ℝ) = Set.Ici 0 from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]

theorem restrict_Iθ_eq : (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    = MeasureTheory.volume.restrict (Set.Ioo 0 (π/2)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show (Work.Spaces.Iθ : Set ℝ) = Set.Icc 0 (π/2) from rfl,
      Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π/2)]
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)
  · rw [show (Work.Spaces.Iθ : Set ℝ) = Set.Icc 0 (π/2) from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]

/-- The complement of the open quadrant is null for the product of the two restricted
(closed) measures. -/
theorem measure_quad_compl :
    ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π/2)))) Quadᶜ = 0 := by
  rw [Measure.prod_restrict, Measure.restrict_apply isOpen_Quad.measurableSet.compl]
  change (MeasureTheory.volume.prod MeasureTheory.volume) (Quadᶜ ∩ Quad) = 0
  rw [Set.compl_inter_self, measure_empty]

theorem ae_mem_Quad_prod' :
    ∀ᵐ q ∂((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π/2)))), q ∈ Quad := by
  simpa using compl_mem_ae_iff.mpr measure_quad_compl

theorem ae_mem_Quad_prod :
    ∀ᵐ q ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), q ∈ Quad := by
  rw [restrict_Iz_eq, restrict_Iθ_eq]
  exact ae_mem_Quad_prod'

/-! ## Continuity of the two weights on the quadrant -/

theorem continuousOn_wdiv :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.w q.1
      / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2)) Quad := by
  have hsinpos : ∀ p ∈ Quad, 0 < Real.sin (2 * p.2) := fun p hp =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Quad := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Quad :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  exact hw.div hsinpow (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))

theorem continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2) Quad := by
  have hsinpos : ∀ p ∈ Quad, 0 < Real.sin (2 * p.2) := fun p hp =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Quad := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) Quad :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2)
      = fun q : ℝ × ℝ => Work.Spaces.w q.1 * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext q; rfl
  rw [hfun]
  exact hw.mul hsinpow

/-! ## Almost-everywhere strong measurability of the mollified slots -/

theorem aestronglyMeasurable_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (fun q : ℝ × ℝ => g q.1 q.2) Quad) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => Jeps ρ ε g q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [restrict_Iz_eq, restrict_Iθ_eq, ← Measure.restrict_eq_self_of_ae_mem ae_mem_Quad_prod']
  exact (JepsHkMem.continuousOn_Jeps hρ hε hg).aestronglyMeasurable isOpen_Quad.measurableSet

theorem aestronglyMeasurable_Jeps_slice' {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (fun q : ℝ × ℝ => g q.1 q.2) Quad)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => Jeps ρ ε g z θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π/2))) := by
  have hmap : ContinuousOn (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (π/2)) := by fun_prop
  have hcomp : ContinuousOn (fun θ : ℝ => Jeps ρ ε g z θ) (Set.Ioo 0 (π/2)) :=
    (JepsHkMem.continuousOn_Jeps hρ hε hg).comp hmap (fun θ hθ => ⟨hz, hθ⟩)
  exact hcomp.aestronglyMeasurable isOpen_Ioo.measurableSet

theorem aestronglyMeasurable_Jeps_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (fun q : ℝ × ℝ => g q.1 q.2) Quad)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => Jeps ρ ε g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq]
  exact aestronglyMeasurable_Jeps_slice' hρ hε hg hz

/-- The continuity on the quadrant of the mixed derivatives of a profile that is `C^n` there for
every `n`. -/
theorem continuousOn_mixed_of_smooth {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (j i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2) Quad :=
  (Work.FTS.LocData.contDiffOn_mixed isOpen_Quad (contDiffOn_infty.mpr hsm) j i).continuousOn


/-- The mollified mixed slots are a.e. strongly measurable on the product of the two closed
intervals. -/
theorem aestronglyMeasurable_mixed_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (j i : ℕ) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => Work.Spaces.mixed j i (Jeps ρ ε f) q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine (aestronglyMeasurable_Jeps hρ hε (continuousOn_mixed_of_smooth hsm j i)).congr ?_
  filter_upwards [ae_mem_Quad_prod] with q hq
  exact (mixed_Jeps ρ hρ hε hsm hq.1 hq.2 j i).symm

theorem aestronglyMeasurable_DzIter_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (i : ℕ) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => Work.Spaces.DzIter i (Jeps ρ ε f) q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have h := aestronglyMeasurable_mixed_Jeps hρ hε hsm i 0
  simpa only [Work.Spaces.mixed_zero_right] using h

theorem aestronglyMeasurable_mixed_Jeps_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z : ℝ} (hz : 0 < z) (j i : ℕ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.mixed j i (Jeps ρ ε f) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq]
  refine (aestronglyMeasurable_Jeps_slice' hρ hε (continuousOn_mixed_of_smooth hsm j i) hz).congr ?_
  filter_upwards [self_mem_ae_restrict isOpen_Ioo.measurableSet] with θ hθ
  exact (mixed_Jeps ρ hρ hε hsm hz hθ j i).symm

theorem aestronglyMeasurable_DzIter_Jeps_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z : ℝ} (hz : 0 < z) (i : ℕ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter i (Jeps ρ ε f) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h := aestronglyMeasurable_mixed_Jeps_slice hρ hε hsm hz i 0
  simpa only [Work.Spaces.mixed_zero_right] using h

/-! ## Almost-everywhere strong measurability of the mollified `H^k`-integrand -/

theorem aestronglyMeasurable_wdiv_slice (z : ℝ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq]
  exact (continuousOn_const.div
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.StrongEps.sin_two_pos hθ))))
    (fun θ hθ => ne_of_gt (Real.rpow_pos_of_pos (Work.FTS.StrongEps.sin_two_pos hθ) _))
      |>.aestronglyMeasurable isOpen_Ioo.measurableSet)

theorem aestronglyMeasurable_Wt_slice (α z : ℝ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.Wt α z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq]
  have hfun : (fun θ : ℝ => Work.Spaces.Wt α z θ)
      = fun θ : ℝ => Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext θ; rfl
  rw [hfun]
  exact (continuousOn_const.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.StrongEps.sin_two_pos hθ)))))
    |>.aestronglyMeasurable isOpen_Ioo.measurableSet

theorem aestronglyMeasurable_HkIntegrand_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {α : ℝ} {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hDz : ∀ i : ℕ, AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.DzIter i (Jeps ρ ε f) q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    fun i => aestronglyMeasurable_DzIter_Jeps hρ hε hsm i
  have hMx : ∀ j i : ℕ, AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.mixed j i (Jeps ρ ε f) q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    fun j i => aestronglyMeasurable_mixed_Jeps hρ hε hsm j i
  have hW : AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [restrict_Iz_eq, restrict_Iθ_eq]
    rw [← Measure.restrict_eq_self_of_ae_mem ae_mem_Quad_prod',
      ← Measure.restrict_eq_self_of_ae_mem ae_mem_Quad_prod']
    exact continuousOn_wdiv.aestronglyMeasurable isOpen_Quad.measurableSet
  have hWt : AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [restrict_Iz_eq, restrict_Iθ_eq]
    rw [← Measure.restrict_eq_self_of_ae_mem ae_mem_Quad_prod',
      ← Measure.restrict_eq_self_of_ae_mem ae_mem_Quad_prod']
    exact (continuousOn_Wt α).aestronglyMeasurable isOpen_Quad.measurableSet
  have hfun : (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) q.1 q.2)
      = (∑ i ∈ Finset.range (k + 1), fun q : ℝ × ℝ =>
            (Work.Spaces.DzIter i (Jeps ρ ε f) q.1 q.2
              * (Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), fun q : ℝ × ℝ =>
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i (Jeps ρ ε f) q.1 q.2 * Work.Spaces.Wt α q.1 q.2) ^ 2
                else 0) := by
    funext q
    simp only [Work.Spaces.HkIntegrand, Finset.sum_apply, Pi.add_apply]
  rw [hfun]
  refine AEStronglyMeasurable.add ?_ ?_
  · exact Finset.aestronglyMeasurable_sum _ (fun i _ => ((hDz i).mul hW).pow 2)
  · refine Finset.aestronglyMeasurable_sum _ (fun i _ => ?_)
    refine Finset.aestronglyMeasurable_sum _ (fun j _ => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact ((hMx j i).mul hWt).pow 2
    · simp only [if_neg hc]
      exact aestronglyMeasurable_const

theorem aestronglyMeasurable_HkIntegrand_Jeps_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ)
    {α : ℝ} {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hDz : ∀ i : ℕ, AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.DzIter i (Jeps ρ ε f) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun i => aestronglyMeasurable_DzIter_Jeps_slice hρ hε hsm hz i
  have hMx : ∀ j i : ℕ, AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.mixed j i (Jeps ρ ε f) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun j i => aestronglyMeasurable_mixed_Jeps_slice hρ hε hsm hz j i
  have hfun : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
      = (∑ i ∈ Finset.range (k + 1), fun θ : ℝ =>
            (Work.Spaces.DzIter i (Jeps ρ ε f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), fun θ : ℝ =>
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i (Jeps ρ ε f) z θ * Work.Spaces.Wt α z θ) ^ 2
                else 0) := by
    funext θ
    simp only [Work.Spaces.HkIntegrand, Finset.sum_apply, Pi.add_apply]
  rw [hfun]
  refine AEStronglyMeasurable.add ?_ ?_
  · exact Finset.aestronglyMeasurable_sum _
      (fun i _ => ((hDz i).mul (aestronglyMeasurable_wdiv_slice z)).pow 2)
  · refine Finset.aestronglyMeasurable_sum _ (fun i _ => ?_)
    refine Finset.aestronglyMeasurable_sum _ (fun j _ => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact ((hMx j i).mul (aestronglyMeasurable_Wt_slice α z)).pow 2
    · simp only [if_neg hc]
      exact aestronglyMeasurable_const


/-! ## Measurability of the shifted joint integrand -/

theorem aemeasurable_shift_z_pair {H : ℝ → ℝ → ℝ}
    (hH : ContinuousOn (fun q : ℝ × ℝ => H q.1 q.2) Quad) {z : ℝ} (hz : 0 < z) :
    AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (H (z * Real.exp (-q.1)) q.2))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  classical
  set S : Set (ℝ × ℝ) := {q | q.2 ∈ Set.Ioo 0 (π/2)} with hSdef
  have hSmeas : MeasurableSet S := (isOpen_Ioo.preimage continuous_snd).measurableSet
  have hnull : (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) Sᶜ = 0 := by
    have hScompl : Sᶜ = (Set.univ : Set ℝ) ×ˢ (Set.Ioo 0 (π/2))ᶜ := by
      ext q; simp [hSdef]
    have hIc : (MeasureTheory.volume.restrict Work.Spaces.Iθ) (Set.Ioo (0 : ℝ) (π/2))ᶜ = 0 := by
      rw [restrict_Iθ_eq, Measure.restrict_apply measurableSet_Ioo.compl,
        Set.compl_inter_self, measure_empty]
    rw [hScompl, Measure.prod_prod, hIc, mul_zero]
  have hmaps : MapsTo (fun q : ℝ × ℝ => (z * Real.exp (-q.1), q.2)) S Quad := by
    intro q hq
    exact ⟨mul_pos hz (Real.exp_pos _), hq⟩
  have hmap : ContinuousOn (fun q : ℝ × ℝ => (z * Real.exp (-q.1), q.2)) S := by
    refine ContinuousOn.prodMk ?_ continuousOn_snd
    exact continuousOn_const.mul
      ((Real.continuous_exp.comp (continuous_neg.comp continuous_fst)).continuousOn)
  have hcont : ContinuousOn (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2) S :=
    hH.comp hmap hmaps
  have hA : AEMeasurable (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2)
      (Measure.restrict ((MeasureTheory.volume.prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) S) :=
    hcont.aemeasurable hSmeas
  have hind : AEMeasurable (S.indicator (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2))
      ((MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
    (aemeasurable_indicator_iff hSmeas).mpr hA
  have hcongr : (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2)
      =ᵐ[((MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)))]
      S.indicator (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2) := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq
    simp only [Set.mem_compl_iff, not_not] at hq
    exact (Set.indicator_of_mem hq (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2)).symm
  have hGae : AEMeasurable (fun q : ℝ × ℝ => H (z * Real.exp (-q.1)) q.2)
      ((MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
    hind.congr hcongr.symm
  exact ENNReal.measurable_ofReal.comp_aemeasurable hGae

end JepsHkMem

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsHkMem.lintegral_HkIntegrand_Jeps_lt_top =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.JepsHkMem

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

theorem lintegral_HkIntegrand_Jeps_lt_top {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    (hmem : Work.Spaces.HkMem α k f) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Jeps ρ ε f) z θ)) < ⊤ := by
  -- the three shift bounds of the `E1` chapter
  obtain ⟨cη, hcηpos, hWη0⟩ := HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγpos, hWγ0⟩ := HkSqAux.Wt_shift_le
  obtain ⟨δ, hδpos, hJac0⟩ := HkSqAux.logJac_shift_le
  have hc0 : 0 ≤ max cη cγ := le_of_lt (lt_of_lt_of_le hcηpos (le_max_left _ _))
  -- the two weight bounds, with the common constant `max cη cγ`
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)) := by
    intro z θ hz hθ p
    refine (hWη0 z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact div_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.StrongEps.sin_two_pos
          (Work.FTS.StrongEps.thShift_mem hθ))) _)
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    intro z θ hz hθ p
    exact (hWγ0 α hα z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.StrongEps.sin_two_pos
          (Work.FTS.StrongEps.thShift_mem hθ))) _)))
  -- the `H^k`-integrand of `f` is continuous on the open quadrant
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad :=
    HkSqAux.continuousOn_HkIntegrand_Quad α k hsm
  set C : ENNReal := ENNReal.ofReal (Work.Spaces.HkSq α k f) with hC
  set E1 : ℝ × ℝ → ENNReal := fun p =>
    ENNReal.ofReal (Real.exp (2 * max cη cγ * (|p.1| + |p.2|))) with hE1
  set E2 : ℝ × ℝ → ENNReal := fun p =>
    ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) with hE2
  set E3 : ℝ × ℝ → ENNReal := fun p =>
    ENNReal.ofReal (Real.exp ((2 * max cη cγ + δ) * (|p.1| + |p.2|))) with hE3
  set K : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Work.FTS.StrongEps.Jker ρ ε p) with hK
  set Φ : ℝ → ℝ → ENNReal := fun z θ => ENNReal.ofReal
    (Work.Spaces.HkIntegrand α k (Work.FTS.StrongEps.Jeps ρ ε f) z θ) with hΦ
  -- the pointwise slot estimate
  have h2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ)
      ≤ (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) := by
    refine MeasureTheory.setLIntegral_mono' measurableSet_Ici fun z hz =>
      MeasureTheory.setLIntegral_mono' measurableSet_Icc fun θ hθ => ?_
    rw [hΦ, hK, hE1]
    exact HkSqAux.ofReal_GJ_le ρ hρ hε hα hsm hWη hWγ hz hθ k
  -- Tonelli
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
            (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      = (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))) := by
    rw [hK, hE1]
    exact HkSqAux.fubini_shift hρ.cont hcont
  -- the log-coordinate shift bound for the shifted integrand
  have h4 : (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))))
      ≤ (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C)) := by
    refine lintegral_mono fun p => mul_le_mul_right ?_ _
    rw [hE2, hC]
    exact HkSqAux.integral_shift_le (fun s ζ p₁ p₂ => hJac0 s ζ p₁ p₂) hmem hcont p
  -- the exponential factors combine
  have h5 : (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C))
      = C * (∫⁻ p : ℝ × ℝ, K p * E3 p) := by
    have hAB : ∀ p : ℝ × ℝ, E1 p * E2 p = E3 p := by
      intro p
      rw [hE1, hE2, hE3, HkSqAux.ofReal_exp_mul]
      congr 2
      ring
    have hstep1 : (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C))
        = ∫⁻ p : ℝ × ℝ, (K p * (E1 p * E2 p)) * C :=
      lintegral_congr fun p => by ring
    have hstep2 : (∫⁻ p : ℝ × ℝ, (K p * (E1 p * E2 p)) * C)
        = (∫⁻ p : ℝ × ℝ, K p * (E1 p * E2 p)) * C :=
      MeasureTheory.lintegral_mul_const' C _ ENNReal.ofReal_ne_top
    have hstep3 : (∫⁻ p : ℝ × ℝ, K p * (E1 p * E2 p)) = ∫⁻ p : ℝ × ℝ, K p * E3 p :=
      lintegral_congr fun p => by rw [hAB p]
    rw [hstep1, hstep2, hstep3, mul_comm]
  -- the kernel mass bound
  have h6 : (∫⁻ p : ℝ × ℝ, K p * E3 p)
      ≤ ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε)) := by
    rw [hK, hE3]
    exact HkSqAux.Jker_exp_integral_le hρ hε hc0 (le_of_lt hδpos)
  have hfinal : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ)
      ≤ C * ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε)) :=
    calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ)
        ≤ (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))) := h2
      _ = (∫⁻ p : ℝ × ℝ, (K p * E1 p)
            * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                  (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)))) := h3
      _ ≤ (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C)) := h4
      _ = C * (∫⁻ p : ℝ × ℝ, K p * E3 p) := h5
      _ ≤ C * ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε)) :=
          mul_le_mul_right h6 C
  refine lt_of_le_of_lt hfinal ?_
  refine lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ?_ ?_)
  · rw [hC]; exact ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_ne_top

end Work.FTS.StrongEps.JepsHkMem
end
-- ===== merged: Submission.Work.FTS.StrongPersist.Dbd =====
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

open Work.FTS.Galerkin (Fn Fam slice gdot dynLin dynRHS)
open Work.FTS.Nonlin (Xn)
open Work.FTS.VocabO (HQo)
open Work.Spaces (HkMem HkSq HkNorm)

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false








end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.t1TermSix =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_eta_eq canonW_gam_eq)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## Auxiliary lemmas

The two slice-integrability pieces used below are the delegated lemmas
`TermSixAux.sliceIntSup` (a sup-bounded factor times two canonical slots is `θ`-slice
integrable) and `TermSixAux.sliceIntCS` (a sup-bounded factor times a Cauchy–Schwarz pair is
`θ`-slice integrable), proved in
`Submission/Work/FTS/StrongPersist/N6Trans/T1SixAux/TermSixAux/`. -/

/-! ### Swapping the two non-sup slots -/


/-! ## The main theorem -/


end Work.FTS.StrongPersist.N6Trans.T1SixAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SupOpenH2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.SupOpenH2` — the open-quadrant Agmon bound

`|h z θ| ≤ C α^{-1/2} |h|_{ℋ²}` on the open quadrant `Q0`, for `h` only assumed `C^∞` on the
open quadrant and honestly in `ℋ²` (`HQo α 2 h`).

Route.  Fix `(z,θ) ∈ Q0`, `z > 0`.  The angular Agmon inequality
`Work.H2.T1Q.SliceSupOpen` bounds `h(z,θ)²` by the two angular integrals
`∫_θ h(z,·)²` and `∫_θ (∂_θh)² sin(2θ)^{2-γ}` at the fixed radius `z`; multiplying by the radial
weight `(w z)² z` converts these into the two `θ`-integrated quantities
`z(w z)² ∫_θ h²σ^{-η}` and `z(w z)² ∫_θ (D_θh)²σ^{-γ}`, which are bounded at `z` by their global
`ℋ²`-integrals (`zavg_A`, `zavg_B`, via the "log-window averaging" of `SupOpenH2Z`), using
`(w z)² z ≥ 256/27` (`w_sq_mul_self_ge`) to undo the radial weight.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

theorem SupOpenH2 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ h : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 2 h →
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |h z θ| ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 h := by
  refine ⟨100, by norm_num, ?_⟩
  intro α hα hα1 h hQ z θ hzθ
  obtain ⟨hso, hmem⟩ := hQ
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hθmem : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hγ1 : 1 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hγm1 : Work.Spaces.gam α - 1 = α / 10 := by rw [Work.Spaces.gam]; ring
  -- ## the angular Agmon inequality at radius `z`
  have hslice : ContDiffOn ℝ 1 (fun θ' => h z θ') (Set.Ioo 0 (π / 2)) := by
    have hsle : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
      rw [Work.Stability.smoothOrder]
      exact WithTop.coe_le_coe.mpr le_top
    exact (Work.FTS.LocData.contDiffOn_slice_θ hso hz).of_le hsle
  have hu2 : IntegrableOn (fun θ' => (h z θ') ^ 2) Work.Spaces.Iθ := integrableOn_hsq hso hmem hz
  have hint2 : IntegrableOn (fun θ' => (Work.Spaces.pth h z θ') ^ 2
      * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    integrableOn_pth_sq hα hα1 hso hmem hz
  have hsup := Work.H2.T1Q.SliceSupOpen α (fun θ' => h z θ') hα hα1 hslice hu2 hint2 θ hθmem
  -- ## weighted comparison of the plain angular `L²`-norm
  have hint1 : IntegrableOn (fun θ' => (h z θ') ^ 2
      * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    integrableOn_hsq_sEta hso hmem hz
  have hcmp := int_sq_le_two_weighted (aesm_sq_slice_of_SmoothOpen hso hz) hint1
  -- ## convert `∂_θ` to `D_θ`
  have hconv : (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.pth h z θ') ^ 2
        * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α))
      = ∫ θ' in Work.Spaces.Iθ, (Work.Spaces.Dth h z θ') ^ 2
        * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ' hθ' => ?_
    show (Work.Spaces.pth h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.Dth h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))
    rw [show Work.Spaces.Dth h z θ' = Real.sin (2 * θ') * Work.Spaces.pth h z θ' from rfl]
    rw [show (Real.sin (2 * θ') * Work.Spaces.pth h z θ') ^ 2
          * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))
        = (Work.Spaces.pth h z θ') ^ 2
          * ((Real.sin (2 * θ')) ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)))
        from by rw [mul_pow]; ring]
    rw [sin_two_sq_mul_neg_Iθ (p := Work.Spaces.gam α) hθ' (gam_ne_two hα1)]
  -- ## the two `z`-averaging bounds
  have hA := zavg_A hso hmem hz
  have hB := zavg_B hα hso hmem hz
  have hWnn : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 * z := by positivity
  have hWge : (256 : ℝ) / 27 ≤ (Work.Spaces.w z) ^ 2 * z := w_sq_mul_self_ge hz
  -- ## combine
  have hstep : (Work.Spaces.w z) ^ 2 * z * (h z θ) ^ 2
      ≤ (8 / Real.pi) * ((Work.Spaces.w z) ^ 2 * z
          * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))))
        + (200 / (Work.Spaces.gam α - 1)) * ((Work.Spaces.w z) ^ 2 * z
          * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.Dth h z θ') ^ 2
            * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)))) := by
    have hsup' : (h z θ) ^ 2 ≤ (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2)
        + (200 / (Work.Spaces.gam α - 1)) * (∫ θ' in Work.Spaces.Iθ,
            (Work.Spaces.pth h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)) :=
      hsup
    rw [hconv] at hsup'
    have hcmp2 : (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2)
        ≤ (8 / Real.pi) * (∫ θ' in Work.Spaces.Iθ,
            (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))) := by
      have hml := mul_le_mul_of_nonneg_left hcmp (by positivity : (0:ℝ) ≤ 4 / Real.pi)
      calc (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2)
          ≤ (4 / Real.pi) * (2 * (∫ θ' in Work.Spaces.Iθ,
              (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta)))) := hml
        _ = (8 / Real.pi) * (∫ θ' in Work.Spaces.Iθ,
              (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))) := by ring
    have h1 : (h z θ) ^ 2 ≤ (8 / Real.pi) * (∫ θ' in Work.Spaces.Iθ,
          (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta)))
        + (200 / (Work.Spaces.gam α - 1)) * (∫ θ' in Work.Spaces.Iθ,
            (Work.Spaces.Dth h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))) := by
      nlinarith [hsup', hcmp2]
    calc (Work.Spaces.w z) ^ 2 * z * (h z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * z * ((8 / Real.pi) * (∫ θ' in Work.Spaces.Iθ,
              (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta)))
            + (200 / (Work.Spaces.gam α - 1)) * (∫ θ' in Work.Spaces.Iθ,
                (Work.Spaces.Dth h z θ') ^ 2
                  * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)))) :=
          mul_le_mul_of_nonneg_left h1 hWnn
      _ = (8 / Real.pi) * ((Work.Spaces.w z) ^ 2 * z
            * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2
              * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))))
          + (200 / (Work.Spaces.gam α - 1)) * ((Work.Spaces.w z) ^ 2 * z
            * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.Dth h z θ') ^ 2
              * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)))) := by ring
  have hAB : (8 / Real.pi) * ((Work.Spaces.w z) ^ 2 * z
          * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))))
        + (200 / (Work.Spaces.gam α - 1)) * ((Work.Spaces.w z) ^ 2 * z
          * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.Dth h z θ') ^ 2
            * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))))
      ≤ ((8 / Real.pi) * 9 + (200 / (Work.Spaces.gam α - 1)) * 9) * Work.Spaces.HkSq α 2 h := by
    have h8 : (0 : ℝ) ≤ 8 / Real.pi := by positivity
    have h200 : (0 : ℝ) ≤ 200 / (Work.Spaces.gam α - 1) := by
      apply div_nonneg (by norm_num); linarith
    have hA' := mul_le_mul_of_nonneg_left hA h8
    have hB' := mul_le_mul_of_nonneg_left hB h200
    linarith [hA', hB']
  have hfac : 200 / (Work.Spaces.gam α - 1) = 2000 / α := by
    rw [hγm1]; field_simp; norm_num
  have hcoef : (27 / 256) * ((8 / Real.pi) * 9 + (200 / (Work.Spaces.gam α - 1)) * 9)
      ≤ 10000 / α := by
    rw [hfac]
    have hπ : 8 / Real.pi ≤ 3 := by
      rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    have h3α : 8 / Real.pi ≤ 3 / α := by
      rw [div_le_div_iff₀ Real.pi_pos hα]
      nlinarith [Real.pi_gt_three, hα.le, hα1]
    have hsum : 8 / Real.pi + 2000 / α ≤ 2003 / α := by
      have h4 : (3 : ℝ) / α + 2000 / α = 2003 / α := by ring
      linarith [h3α, h4]
    have h5 : 2003 / α ≤ 10000 / α :=
      div_le_div_of_nonneg_right (by norm_num) hα.le
    have h6 : (0 : ℝ) ≤ 8 / Real.pi + 2000 / α := by positivity
    have hrel : (27 / 256) * ((8 / Real.pi) * 9 + (2000 / α) * 9)
        = (243 / 256) * (8 / Real.pi + 2000 / α) := by ring
    rw [hrel]
    calc (243 / 256) * (8 / Real.pi + 2000 / α)
        ≤ 1 * (8 / Real.pi + 2000 / α) :=
          mul_le_mul_of_nonneg_right (by norm_num) h6
      _ ≤ 2003 / α := by rw [one_mul]; exact hsum
      _ ≤ 10000 / α := h5
  have hsq : (h z θ) ^ 2 ≤ (10000 / α) * Work.Spaces.HkSq α 2 h := by
    have hWh : (Work.Spaces.w z) ^ 2 * z * (h z θ) ^ 2
        ≤ ((8 / Real.pi) * 9 + (200 / (Work.Spaces.gam α - 1)) * 9)
          * Work.Spaces.HkSq α 2 h := le_trans hstep hAB
    have h1 : (h z θ) ^ 2 ≤ (27 / 256) * ((Work.Spaces.w z) ^ 2 * z * (h z θ) ^ 2) := by
      have hle : (1 : ℝ) ≤ (27 / 256) * ((Work.Spaces.w z) ^ 2 * z) := by linarith [hWge]
      nlinarith [hle, sq_nonneg (h z θ)]
    have hSq : (0 : ℝ) ≤ Work.Spaces.HkSq α 2 h := Work.Spaces.HkSq_nonneg α 2 h
    have h2 : (27 / 256) * (((8 / Real.pi) * 9 + (200 / (Work.Spaces.gam α - 1)) * 9)
          * Work.Spaces.HkSq α 2 h)
        ≤ (10000 / α) * Work.Spaces.HkSq α 2 h := by
      have := hcoef
      nlinarith [this, hSq]
    linarith [h1, hWh, h2]
  -- ## square roots
  have h100 : (0 : ℝ) ≤ 100 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 h := by
    have h1 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have h2 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 2 h := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (by norm_num) h1) h2
  have hsq2 : (h z θ) ^ 2 ≤ (100 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 h) ^ 2 := by
    rw [mul_pow, mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 2 h)]
    have hrp : (α ^ (-(1 / 2 : ℝ))) ^ 2 = α ^ (-(1 : ℝ)) := by
      rw [pow_two, ← Real.rpow_add hα]; ring_nf
    rw [hrp, Real.rpow_neg_one]
    have hdiv : (10000 / α) * Work.Spaces.HkSq α 2 h
        ≤ 10000 * α⁻¹ * Work.Spaces.HkSq α 2 h := by
      rw [div_eq_mul_inv]
    linarith [hsq, hdiv]
  calc |h z θ| = Real.sqrt ((h z θ) ^ 2) := (Real.sqrt_sq_eq_abs (h z θ)).symm
    _ ≤ Real.sqrt ((100 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 h) ^ 2) :=
        Real.sqrt_le_sqrt hsq2
    _ = 100 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 h := Real.sqrt_sq h100

end Work.FTS.StrongPersist
end
end
