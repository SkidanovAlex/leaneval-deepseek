import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.PhiStar.EllExistHalf
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Honesty.zDeriv_radGreen_sq_w_sq_integrableOn
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.EpsSqTools.Pointwise
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.H6Rows.NstarRow
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gLocal
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmA
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyDefs
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyRight
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.StrongPersist.StarPkg6Fields
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.cmode_bessel_L2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty


end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.psiSeries_tendsto_of_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-! ## elementary helpers -/

theorem pst_w_ge_one {t : ℝ} (ht : 0 < t) : 1 ≤ Work.Spaces.w t := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

theorem pst_smoothOpen_neg {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (-f) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hf ⊢
  have hfun : Function.uncurry (-f) = -(Function.uncurry f) := by funext p; rfl
  rw [hfun]
  exact hf.neg

theorem pst_smoothOpen_sub {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  have h := Work.FTS.EllipticEst.smoothOpen_add hf (pst_smoothOpen_neg hg)
  simpa only [Pi.neg_apply, sub_eq_add_neg] using h

theorem hkMem_neg_zero {α : ℝ} {f : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α 0 f) :
    Work.Spaces.HkMem α 0 (-f) := by
  obtain ⟨h1, h2⟩ := h
  have hpt : ∀ z θ : ℝ, Work.Spaces.HkIntegrand α 0 (-f) z θ
      = Work.Spaces.HkIntegrand α 0 f z θ := by
    intro z θ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
      Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
    simp only [Pi.neg_apply]
    ring
  refine ⟨fun z hz => (h1 z hz).congr_fun (fun θ _ => (hpt z θ).symm) measurableSet_Icc, ?_⟩
  refine h2.congr_fun (fun z _ => ?_) measurableSet_Ici
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => (hpt z θ).symm)

theorem cmode_sq_integrable {α : ℝ} {X : ℝ → ℝ → ℝ}
    (hX : Work.FTS.EllipticEst.SmoothOpen X) (hmX : Work.Spaces.HkMem α 0 X) (m : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m X t) ^ 2)
      (Set.Ioi 0) := by
  have hW := (Work.FTS.ClassCHon.Hcoef.cmode_L2_bound hX hmX m).1
  refine hW.mono' ((Work.EllipticEst.ModalSolution.aesm_cmode hX m).pow 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : 1 ≤ (Work.Spaces.w t) ^ 2 := by
    have := pst_w_ge_one ht
    nlinarith
  calc (Work.FTS.PhiStar.Series.cmode m X t) ^ 2
      = (Work.FTS.PhiStar.Series.cmode m X t) ^ 2 * 1 := by ring
    _ ≤ (Work.FTS.PhiStar.Series.cmode m X t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = (Work.FTS.PhiStar.Series.cmode m X t * Work.Spaces.w t) ^ 2 := by ring

theorem psiTrunc_sub {α : ℝ} {X Y : ℝ → ℝ → ℝ} (N : ℕ) (z θ : ℝ) :
    Work.FTS.PhiStar.Series.psiTrunc α X N z θ
        - Work.FTS.PhiStar.Series.psiTrunc α Y N z θ
      = ∑ m ∈ Finset.range (N + 1),
          (Work.FTS.PhiStar.Series.acoeff α m X z
              - Work.FTS.PhiStar.Series.acoeff α m Y z)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  simp only [Work.FTS.PhiStar.Series.psiTrunc]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun m _ => by ring)

theorem psiTrunc_tendsto_of_summable {α : ℝ} {X : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθI : θ ∈ Work.Spaces.Iθ)
    (hcoef : Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m X z|)) :
    Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α X N z θ)
      Filter.atTop (nhds (Work.FTS.PhiStar.Series.psiSeries α X z θ)) := by
  obtain ⟨Ce, hCe, hCeb⟩ := Work.FTS.PhiStar.Series.eFam_sup_le
  have hmaj : Summable (fun m : ℕ => Ce * (((m : ℝ) + 1)
      * |Work.FTS.PhiStar.Series.acoeff α m X z|)) := hcoef.mul_left Ce
  have hnorm : Summable (fun m : ℕ => ‖Work.FTS.PhiStar.Series.acoeff α m X z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖) := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hmaj
    rw [Real.norm_eq_abs, abs_mul]
    calc |Work.FTS.PhiStar.Series.acoeff α m X z|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ |Work.FTS.PhiStar.Series.acoeff α m X z| * (Ce * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (hCeb m θ hθI) (abs_nonneg _)
      _ = Ce * (((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m X z|) := by ring
  have hS : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.acoeff α m X z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := hnorm.of_norm
  have hlim := hS.hasSum.tendsto_sum_nat
  have hfun : (fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
        Work.FTS.PhiStar.Series.acoeff α m X z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      = ((fun n : ℕ => ∑ m ∈ Finset.range n,
          Work.FTS.PhiStar.Series.acoeff α m X z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        ∘ fun N : ℕ => N + 1) := by
    funext N
    rfl
  simp only [Work.FTS.PhiStar.Series.psiTrunc, Work.FTS.PhiStar.Series.psiSeries, hfun]
  exact hlim.comp (Filter.tendsto_add_atTop_nat 1)

theorem psiTrunc_diff_le {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {G : ℕ → ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (hG : ∀ n, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hGm : ∀ n, Work.Spaces.HkMem α 0 (G n))
    (hFm : Work.Spaces.HkMem α 0 F)
    {z θ Ce : ℝ} (hCe : 0 ≤ Ce) (hz : 0 < z) (hθI : θ ∈ Work.Spaces.Iθ)
    (hCeb : ∀ m : ℕ, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Ce * ((m : ℝ) + 1)) :
    ∀ (n N : ℕ), |Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ
        - Work.FTS.PhiStar.Series.psiTrunc α F N z θ|
      ≤ Ce * ((2 / α) * z ^ (-(1 / 2) : ℝ)
          * (2 * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => G n z θ - F z θ)))) := by
  intro n N
  set D : ℝ → ℝ → ℝ := fun z θ => G n z θ - F z θ with hD
  have hDsm : Work.FTS.EllipticEst.SmoothOpen D := by
    rw [hD]; exact pst_smoothOpen_sub (hG n) hF
  have hDmem : Work.Spaces.HkMem α 0 D := by
    rw [hD]
    have h := Work.FTS.EllipticEst.HkMem_add_open (α := α) (k := 0) (f := G n) (g := -F)
      (hG n) (pst_smoothOpen_neg hF) (hGm n) (hkMem_neg_zero hFm)
    simpa only [Pi.neg_apply, sub_eq_add_neg] using h
  set U : ℕ → ℝ := fun m => Real.sqrt (∫ t in Set.Ioi 0,
      (Work.FTS.PhiStar.Series.cmode m D t) ^ 2) with hU
  have hUsq : ∀ m : ℕ, (U m) ^ 2
      = ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m D t) ^ 2 := by
    intro m
    rw [hU]
    exact Real.sq_sqrt (integral_nonneg (fun t => sq_nonneg _))
  have hUnn : ∀ m : ℕ, 0 ≤ U m := by
    intro m; rw [hU]; exact Real.sqrt_nonneg _
  have hmb : ∀ m : ℕ, Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2
      ≤ Work.Spaces.HkSq α 0 D := by
    intro m
    have hW : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m D t * Work.Spaces.w t) ^ 2)
        (Set.Ioi 0) := (Work.FTS.ClassCHon.Hcoef.cmode_L2_bound hDsm hDmem m).1
    have hb := (Work.FTS.ClassCHon.Hcoef.cmode_L2_bound hDsm hDmem m).2
    rw [hUsq m]
    refine le_trans (mul_le_mul_of_nonneg_left ?_
      (Work.EllipticEst.ModalSolution.eNorm_pos m).le) hb
    refine setIntegral_mono_on (cmode_sq_integrable hDsm hDmem m) hW measurableSet_Ioi ?_
    intro t ht
    have h1 : 1 ≤ (Work.Spaces.w t) ^ 2 := by have := pst_w_ge_one ht; nlinarith
    calc (Work.FTS.PhiStar.Series.cmode m D t) ^ 2
        = (Work.FTS.PhiStar.Series.cmode m D t) ^ 2 * 1 := by ring
      _ ≤ (Work.FTS.PhiStar.Series.cmode m D t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = (Work.FTS.PhiStar.Series.cmode m D t * Work.Spaces.w t) ^ 2 := by ring
  have hintc : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => D z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    fun z hz => Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem hDmem hz
  have hints : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => D z θ ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    fun z hz => Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem hDmem hz
  have hBessel : ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1),
      Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2 ≤ Work.Spaces.HkSq α 0 D := by
    intro N
    refine le_trans (Finset.sum_le_sum (fun m _ => ?_))
      (Work.FTS.ClassC.sum_eNorm_cmode_sq_le_HkSq α D N hDsm hDmem hintc hints)
    have hW' : MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.FTS.PhiStar.Series.cmode m D z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (Set.Ioi 0) :=
      ((Work.FTS.ClassCHon.Hcoef.cmode_L2_bound hDsm hDmem m).1).congr_fun
        (fun t _ => by ring) measurableSet_Ioi
    refine mul_le_mul_of_nonneg_left ?_ (Work.EllipticEst.ModalSolution.eNorm_pos m).le
    rw [hUsq m]
    refine setIntegral_mono_on (cmode_sq_integrable hDsm hDmem m) hW' measurableSet_Ioi ?_
    intro t ht
    have h1 : 1 ≤ (Work.Spaces.w t) ^ 2 := by have := pst_w_ge_one ht; nlinarith
    calc (Work.FTS.PhiStar.Series.cmode m D t) ^ 2
        = (Work.FTS.PhiStar.Series.cmode m D t) ^ 2 * 1 := by ring
      _ ≤ (Work.FTS.PhiStar.Series.cmode m D t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hHnn : 0 ≤ Work.Spaces.HkSq α 0 D := by
    have h := hmb 0
    have h1 : (0 : ℝ) ≤ (U 0) ^ 2 := sq_nonneg _
    have h2 : 0 < Work.EllipticEst.ModalSolution.eNorm 0 :=
      Work.EllipticEst.ModalSolution.eNorm_pos 0
    nlinarith
  have hCS : ∑ m ∈ Finset.range (N + 1), U m / Real.sqrt ((m : ℝ) + 1)
      ≤ 2 * Real.sqrt (Work.Spaces.HkSq α 0 D) :=
    DiffGreen.sum_sqrt_eNorm_le (U := U) hUnn hHnn hBessel N
  have hper : ∀ m : ℕ, ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m (G n) z
        - Work.FTS.PhiStar.Series.acoeff α m F z|
      ≤ (2 / α) * z ^ (-(1 / 2) : ℝ) * (U m / Real.sqrt ((m : ℝ) + 1)) := by
    intro m
    have hdiff := DiffGreen.radGreen_diff_abs_le (α := α) hα hα4 m
      (Work.EllipticEst.ModalSolution.aesm_cmode hF m)
      (Work.EllipticEst.ModalSolution.aesm_cmode (hG n) m)
      (cmode_sq_integrable hF hFm m) (cmode_sq_integrable (hG n) (hGm n) m) hz
    have hcongr : (∫ t in Set.Ioi 0,
          (Work.FTS.PhiStar.Series.cmode m (G n) t
            - Work.FTS.PhiStar.Series.cmode m F t) ^ 2) = (U m) ^ 2 := by
      have h1 : (∫ t in Set.Ioi 0,
          (Work.FTS.PhiStar.Series.cmode m (G n) t - Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
          = ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m D t) ^ 2 := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        rw [hD, DiffGreen.cmode_sub (α := α) (hG n) hF (hGm n) hFm m ht]
      rw [h1, hUsq m]
    calc ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m (G n) z
            - Work.FTS.PhiStar.Series.acoeff α m F z|
        = ((m : ℝ) + 1) * |Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.Series.cmode m (G n)) z
            - Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.Series.cmode m F) z| := by
          simp only [Work.FTS.PhiStar.Series.acoeff]
      _ ≤ (2 / α) * Real.sqrt (∫ t in Set.Ioi 0,
              (Work.FTS.PhiStar.Series.cmode m (G n) t
                - Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
            * z ^ (-(1 / 2) : ℝ) / Real.sqrt ((m : ℝ) + 1) := hdiff
      _ = (2 / α) * U m * z ^ (-(1 / 2) : ℝ) / Real.sqrt ((m : ℝ) + 1) := by
          rw [hcongr, Real.sqrt_sq (hUnn m)]
      _ = (2 / α) * z ^ (-(1 / 2) : ℝ) * (U m / Real.sqrt ((m : ℝ) + 1)) := by ring
  have hsum : ∑ m ∈ Finset.range (N + 1),
        (((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m (G n) z
            - Work.FTS.PhiStar.Series.acoeff α m F z|)
      ≤ (2 / α) * z ^ (-(1 / 2) : ℝ) * (2 * Real.sqrt (Work.Spaces.HkSq α 0 D)) := by
    have h1 : ∑ m ∈ Finset.range (N + 1),
          (((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m (G n) z
              - Work.FTS.PhiStar.Series.acoeff α m F z|)
        ≤ ∑ m ∈ Finset.range (N + 1),
            ((2 / α) * z ^ (-(1 / 2) : ℝ) * (U m / Real.sqrt ((m : ℝ) + 1))) :=
      Finset.sum_le_sum (fun m _ => hper m)
    have h2 : ∑ m ∈ Finset.range (N + 1),
            ((2 / α) * z ^ (-(1 / 2) : ℝ) * (U m / Real.sqrt ((m : ℝ) + 1)))
        = (2 / α) * z ^ (-(1 / 2) : ℝ)
            * ∑ m ∈ Finset.range (N + 1), U m / Real.sqrt ((m : ℝ) + 1) := by
      rw [Finset.mul_sum]
    rw [h2] at h1
    refine le_trans h1 (mul_le_mul_of_nonneg_left hCS ?_)
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hz.le _)
  have hTr : |Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ
        - Work.FTS.PhiStar.Series.psiTrunc α F N z θ|
      = |∑ m ∈ Finset.range (N + 1),
          (Work.FTS.PhiStar.Series.acoeff α m (G n) z
              - Work.FTS.PhiStar.Series.acoeff α m F z)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by
    rw [psiTrunc_sub]
  rw [hTr]
  calc |∑ m ∈ Finset.range (N + 1),
          (Work.FTS.PhiStar.Series.acoeff α m (G n) z
            - Work.FTS.PhiStar.Series.acoeff α m F z) * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ ∑ m ∈ Finset.range (N + 1),
          |(Work.FTS.PhiStar.Series.acoeff α m (G n) z
            - Work.FTS.PhiStar.Series.acoeff α m F z) * Work.FTS.PhiStar.Gegenbauer.eFam m θ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range (N + 1),
          Ce * (((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m (G n) z
              - Work.FTS.PhiStar.Series.acoeff α m F z|) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        rw [abs_mul]
        calc |Work.FTS.PhiStar.Series.acoeff α m (G n) z
                - Work.FTS.PhiStar.Series.acoeff α m F z|
              * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
            ≤ |Work.FTS.PhiStar.Series.acoeff α m (G n) z
                - Work.FTS.PhiStar.Series.acoeff α m F z| * (Ce * ((m : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left (hCeb m θ hθI) (abs_nonneg _)
          _ = Ce * (((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m (G n) z
                - Work.FTS.PhiStar.Series.acoeff α m F z|) := by ring
    _ = Ce * ∑ m ∈ Finset.range (N + 1),
          (((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m (G n) z
              - Work.FTS.PhiStar.Series.acoeff α m F z|) := by rw [Finset.mul_sum]
    _ ≤ Ce * ((2 / α) * z ^ (-(1 / 2) : ℝ) * (2 * Real.sqrt (Work.Spaces.HkSq α 0 D))) :=
        mul_le_mul_of_nonneg_left hsum hCe

theorem psiSeries_tendsto_of_HkSq {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {G : ℕ → ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (hG : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hGm : ∀ n : ℕ, Work.Spaces.HkMem α 0 (G n))
    (hFm : Work.Spaces.HkMem α 0 F)
    (hconv : Filter.Tendsto (fun n : ℕ =>
        Work.Spaces.HkSq α 0 (fun z θ => G n z θ - F z θ)) Filter.atTop (nhds 0)) :
    (∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.FTS.PhiStar.Series.psiSeries α (G n) z θ)
        Filter.atTop (nhds (Work.FTS.PhiStar.Series.psiSeries α F z θ))) := by
  intro z hz θ hθ0 hθ2
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ2.le⟩
  obtain ⟨Ce, hCe, hCeb⟩ := Work.FTS.PhiStar.Series.eFam_sup_le
  have hsumG : ∀ n : ℕ, Summable (fun m : ℕ => ((m : ℝ) + 1) *
      |Work.FTS.PhiStar.Series.acoeff α m (G n) z|) :=
    fun n => Work.FTS.PhiStar.Honesty.hcoef_psiSeries hα hα4 (hG n) (hGm n) z hz
  have hsumF : Summable (fun m : ℕ => ((m : ℝ) + 1) *
      |Work.FTS.PhiStar.Series.acoeff α m F z|) :=
    Work.FTS.PhiStar.Honesty.hcoef_psiSeries hα hα4 hF hFm z hz
  have hlimG : ∀ n : ℕ, Filter.Tendsto
      (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ)
      Filter.atTop (nhds (Work.FTS.PhiStar.Series.psiSeries α (G n) z θ)) :=
    fun n => psiTrunc_tendsto_of_summable hθI (hsumG n)
  have hlimF : Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
      Filter.atTop (nhds (Work.FTS.PhiStar.Series.psiSeries α F z θ)) :=
    psiTrunc_tendsto_of_summable hθI hsumF
  set B : ℕ → ℝ := fun n => Ce * ((2 / α) * z ^ (-(1 / 2) : ℝ) * 2)
      * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => G n z θ - F z θ)) with hB
  have hBlim : Filter.Tendsto B Filter.atTop (nhds 0) := by
    have hs : Filter.Tendsto (fun n : ℕ => Real.sqrt (Work.Spaces.HkSq α 0
        (fun z θ => G n z θ - F z θ))) Filter.atTop (nhds 0) := by
      have h := hconv.sqrt
      rwa [Real.sqrt_zero] at h
    have h2 := hs.const_mul (Ce * ((2 / α) * z ^ (-(1 / 2) : ℝ) * 2))
    simpa only [hB, mul_zero] using h2
  have hmid : ∀ n N : ℕ, |Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ
      - Work.FTS.PhiStar.Series.psiTrunc α F N z θ| ≤ B n := by
    intro n N
    have h := psiTrunc_diff_le hα hα4 hG hF hGm hFm hCe.le hz hθI hCeb n N
    have he : Ce * ((2 / α) * z ^ (-(1 / 2) : ℝ)
        * (2 * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => G n z θ - F z θ)))) = B n := by
      rw [hB]; ring
    rwa [he] at h
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨n0, hn0⟩ := Metric.tendsto_atTop.mp hBlim (ε / 2) hε2
  refine ⟨n0, fun n hn => ?_⟩
  have hBn : B n < ε / 2 := by
    have h := hn0 n hn
    rw [Real.dist_eq, sub_zero] at h
    exact (abs_lt.mp h).2
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  have hevG : ∀ᶠ N in Filter.atTop, |Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
      - Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ| < ε / 4 := by
    have h' : Filter.Tendsto (fun N : ℕ => |Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
        - Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ|) Filter.atTop (nhds 0) := by
      have h := ((hlimG n).const_sub (Work.FTS.PhiStar.Series.psiSeries α (G n) z θ)).abs
      simpa using h
    exact h'.eventually (Iio_mem_nhds hε4)
  have hevF : ∀ᶠ N in Filter.atTop, |Work.FTS.PhiStar.Series.psiSeries α F z θ
      - Work.FTS.PhiStar.Series.psiTrunc α F N z θ| < ε / 4 := by
    have h' : Filter.Tendsto (fun N : ℕ => |Work.FTS.PhiStar.Series.psiSeries α F z θ
        - Work.FTS.PhiStar.Series.psiTrunc α F N z θ|) Filter.atTop (nhds 0) := by
      have h := (hlimF.const_sub (Work.FTS.PhiStar.Series.psiSeries α F z θ)).abs
      simpa using h
    exact h'.eventually (Iio_mem_nhds hε4)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hevG.and hevF)
  obtain ⟨hNG, hNF⟩ := hN N le_rfl
  have htri : |Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
        - Work.FTS.PhiStar.Series.psiSeries α F z θ|
      ≤ |Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
            - Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ|
        + |Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ
            - Work.FTS.PhiStar.Series.psiTrunc α F N z θ|
        + |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
            - Work.FTS.PhiStar.Series.psiSeries α F z θ| := by
    have he : Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
          - Work.FTS.PhiStar.Series.psiSeries α F z θ
        = (Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
              - Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ)
          + (Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ
              - Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
          + (Work.FTS.PhiStar.Series.psiTrunc α F N z θ
              - Work.FTS.PhiStar.Series.psiSeries α F z θ) := by ring
    rw [he]
    have h1 : |(Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
              - Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ)
          + (Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ
              - Work.FTS.PhiStar.Series.psiTrunc α F N z θ)|
        ≤ |Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
              - Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ|
          + |Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ
              - Work.FTS.PhiStar.Series.psiTrunc α F N z θ| := abs_add_le _ _
    calc |((Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
              - Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ)
          + (Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ
              - Work.FTS.PhiStar.Series.psiTrunc α F N z θ))
          + (Work.FTS.PhiStar.Series.psiTrunc α F N z θ
              - Work.FTS.PhiStar.Series.psiSeries α F z θ)|
        ≤ |(Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
              - Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ)
          + (Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ
              - Work.FTS.PhiStar.Series.psiTrunc α F N z θ)|
          + |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
              - Work.FTS.PhiStar.Series.psiSeries α F z θ| := abs_add_le _ _
      _ ≤ (|Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
              - Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ|
          + |Work.FTS.PhiStar.Series.psiTrunc α (G n) N z θ
              - Work.FTS.PhiStar.Series.psiTrunc α F N z θ|)
          + |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
              - Work.FTS.PhiStar.Series.psiSeries α F z θ| := by linarith
  have hmidn := hmid n N
  have h3 : |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
      - Work.FTS.PhiStar.Series.psiSeries α F z θ| < ε / 4 := by
    rw [abs_sub_comm]; exact hNF
  have hfin : |Work.FTS.PhiStar.Series.psiSeries α (G n) z θ
      - Work.FTS.PhiStar.Series.psiSeries α F z θ| < ε := by
    linarith [htri, hNG, hmidn, h3, hBn]
  rwa [Real.dist_eq]

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_modeEnergy_of_compactSource =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-!
# `Work.FTS.PhiStar.Honesty.radGreen_modeEnergy_of_compactSource`

The sharp per-mode weighted `L²` bound for the mode-`m` radial Green function

  `a := radGreen α m c`,   `−α²z²a'' − α(5+α)z a' + λ_m a = c`,   `λ_m = lamR m = 2m(2m+5)`,

for a source `c` which is only *continuous* on `(0,∞)` and *compactly supported away from `0`*
(`c ≡ 0` off some `[a,b]` with `a > 0`):

  `(λ_m − 3α² − 3α(5+α)/2)² · ∫_0^∞ a² w²  ≤  ∫_0^∞ c² w²`,   `w(z) = (1+z)²/z²`.

The hypothesis set is the honest one: no smoothness of `c` beyond continuity, no explicit
boundedness, no positioned support interval.  Everything the abstract per-mode theorem
`Work.FTS.ClassC.radGreen_modeEnergy` asks for is *deduced*:

* the global bound `∃ M, ∀ t, |c t| ≤ M` and the two-sided rate conditions `hdec`, `hvy` come
  from compact support plus continuity (`radGreen_source_facts_of_compactSupport`, the sibling
  lemma of this directory);
* the three Green-formula integrability conditions and the `c²w²`-slot likewise;
* the two derivative slots of `a` come from `Series.radGreenI_differentiableAt`, which needs
  only continuity of `c` (not smoothness);
* the two weighted `L²` slots `(z a')²w²` and `a²w²` come from the near-`0`/far-`∞` pointwise
  bounds of `a` (`ClassC.HonestCut.radGreen_near_pointwise_bound` /
  `..._far_pointwise_bound`) through `ClassC.HonestCut.radGreen_w2_slots_of_pointwise_bounds`,
  and the pairing slot `c·a·w²` from AM–GM against those two squares.
-/

/-- **The sharp per-mode weighted `L²` bound for `radGreen` with a continuous, compactly
supported (away from `0`) source.** -/
theorem radGreen_modeEnergy_of_compactSource {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : ContinuousOn c (Set.Ioi 0))
    (hsupp : ∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) :
    (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2) ^ 2
        * (∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2
            * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  -- ## the source-side facts: decay at `∞`, vanishing at `0`, the three kernel-integrability
  --    conditions and the weighted square of the source
  obtain ⟨hdec, hvy, hg0, hg0', hginf, hint4⟩ :=
    Work.FTS.PhiStar.Honesty.radGreen_source_facts_of_compactSupport (α := α) (m := m) hc hsupp
  -- ## the two derivative slots of the Green function, from continuity of `c` alone
  have hd := Work.FTS.PhiStar.Series.radGreenI_differentiableAt (α := α) (m := m) hα hc
    hg0 hg0' hginf
  have hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (Work.FTS.PhiStar.Radial.radGreen α m c)
      (deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) z :=
    fun z hz => ((hd z hz).1).hasDerivAt
  have hderiv2 : ∀ z : ℝ, 0 < z →
      HasDerivAt (deriv (Work.FTS.PhiStar.Radial.radGreen α m c))
        (deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z) z :=
    fun z hz => ((hd z hz).2).hasDerivAt
  -- ## the two weighted `L²` slots of the solution, from the near-`0`/far-`∞` pointwise bounds
  obtain ⟨hint1, hint2⟩ := Work.FTS.ClassC.HonestCut.radGreen_w2_slots_of_pointwise_bounds
    (α := α) m hderiv hderiv2
    (Work.FTS.ClassC.HonestCut.radGreen_near_pointwise_bound (α := α) hα hα4 m hm hc hvy
      hg0 hg0' hginf)
    (Work.FTS.ClassC.HonestCut.radGreen_far_pointwise_bound (α := α) hα hα4 m hc hdec
      hg0 hg0' hginf)
  -- ## the pairing slot `c·a·w²`, by AM–GM against the two squares
  have ha : ContinuousOn (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z) (Set.Ioi 0) :=
    fun z hz => (hderiv z hz).continuousAt.continuousWithinAt
  have hint3 : MeasureTheory.IntegrableOn
      (fun z : ℝ => c z * Work.FTS.PhiStar.Radial.radGreen α m c z * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) := by
    have hdom : MeasureTheory.Integrable
        (fun z : ℝ => ((c z) ^ 2 * (Work.Spaces.w z) ^ 2
          + (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2) / 2)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      simpa only [Pi.add_apply] using (hint4.add hint2).div_const 2
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
        unfold Work.Spaces.w
        refine (((continuous_const.add continuous_id).continuousOn.pow 2).div
          (continuous_id.continuousOn.pow 2) (fun z hz => ?_)).pow 2
        exact pow_ne_zero 2 (ne_of_gt hz)
      exact ((hc.mul ha).mul hw).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      rw [Real.norm_eq_abs]
      refine abs_le.mpr ⟨?_, ?_⟩
      · nlinarith [sq_nonneg (c z * Work.Spaces.w z
            + Work.FTS.PhiStar.Radial.radGreen α m c z * Work.Spaces.w z)]
      · nlinarith [sq_nonneg (c z * Work.Spaces.w z
            - Work.FTS.PhiStar.Radial.radGreen α m c z * Work.Spaces.w z)]
  -- ## the sharp per-mode energy bound, with all eight side conditions in place
  exact Work.FTS.ClassC.radGreen_modeEnergy hα hα4 m hm hc hdec hvy hg0 hg0' hginf
    hderiv hderiv2 hint1 hint2 hint3 hint4

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts.sep_HkSq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts

theorem sep_HkSq_le {α : ℝ} {C : ℝ → ℝ} {B : ℝ → ℝ}
    (hAng : MeasureTheory.IntegrableOn
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C) Work.Spaces.Iθ)
    (hRad : MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.SlotSum B) Work.Spaces.Iz) :
    Work.Spaces.HkSq α 6 (fun z θ => C θ * B z)
      ≤ (∫ θ in Work.Spaces.Iθ,
            Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ)
        * (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum B z) := by
  -- The pointwise separation bound: on `Iθ` the `ℋ⁶`-integrand of `C·B` is dominated by the
  -- product of the angular block `AngBlk α C θ` and the radial slot sum `SlotSum B z`.
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z' θ' => C θ' * B z') z θ
        ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ
          * Work.FTS.StrongPersist.SlotSum B z := by
    intro z hz θ hθ
    have h1 := Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 6)
      (C := C) (B := B) (z := z) (θ := θ) hθ
    simpa only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk,
      Work.FTS.StrongPersist.SlotSum] using h1
  -- Integrate the bound in `θ` (the radial factor is a constant there).
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z' θ' => C θ' * B z') z θ)
        ≤ (∫ θ in Work.Spaces.Iθ,
              Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ)
          * Work.FTS.StrongPersist.SlotSum B z := by
    intro z hz
    have hmaj : MeasureTheory.Integrable
        (fun θ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ
          * Work.FTS.StrongPersist.SlotSum B z) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hAng.mul_const _
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 6 (fun z' θ' => C θ' * B z') z θ
          ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ
            * Work.FTS.StrongPersist.SlotSum B z :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ)
    refine (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hmaj
      hae).trans (le_of_eq ?_)
    rw [MeasureTheory.integral_mul_const]
  -- Integrate in `z` (now the angular factor is the constant `∫_θ AngBlk`).
  have houter := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
    (hRad.const_mul (∫ θ in Work.Spaces.Iθ,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.AngBlk α C θ))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)
  rw [MeasureTheory.integral_const_mul] at houter
  rw [Work.Spaces.HkSq]
  exact houter

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceAt0_of_SmoothOpen_HkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary helpers -/

private lemma sin_two_nonneg_Iθ_s {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Work.FTS.StrongEps.EpsSqTools.sin_two_nonneg_Iθ_eps hθ

/-- Pointwise identity: on `Iθ` the weighted `(0,0)`-slot is `w²` times the `η`-weighted square. -/
private lemma zSlot_sq_eq {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h : ℝ) :
    (h * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
      = (Work.Spaces.w z)^2 * (h^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) := by
  have hs := sin_two_nonneg_Iθ_s hθ
  have hpow : ((Real.sin (2*θ))^(Work.Spaces.eta/2))^2 = (Real.sin (2*θ))^(Work.Spaces.eta) := by
    rw [Work.FTS.StrongEps.EpsSqTools.sin_rpow_sq hs]; congr 1; ring
  rw [mul_pow, div_pow, hpow, Real.rpow_neg hs]
  ring

/-- The angular sampling sequence `θ_n = 1/(n+2)`, converging to `0⁺`. -/
private noncomputable def trs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)

private lemma trs_pos (n : ℕ) : 0 < trs n := by
  change 0 < (1:ℝ) / ((n : ℝ) + 2)
  positivity

private lemma tendsto_trs : Tendsto trs atTop (𝓝[>] (0:ℝ)) := by
  have h0 : Tendsto trs atTop (𝓝 (0:ℝ)) := by
    have htop : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    change Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 2)) atTop (𝓝 (0:ℝ))
    simpa [one_div] using htop.const_div_atTop (1:ℝ)
  rw [tendsto_nhdsWithin_iff]
  exact ⟨h0, Filter.Eventually.of_forall trs_pos⟩

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
private lemma sqrt_add_le_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h2 : 0 ≤ Real.sqrt a + Real.sqrt b := add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b)^2 := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  rw [← Real.sqrt_sq h2]
  exact Real.sqrt_le_sqrt h

/-- The AM–GM inequality `x·√s ≤ (x²+s)/2` for `x, s ≥ 0`. -/
private lemma mul_sqrt_le {x s : ℝ} (_hx : 0 ≤ x) (hs : 0 ≤ s) :
    x * Real.sqrt s ≤ (x^2 + s)/2 := by
  nlinarith [sq_nonneg (x - Real.sqrt s), Real.sq_sqrt hs, Real.sqrt_nonneg s]

/-- If the slice has a trace `mu` at `0⁺`, the sampled sequence converges to `mu`. -/
private lemma limUnder_trs_eq {f : ℝ → ℝ → ℝ} {z mu : ℝ}
    (h : Tendsto (fun θ => f z θ) (𝓝[>] (0:ℝ)) (𝓝 mu)) :
    limUnder atTop (fun n : ℕ => f z (trs n)) = mu :=
  (h.comp tendsto_trs).limUnder_eq

set_option maxHeartbeats 1600000 in
theorem TraceAt0_of_SmoothOpen_HkMem {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f) :
    ∃ lam : ℝ → ℝ, Measurable lam ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (lam z))) ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), ∀ θ ∈ Set.Ioo 0 (Real.pi/4),
        (f z θ - lam z)^2
          ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
            * (∫ σ in Work.Spaces.Iθ,
                (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2)) ∧
      MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)) := by
  classical
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα0
  have hγm : 0 < Work.Spaces.gam α - 1 := by linarith
  -- the three slot functions
  let S : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2
  let T : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    (f z θ * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
  let A : ℝ → ℝ := fun z => ∫ σ in Work.Spaces.Iθ,
    (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2
  have hAnn : ∀ z : ℝ, 0 ≤ A z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun σ hσ => mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ_s hσ) _) (sq_nonneg _))
  have hSnn : ∀ z : ℝ, 0 ≤ S z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hTnn : ∀ z : ℝ, 0 ≤ T z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  -- product integrability of the two slots
  have hprod01 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ =>
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed hso hm 0 1
      (by norm_num) (by norm_num)
  have hprod0 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter 0 f z θ
        * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_z hso hm 0 (by norm_num)
  have hSintIz : MeasureTheory.Integrable S (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hprod01.integral_prod_left
  have hTintIz : MeasureTheory.Integrable T (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h : MeasureTheory.Integrable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 f z θ
          * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hprod0.integral_prod_left
    simpa only [Work.Spaces.DzIter_zero] using h
  -- a.e. slot integrability in `θ`
  have hslot01ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable
        (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hprod01.prod_right_ae
  -- the trace exists for almost every `z`
  have hQaeIz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∃ mu : ℝ, Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds mu) ∧
        ∀ θ ∈ Set.Ioo 0 (π/4),
          (f z θ - mu)^2 ≤ 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
            * A z := by
    filter_upwards [hslot01ae, Work.FTS.StrongEps.EpsSqTools.ae_pos_Iz] with z hslot hz
    exact SliceTracePth hα hz hso hslot
  -- the two measures agree
  have hIz : (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.restrict_Ioi_eq_restrict_Ici
  have hQae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ∃ mu : ℝ, Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds mu) ∧
        ∀ θ ∈ Set.Ioo 0 (π/4),
          (f z θ - mu)^2 ≤ 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
            * A z := by
    rw [hIz]; exact hQaeIz
  -- the measurable trace
  have hAe : AEMeasurable
      (fun z : ℝ => limUnder atTop (fun n : ℕ => f z (trs n)))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := aemeasurable_traceSeq hso
  set lam : ℝ → ℝ := hAe.mk (fun z : ℝ => limUnder atTop (fun n : ℕ => f z (trs n))) with hlamdef
  have hlammeas : Measurable lam := hAe.measurable_mk
  have hlamae : (fun z : ℝ => limUnder atTop (fun n : ℕ => f z (trs n)))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))] lam := hAe.ae_eq_mk
  -- the a.e. trace and the a.e. rate
  have htr : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (lam z)) := by
    filter_upwards [hQae, hlamae] with z hQ hzeq
    obtain ⟨mu, hmu, -⟩ := hQ
    rw [← hzeq, limUnder_trs_eq hmu]
    exact hmu
  have hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), ∀ θ ∈ Set.Ioo 0 (π/4),
      (f z θ - lam z)^2
        ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
          * (∫ σ in Work.Spaces.Iθ,
              (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2) := by
    filter_upwards [hQae, hlamae] with z hQ hzeq
    obtain ⟨mu, hmu, hb⟩ := hQ
    have heq : lam z = mu := by rw [← hzeq, limUnder_trs_eq hmu]
    rw [heq]
    exact hb
  -- the pointwise `L²` bound on the trace
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      (lam z)^2 * (Work.Spaces.w z)^2
        ≤ (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z := by
    filter_upwards [hQae, hlamae, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
      with z hQ hzeq hzmem
    have hz : 0 < z := hzmem
    obtain ⟨mu, hmu, hb⟩ := hQ
    have heq : lam z = mu := by rw [← hzeq, limUnder_trs_eq hmu]
    -- integrability of `θ ↦ f² sin^{-η}`
    have hzint0 : MeasureTheory.Integrable
        (fun θ => (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hsum := Work.FTS.EllipticEst.integrableOn_zSummand α 1 hso hm 0 (by norm_num)
        (z := z) (le_of_lt hz)
      have hw : ((Work.Spaces.w z)^2) ≠ 0 := by
        have h1 : (0:ℝ) < (1+z)^2 := by positivity
        have h2 : (0:ℝ) < z^2 := by positivity
        rw [Work.Spaces.w]; exact pow_ne_zero 2 (div_ne_zero (ne_of_gt h1) (ne_of_gt h2))
      refine (hsum.const_mul (((Work.Spaces.w z)^2)⁻¹)).congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ hθ => ?_)
      show ((Work.Spaces.w z)^2)⁻¹
          * (f z θ * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
        = (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
      have h1 : (f z θ * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
          = (Work.Spaces.w z)^2 * ((f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) :=
        zSlot_sq_eq hθ (f z θ)
      rw [h1, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]
    have hstep := TraceThetaStep (γ := Work.Spaces.gam α) (m := lam z) (A := A z) (u := fun θ => f z θ)
      hγ1 (hAnn z) hzint0 (fun θ hθ => by rw [heq]; exact hb θ hθ)
    have hmul := mul_le_mul_of_nonneg_right hstep (sq_nonneg (Work.Spaces.w z))
    have hAeq : A z * (Work.Spaces.w z)^2 = S z := by
      rw [mul_comm]
      exact (Work.FTS.StrongEps.EpsSqTools.slot_slice_eq hα0 hα1 f).symm
    have hYeq : (Work.Spaces.w z)^2 * (∫ θ in Work.Spaces.Iθ,
          (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) = T z := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ hθ => ?_)
      exact (zSlot_sq_eq hθ (f z θ)).symm
    calc (lam z)^2 * (Work.Spaces.w z)^2
        ≤ (200/(Work.Spaces.gam α - 1) * A z
            + 8/Real.pi * (∫ θ in Work.Spaces.Iθ,
                (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)))
          * (Work.Spaces.w z)^2 := hmul
      _ = (200/(Work.Spaces.gam α - 1)) * (A z * (Work.Spaces.w z)^2)
            + (8/Real.pi) * ((Work.Spaces.w z)^2 * (∫ θ in Work.Spaces.Iθ,
                (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta))) := by ring
      _ = (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z := by
          rw [hAeq, hYeq]
  -- the pointwise bound on `|λ z|/z`
  set Cst : ℝ := max (Real.sqrt (200/(Work.Spaces.gam α - 1))) (Real.sqrt (8/Real.pi)) with hCstdef
  have hCstnn : 0 ≤ Cst := le_max_of_le_left (Real.sqrt_nonneg _)
  have hmain : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ‖lam z / z‖ ≤ (Cst/2) * (S z + T z + 2 * (1/(z * Work.Spaces.w z))^2) := by
    filter_upwards [hpoint, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hp hzmem
    have hz : 0 < z := hzmem
    have hw : 0 < Work.Spaces.w z := by
      rw [Work.Spaces.w]; positivity
    have hS0 : 0 ≤ S z := hSnn z
    have hT0 : 0 ≤ T z := hTnn z
    have hcoef1 : 0 ≤ 200/(Work.Spaces.gam α - 1) := by positivity
    have hcoef2 : 0 ≤ 8/Real.pi := by positivity
    have hPnn : 0 ≤ (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z :=
      add_nonneg (mul_nonneg hcoef1 hS0) (mul_nonneg hcoef2 hT0)
    -- `|λ z| ≤ √P / w`
    have hsq : (lam z)^2 ≤ ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
        / (Work.Spaces.w z)^2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hp]
    have habs : |lam z| ≤ Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
        / Work.Spaces.w z := by
      rw [le_div_iff₀ hw]
      have h1 : |lam z| * Work.Spaces.w z
          = Real.sqrt ((lam z)^2 * (Work.Spaces.w z)^2) := by
        rw [Real.sqrt_mul (sq_nonneg (lam z)), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
          abs_of_pos hw]
      rw [h1]
      exact Real.sqrt_le_sqrt hp
    -- `√P ≤ Cst (√S + √T)`
    have hsqrtP : Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
        ≤ Cst * (Real.sqrt (S z) + Real.sqrt (T z)) := by
      have h1 : Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
          ≤ Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z)
            + Real.sqrt ((8/Real.pi) * T z) :=
        sqrt_add_le_sqrt (mul_nonneg hcoef1 hS0) (mul_nonneg hcoef2 hT0)
      have h2 : Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z)
          = Real.sqrt (200/(Work.Spaces.gam α - 1)) * Real.sqrt (S z) :=
        Real.sqrt_mul hcoef1 _
      have h3 : Real.sqrt ((8/Real.pi) * T z)
          = Real.sqrt (8/Real.pi) * Real.sqrt (T z) := Real.sqrt_mul hcoef2 _
      have h4 : Real.sqrt (200/(Work.Spaces.gam α - 1)) * Real.sqrt (S z)
          ≤ Cst * Real.sqrt (S z) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      have h5 : Real.sqrt (8/Real.pi) * Real.sqrt (T z) ≤ Cst * Real.sqrt (T z) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
      calc Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
          ≤ Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z)
            + Real.sqrt ((8/Real.pi) * T z) := h1
        _ = Real.sqrt (200/(Work.Spaces.gam α - 1)) * Real.sqrt (S z)
            + Real.sqrt (8/Real.pi) * Real.sqrt (T z) := by rw [h2, h3]
        _ ≤ Cst * Real.sqrt (S z) + Cst * Real.sqrt (T z) := add_le_add h4 h5
        _ = Cst * (Real.sqrt (S z) + Real.sqrt (T z)) := by ring
    -- assemble
    have hx : 0 ≤ 1/(z * Work.Spaces.w z) := by positivity
    have hstep1 : |lam z| / z ≤ Cst * ((1/(z * Work.Spaces.w z))
        * (Real.sqrt (S z) + Real.sqrt (T z))) := by
      have hz1 : (0:ℝ) < z := hz
      have h0 : |lam z| / z ≤ (Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z
          + (8/Real.pi) * T z) / Work.Spaces.w z) / z := by
        exact div_le_div_of_nonneg_right habs (le_of_lt hz1)
      have h1 : (Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
            / Work.Spaces.w z) / z
          = (1/(z * Work.Spaces.w z))
            * Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z) := by
        field_simp
      rw [h1] at h0
      calc |lam z| / z
          ≤ (1/(z * Work.Spaces.w z))
            * Real.sqrt ((200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z) := h0
        _ ≤ (1/(z * Work.Spaces.w z)) * (Cst * (Real.sqrt (S z) + Real.sqrt (T z))) :=
            mul_le_mul_of_nonneg_left hsqrtP hx
        _ = Cst * ((1/(z * Work.Spaces.w z)) * (Real.sqrt (S z) + Real.sqrt (T z))) := by ring
    have hstep2 : Cst * ((1/(z * Work.Spaces.w z)) * (Real.sqrt (S z) + Real.sqrt (T z)))
        ≤ (Cst/2) * (S z + T z + 2 * (1/(z * Work.Spaces.w z))^2) := by
      have h1 : (1/(z * Work.Spaces.w z)) * Real.sqrt (S z)
          ≤ ((1/(z * Work.Spaces.w z))^2 + S z)/2 := mul_sqrt_le hx hS0
      have h2 : (1/(z * Work.Spaces.w z)) * Real.sqrt (T z)
          ≤ ((1/(z * Work.Spaces.w z))^2 + T z)/2 := mul_sqrt_le hx hT0
      have h3 : (1/(z * Work.Spaces.w z)) * (Real.sqrt (S z) + Real.sqrt (T z))
          ≤ ((1/(z * Work.Spaces.w z))^2 + S z)/2 + ((1/(z * Work.Spaces.w z))^2 + T z)/2 := by
        rw [mul_add]; linarith
      calc Cst * ((1/(z * Work.Spaces.w z)) * (Real.sqrt (S z) + Real.sqrt (T z)))
          ≤ Cst * (((1/(z * Work.Spaces.w z))^2 + S z)/2
              + ((1/(z * Work.Spaces.w z))^2 + T z)/2) :=
            mul_le_mul_of_nonneg_left h3 hCstnn
        _ = (Cst/2) * (S z + T z + 2 * (1/(z * Work.Spaces.w z))^2) := by ring
    have hnorm : ‖lam z / z‖ = |lam z| / z := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hz]
    rw [hnorm]
    exact hstep1.trans hstep2
  -- integrability of the majorant
  have hIoiIz : Set.Ioi (0:ℝ) ⊆ Work.Spaces.Iz := by
    intro z hz
    simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hz ⊢
    exact le_of_lt hz
  have hSint : MeasureTheory.Integrable S (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    hSintIz.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hIoiIz)
  have hTint : MeasureTheory.Integrable T (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    hTintIz.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hIoiIz)
  have hxint : MeasureTheory.Integrable
      (fun z : ℝ => (1 / (z * Work.Spaces.w z))^2)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := inv_zw_sq_integrableOn.1
  have hGint : MeasureTheory.Integrable
      (fun z : ℝ => (Cst/2) * (S z + T z + 2 * (1/(z * Work.Spaces.w z))^2))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    ((hSint.add hTint).add (hxint.const_mul 2)).const_mul (Cst/2)
  have hmeasdiv : AEStronglyMeasurable (fun z : ℝ => lam z / z)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    (hlammeas.div measurable_id).aestronglyMeasurable
  have hIntOn : MeasureTheory.IntegrableOn (fun z : ℝ => lam z / z) (Set.Ioi (0:ℝ)) :=
    MeasureTheory.Integrable.mono' hGint hmeasdiv hmain
  have hcomp := (integrable_comp_exp (fun z : ℝ => lam z / z)).mpr hIntOn
  have hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)) :=
    hcomp.congr (Filter.Eventually.of_forall fun u => by
      show Real.exp u • (lam (Real.exp u) / Real.exp u) = lam (Real.exp u)
      rw [smul_eq_mul, mul_comm, div_mul_cancel₀ _ (Real.exp_ne_zero u)])
  exact ⟨lam, hlammeas, htr, hbd, hint⟩

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Tracing the weighted `ℋ¹`-bound down to the `ε`-space.**

Let `f` be smooth on the open quadrant, with both angular traces vanishing at every
`z > 0` (`f z θ → 0` as `θ → 0⁺` and as `θ → (π/2)⁻`) and with `ℋ¹`-membership
`HkMem α 1 f`.  Then `f` belongs to the weighted space `X = (EpsSq, EpsMem)` of the
`ε`-scheme, with the *sharp* `1/(γ-1)²`-degradation of the constant:

`EpsSq α f ≤ C/(γ-1)² · HkSq α 1 f`,  `γ = 1 + α/10`,  for `α ∈ (0,1]`.

Route: the only `γ`-weighted `L²`-slot of `ℋ¹` is the `(0,1)`-slot
`(mixed 0 1 f · Wt)²`, and on every slice (`z > 0`, a.e. `z ∈ Iz`) the weak-range
angular Hardy inequality (`hardySinGam_weak`, with the vanishing traces at `0` and
`π/2`) bounds the `sin(2θ)^{-γ}`-weighted `L²` of `f` by `4/(γ-1)²` times the
`sin(2θ)^{2-γ}`-weighted `L²` of `∂_θ f`, i.e. exactly by that slot; the common
factor `w(z)²` cancels, and the outer `z`-integral is the comparison
`∫_z ∫_θ (mixed 0 1 f · Wt)² ≤ HkSq α 1 f` of the level-`1` slot. -/
theorem TraceToEpsMem :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 1 f →
      (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) →
      (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ => f z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0)) →
      Work.FTS.StrongEps.EpsMem α f ∧
        Work.FTS.StrongEps.EpsSq α f
          ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 f := by
  obtain ⟨CS, hCSpos, hCS⟩ := EpsSliceLe
  refine ⟨CS, hCSpos, fun α hα f hso hm ht1 ht2 => ?_⟩
  obtain ⟨hα0, hα1⟩ := hα
  -- the `(0,1)`-slot of `ℋ¹`
  obtain ⟨hslotInt, hslotLe⟩ := Slot01LeHkSq1 hso hm
  have hprod := Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed
    (α := α) (k := 1) (F := f) hso hm 0 1 (by norm_num) (by norm_num)
  have hslot_ae := hprod.prod_right_ae
  have hae_pos := Work.FTS.StrongEps.EpsSqTools.ae_pos_Iz
  -- the slicewise Hardy bound, for almost every `z`
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ CS / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    filter_upwards [hslot_ae, hae_pos] with z hslot hz
    have hcd : ContDiffOn ℝ 1 (fun θ => f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (hso.curry_θ hz).of_le (show (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder from by
        simp [Work.Stability.smoothOrder])
    exact hCS α (show α ∈ Set.Ioc 0 1 from ⟨hα0, hα1⟩) f z hz hcd (ht1 z hz) (ht2 z hz) hslot
  have hEint' : MeasureTheory.Integrable
      (fun z : ℝ => CS / (Work.Spaces.gam α - 1) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hslotInt.const_mul _
  -- the outer `z`-integral
  have hmain : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      ≤ CS / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 f := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hslotLe (div_nonneg hCSpos.le (sq_nonneg _)))
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ => sq_nonneg _) hEint' ?_
    filter_upwards [hpoint] with z hz using hz.2
  refine ⟨?_, ?_⟩
  · -- `EpsMem α f`
    have hAESM : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (ContinuousOn.pow (ContinuousOn.mul (hso.forall 0).continuousOn
          (Work.FTS.StrongEps.EpsSqTools.continuousOn_epsW α)) 2)
    have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.HasFiniteIntegral
          (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      filter_upwards [hpoint] with z hz using hz.1.2
    have hzInt : MeasureTheory.HasFiniteIntegral
        (fun z : ℝ => ∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => ∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        hAESM.norm.integral_prod_right'
      have hbdd : (fun z : ℝ => ‖∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖)
          ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          (fun z : ℝ => CS / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
        filter_upwards [hpoint] with z hz
        rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => norm_nonneg _)]
        refine le_trans (le_of_eq ?_) hz.2
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => Real.norm_of_nonneg (sq_nonneg _))
      exact (MeasureTheory.Integrable.mono' hEint' haesm hbdd).2
    have hmeas : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_restrict]
    rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hmeas]
    exact ⟨hAESM, (MeasureTheory.hasFiniteIntegral_prod_iff' hAESM).mpr ⟨hslice, hzInt⟩⟩
  · calc Work.FTS.StrongEps.EpsSq α f
        = ∫ z in Work.Spaces.Iz,
            ∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2 := rfl
      _ ≤ CS / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 f := hmain

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceWeightedL2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000




end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfileDzSlot.EpsSq_dzIter_le_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfileDzSlot

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- Almost every `θ ∈ Iθ = [0,π/2]` lies in the open interval `(0,π/2)` (the two endpoints are
null).  Used to transfer the pointwise identities that hold only on the *open* quadrant. -/
theorem ae_mem_Ioo_Iθ_aux :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  change ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- **The slicewise Hardy transfer for the pure `D_z`-slot of the `ε`-scheme.**

The same statement as the sibling module
`Submission.Work.FTS.StrongEps.EpsRLX.ProfileDzSlot.hardy_slice_dzIter_le`; kept here so that the
main theorem below is self-contained.  For a.e. `z > 0` the `θ`-slice `u := D_z^b f z ·` is `C¹`
on `(0,π/2)` with vanishing traces at both endpoints (from `BdryTraces α 6 f`, `a = 0` slots), so
the weighted Hardy inequality `hardySinGam_weak` with `c = γ` gives

`∫_θ sin(2θ)^{-γ} u² ≤ C/(γ-1)² ∫_θ sin(2θ)^{2-γ}(u')²`,

which is the stated bound because `(epsW)² = w² sin(2θ)^{-γ}` on `Iθ` and
`sin(2θ)·u' = mixed b 1 f` a.e. on `Iθ` (the identity holds on the open quadrant). -/
theorem hardy_slice_local :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f : ℝ → ℝ → ℝ}, α ∈ Set.Ioc 0 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.Nonlin.BdryTraces α 6 f →
      ∀ b : ℕ, b ≤ 4 →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          MeasureTheory.Integrable
            (fun θ : ℝ => (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ C / (Work.Spaces.gam α - 1) ^ 2
            * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
        ∧ MeasureTheory.Integrable
            (fun θ : ℝ =>
              (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.hardySinGam_weak
  refine ⟨CH, hCHpos, ?_⟩
  intro α f hα hso htr b hb hslot_ae
  filter_upwards [hslot_ae, Work.FTS.StrongEps.EpsSqTools.ae_pos_Iz] with z hslot hz
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα.1
  have hγ32 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith [hα.2]
  -- the slice is `C¹` on the open interval
  have hu_cd : ContDiffOn ℝ 1 (fun θ : ℝ => Work.Spaces.DzIter b f z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((hso.DzIter b).curry_θ hz).of_le
      (show (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder from by
        simp [Work.Stability.smoothOrder])
  -- the vanishing traces at both endpoints, from `BdryTraces α 6 f`
  have htrb := htr 0 b (by omega)
  have ht1 : Tendsto (fun θ : ℝ => Work.Spaces.DzIter b f z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Work.FTS.H2.HQ.tendsto_nhdsGT_zero_of_traces α hα.1
      (u := fun θ : ℝ => Work.Spaces.mixed b 0 f z θ)
      (htrb.2 z (Set.mem_Ioi.mpr hz)).1
  have ht2 : Tendsto (fun θ : ℝ => Work.Spaces.DzIter b f z θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
    Work.FTS.H2.HQ.tendsto_nhdsLT_zero_of_traces α hα.1
      (u := fun θ : ℝ => Work.Spaces.mixed b 0 f z θ)
      (htrb.2 z (Set.mem_Ioi.mpr hz)).2
  -- the identity `D_θ(D_z^b f) = mixed b 1 f` on the open quadrant
  have hEqOn : Set.EqOn
      (Function.uncurry (Work.Spaces.DthIter 1 (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.mixed b 1 f))
      (Work.FTS.EllipticEst.Q0) :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      (V := Work.FTS.EllipticEst.Q0) (g := f)
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hso) b 1
  have hDth : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.mixed b 1 f z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := by
    intro θ hθ
    have hm : Work.Spaces.mixed b 1 f z θ
        = Work.Spaces.DthIter 1 (Work.Spaces.DzIter b f) z θ :=
      (hEqOn (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)).symm
    have hD : Work.Spaces.DthIter 1 (Work.Spaces.DzIter b f) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := rfl
    rw [hm, hD]
  -- the weight algebra, a.e. in `θ`
  have hsin2_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
        = Work.Spaces.w z ^ 2 * (Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2) := by
    filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hWt := Work.FTS.StrongEps.EpsSqTools.Wt_sq_eq_eps (α := α) (z := z) hθI
    have hpth := Work.FTS.H2.pth_sq_mul_sin_eq α hα.1 hα.2
      (Work.Spaces.DzIter b f) z θ hθI
    have hDth' : Work.Spaces.Dth (Work.Spaces.DzIter b f) z θ = Work.Spaces.mixed b 1 f z θ := by
      have h1 : Work.Spaces.Dth (Work.Spaces.DzIter b f) z θ
          = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := rfl
      rw [h1, ← hDth θ hθ]
    exact (calc Work.Spaces.w z ^ 2 * (Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2)
        = Work.Spaces.w z ^ 2 * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)) := by ring
      _ = Work.Spaces.w z ^ 2 * ((Work.Spaces.Dth (Work.Spaces.DzIter b f) z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by rw [hpth]
      _ = Work.Spaces.w z ^ 2 * ((Work.Spaces.mixed b 1 f z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by rw [hDth']
      _ = (Work.Spaces.mixed b 1 f z θ) ^ 2
            * (Work.Spaces.w z ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by ring
      _ = (Work.Spaces.mixed b 1 f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by rw [hWt]
      _ = (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [mul_pow]).symm
  -- Hardy's derivative-side integrability, transported from the slot
  have hRwire : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hslot.congr hsin2_ae
  have hw_ne : Work.Spaces.w z ^ 2 ≠ 0 := by
    have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    have h2 : (0 : ℝ) < z ^ 2 := by positivity
    rw [Work.Spaces.w]
    exact pow_ne_zero 2 (div_ne_zero (ne_of_gt h1) (ne_of_gt h2))
  have hRint : MeasureTheory.Integrable
      (fun θ : ℝ => Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (hRwire.const_mul ((Work.Spaces.w z ^ 2)⁻¹)).congr ?_
    filter_upwards with θ
    rw [← mul_assoc, inv_mul_cancel₀ hw_ne, one_mul]
  obtain ⟨hHint, hHle⟩ := hCH (Work.Spaces.gam α)
    (fun θ : ℝ => Work.Spaces.DzIter b f z θ) hγ1 hγ32 hu_cd ht1 ht2
    (by simpa only [MeasureTheory.IntegrableOn, Work.Spaces.pth] using hRint)
  have hHle' : (∫ θ in Work.Spaces.Iθ,
        Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.DzIter b f z θ) ^ 2)
      ≤ CH / (Work.Spaces.gam α - 1) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2 := by
    simpa only [Work.Spaces.pth] using hHle
  -- the `θ`-integral identity of the two slot integrals
  have hsinteq : Work.Spaces.w z ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hsin2_ae] with θ hθ
    exact hθ.symm
  -- the `θ`-integrability of the `epsW`-slice
  have heps_int : MeasureTheory.Integrable
      (fun θ : ℝ => (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (hHint.const_mul (Work.Spaces.w z ^ 2)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun θ hθ => ?_
    show Work.Spaces.w z ^ 2 * (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.DzIter b f z θ) ^ 2)
      = (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2
    have h1 : (Work.FTS.StrongEps.epsW α z θ) ^ 2
        = Work.Spaces.w z ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) :=
      Work.FTS.StrongEps.EpsSqTools.epsW_sq_eq (α := α) (z := z) hθ
    rw [mul_pow, h1]
    ring
  refine ⟨?_, heps_int⟩
  calc (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      = Work.Spaces.w z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter b f z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) :=
        Work.FTS.StrongEps.EpsSqTools.epsSq_slice_eq α z (Work.Spaces.DzIter b f)
    _ = Work.Spaces.w z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.DzIter b f z θ) ^ 2 := by
        congr 1
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => by ring)
    _ ≤ Work.Spaces.w z ^ 2 * (CH / (Work.Spaces.gam α - 1) ^ 2
          * ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hHle' (sq_nonneg _)
    _ = CH / (Work.Spaces.gam α - 1) ^ 2 * (Work.Spaces.w z ^ 2
          * ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2) := by ring
    _ = CH / (Work.Spaces.gam α - 1) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [hsinteq]

/-- **The pure `D_z`-slots of the `ε`-scheme are dominated by the `ℋ⁶`-norm.**

For `α ∈ (0,1]`, `f` smooth on the open quadrant, honestly in `ℋ⁶` and with the boundary traces
`BdryTraces α 6 f`, every radial slot `D_z^b f` (`b ≤ 4`) is in the weighted space `X` of the
`ε`-scheme (`EpsMem`), with weighted energy bounded by `C/(γ-1)² · |f|²_{ℋ⁶}` (`γ = 1 + α/10`).

The energy of the slot carries the *mixed* weight `w² sin(2θ)^{-γ}`, which is more singular at
the angular boundary than the pure `D_z`-weight `w² sin(2θ)^{-η}` of `HkIntegrand`; the extra
factor `(γ-1)^{-2}` pays for the angular weighted Hardy inequality
(`Work.FTS.StrongEps.EpsSqTools.hardySinGam_weak`) which trades the two units of
`sin(2θ)^{-γ}` on `D_z^b f` for the derivative block `D_z^b D_θ f = mixed b 1 f`, i.e. for the
`(b,1)`-slot of `HkIntegrand α 6 f` (`Work.FTS.StrongEps.EpsRLX.slot_mixed_le_HkSq`).  The
boundary traces in `BdryTraces α 6 f` (the `a = 0` slots) are exactly the vanishing conditions
of the Hardy inequality. -/
theorem EpsSq_dzIter_le_HkSq :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.Nonlin.BdryTraces α 6 f → ∀ b : ℕ, b ≤ 4 →
      Work.FTS.StrongEps.EpsMem α (Work.Spaces.DzIter b f) ∧
      Work.FTS.StrongEps.EpsSq α (Work.Spaces.DzIter b f)
        ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C, hCpos, hC⟩ := hardy_slice_local
  refine ⟨C, hCpos, ?_⟩
  intro α hα f hso hm htr b hb
  -- The `(b,1)` mixed slot: product integrability, a.e. slice integrability, and its value.
  have hslot_prod :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed (α := α) (k := 6)
      hso hm b 1 (by norm_num) (by omega)
  have hslot_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable
        (fun θ : ℝ => (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hslot_prod.prod_right_ae
  have hslot_le :=
    Work.FTS.StrongEps.EpsRLX.slot_mixed_le_HkSq (α := α) (k := 6) hso hm (j := b) (i := 1)
      (by norm_num) (by omega)
  -- the slicewise Hardy transfer
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ C / (Work.Spaces.gam α - 1) ^ 2
          * ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      ∧ MeasureTheory.Integrable
          (fun θ : ℝ =>
            (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hC hα hso htr b hb hslot_ae
  have hKpos : (0 : ℝ) ≤ C / (Work.Spaces.gam α - 1) ^ 2 :=
    div_nonneg hCpos.le (by positivity)
  refine ⟨?_, ?_⟩
  · -- `EpsMem α (DzIter b f)`
    have hAESM : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          (Work.Spaces.DzIter b f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (ContinuousOn.pow
          (ContinuousOn.mul (hso.DzIter b).continuousOn
            (Work.FTS.StrongEps.EpsSqTools.continuousOn_epsW α)) 2)
    have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.HasFiniteIntegral
          (fun θ : ℝ => (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      filter_upwards [hpoint] with z hz using hz.2.2
    have hzInt : MeasureTheory.HasFiniteIntegral
        (fun z : ℝ => ∫ θ, ‖(Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => ∫ θ, ‖(Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        hAESM.norm.integral_prod_right'
      have hbdd : (fun z : ℝ => ‖∫ θ,
            ‖(Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖)
          ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          (fun z : ℝ => C / (Work.Spaces.gam α - 1) ^ 2
            * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
        filter_upwards [hpoint] with z hz
        rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => norm_nonneg _)]
        refine le_trans (le_of_eq ?_) hz.1
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => Real.norm_of_nonneg (sq_nonneg _))
      exact (MeasureTheory.Integrable.mono' (hslot_le.1.const_mul _) haesm hbdd).2
    have hmeas : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]
    rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hmeas]
    exact ⟨hAESM, (MeasureTheory.hasFiniteIntegral_prod_iff' hAESM).mpr ⟨hslice, hzInt⟩⟩
  · -- the energy bound
    have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ C / (Work.Spaces.gam α - 1) ^ 2
          * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z =>
          MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
        (hslot_le.1.const_mul _) ?_
      filter_upwards [hpoint] with z hz using hz.1
    calc Work.FTS.StrongEps.EpsSq α (Work.Spaces.DzIter b f)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2 := rfl
      _ ≤ C / (Work.Spaces.gam α - 1) ^ 2
            * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := hmain
      _ ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_left hslot_le.2 hKpos

end Work.FTS.StrongEps.EpsRLX.ProfileDzSlot
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfileMixedSlot.EpsSq_mixed_le_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfileMixedSlot

set_option autoImplicit false

/-! ## The two weights agree after squaring -/

/-- **The weighted square of a mixed slot does not depend on which of the two weights
(`epsW` of the `ε`-scheme, `Wt` of `ℋ^k`) is used**: at an angle `θ ∈ Iθ` they have the common
value `(D_z^jD_θ^i f)² · w(z)² · sin(2θ)^{-γ}`. -/
theorem mixed_epsW_sq_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed j i f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2
      = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  simp only [mul_pow, Work.FTS.StrongEps.EpsSqTools.epsW_sq_eq hθ,
    Work.FTS.StrongEps.EpsSqTools.Wt_sq_eq_eps hθ]

/-- The weight `epsW α z θ = w(z)/sin(2θ)^{γ/2}` of the `ε`-scheme agrees with the mixed-block
weight `Wt α z θ = w(z)·sin(2θ)^{-γ/2}` at every angle `θ ∈ Iθ`. -/
theorem epsW_eq_Wt_of_mem_Iθ {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.StrongEps.epsW α z θ = Work.Spaces.Wt α z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.StrongEps.EpsSqTools.sin_two_nonneg_Iθ_eps hθ
  rw [Work.FTS.StrongEps.epsW, Work.Spaces.Wt, Work.Spaces.wTheta, div_eq_mul_inv,
    ← Real.rpow_neg hs]

/-! ## The domain measure -/

/-- The product of the two restricted measures on the domain `Iz × Iθ` is the restriction of the
volume of `ℝ × ℝ`. -/
theorem domain_restrict_eq :
    (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]

/-- `EpsMem` re-expressed as integrability for the product of the two restricted measures on the
domain, `(volume.restrict Iz).prod (volume.restrict Iθ)` — the form in which the product
integrability of a slot is available. -/
theorem EpsMem_iff_integrable_prod {α : ℝ} {f : ℝ → ℝ → ℝ} :
    Work.FTS.StrongEps.EpsMem α f ↔ MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, domain_restrict_eq]

/-! ## The main estimate -/

theorem EpsSq_mixed_le_HkSq {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    Work.FTS.StrongEps.EpsMem α (Work.Spaces.mixed j i f) ∧
    Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed j i f) ≤ Work.Spaces.HkSq α k f := by
  have hsq : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      (Work.Spaces.mixed j i f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
    fun z θ hθ => mixed_epsW_sq_eq α f j i hθ
  refine ⟨?_, ?_⟩
  · -- the membership: product integrability of the slot, transported from `Wt` to `epsW`
    rw [EpsMem_iff_integrable_prod]
    have hprod := Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed
      hso hm j i hi hij
    refine hprod.congr ?_
    have hae : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod
        (volume.restrict Work.Spaces.Iθ)), p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
      rw [← domain_restrict_eq]
      exact MeasureTheory.ae_restrict_mem (μ := (volume : Measure (ℝ × ℝ)))
        (measurableSet_Ici.prod measurableSet_Icc)
    filter_upwards [hae] with p hp
    simp only [Function.uncurry]
    exact (hsq p.1 p.2 (Set.mem_prod.mp hp).2).symm
  · -- the size bound: the slot is one summand of the `ℋ^k`-integrand
    obtain ⟨_, hle⟩ := Work.FTS.StrongEps.EpsRLX.slot_mixed_le_HkSq hso hm
      (j := j) (i := i) hi hij
    rw [Work.FTS.StrongEps.EpsSq]
    refine le_trans (le_of_eq ?_) hle
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with z
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with θ hθ
    exact hsq z θ hθ

end Work.FTS.StrongEps.EpsRLX.ProfileMixedSlot
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_Pz_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Two transport lemmas for the `X`-structure -/

/-- **The membership `EpsMem` only depends on the pointwise values.**  `EpsMem α f` is the
integrability of `(f · epsW α)²` on `Iz ×ˢ Iθ`, so it transfers along a pointwise equality. -/
theorem EpsMem_congr {α : ℝ} {f g : Work.FTS.Galerkin.Fn} (h : ∀ z θ, f z θ = g z θ) :
    Work.FTS.StrongEps.EpsMem α f → Work.FTS.StrongEps.EpsMem α g := by
  intro hf
  have heq : (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      = fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := by
    funext p
    rw [h p.1 p.2]
  rw [Work.FTS.StrongEps.EpsMem] at hf ⊢
  rwa [heq] at hf

/-- **The pointwise form of the projected difference.**  `Pz f - Pz g = (f - g) - c · bump` with
`c = (L₁₂ f 0 - L₁₂ g 0)/pzNorm` (the projection is affine with linear part the identity). -/
theorem Pz_sub_apply (f g : Work.FTS.Galerkin.Fn) (z θ : ℝ) :
    (Work.FTS.StrongEps.Pz f - Work.FTS.StrongEps.Pz g) z θ
      = (f z θ - g z θ)
        - ((Work.Construction.L12 f 0 - Work.Construction.L12 g 0) / Work.FTS.StrongEps.pzNorm)
            * Work.FTS.StrongEps.bump z θ := by
  simp only [Pi.sub_apply, Work.FTS.StrongEps.Pz_apply]
  ring

/-! ## The target -/

/-- **`P₀` is bounded on the weighted space `X`** (difference form), with a constant independent of
`α ∈ (0,1]`: for `f`, `g` in the open-quadrant class with honest `ℋ⁴`-size and with the difference
in `X`, the projected difference is in `X` and

  `EpsSq α (Pz f - Pz g) ≤ C · EpsSq α (f - g)`.

See the module docstring for the route; the two inputs are
`EpsSqTools.L12_zero_le_EpsSq` (`|L₁₂ h 0| ≤ C₁ √(EpsSq α h)`) and
`EpsSqTools.EpsSq_sub_smul_bumpP` (`EpsSq α ((f - g) - c • bump) ≤ 2 EpsSq α (f - g) + B c²`). -/
theorem EpsSq_Pz_sub_le : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 4 g →
      Work.FTS.StrongEps.EpsMem α (fun z θ => f z θ - g z θ) →
        Work.FTS.StrongEps.EpsMem α
            (fun z θ => Work.FTS.StrongEps.Pz f z θ - Work.FTS.StrongEps.Pz g z θ) ∧
        Work.FTS.StrongEps.EpsSq α
            (fun z θ => Work.FTS.StrongEps.Pz f z θ - Work.FTS.StrongEps.Pz g z θ)
          ≤ C * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := L12_zero_le_EpsSq
  obtain ⟨B, hBpos, hB⟩ := EpsSq_sub_smul_bumpP
  refine ⟨2 + B * C₁ ^ 2 / pzNorm ^ 2, ?_, ?_⟩
  · have h1 : 0 ≤ B * C₁ ^ 2 / pzNorm ^ 2 :=
      div_nonneg (mul_nonneg hBpos.le (sq_nonneg _)) (sq_nonneg _)
    linarith
  intro α hα f g hf hg hmf hmg hmem
  -- `L₁₂` is additive on the honest `ℋ⁴`-class at `z = 0 ∈ Iz = Ici 0`
  have hL12 : Work.Construction.L12 (fun z θ => f z θ - g z θ) 0
      = Work.Construction.L12 f 0 - Work.Construction.L12 g 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hf hg hmf hmg 0 (Set.mem_Ici.mpr le_rfl)
  set c : ℝ := (Work.Construction.L12 f 0 - Work.Construction.L12 g 0) / pzNorm with hcdef
  have hpt : ∀ z θ : ℝ, (Work.FTS.StrongEps.Pz f - Work.FTS.StrongEps.Pz g) z θ
      = (f z θ - g z θ) - c * Work.FTS.StrongEps.bump z θ := by
    intro z θ
    rw [Pz_sub_apply f g z θ, hcdef]
  obtain ⟨hmem', hbd⟩ := hB α hα f g hf hg c hmem
  have hc : c = Work.Construction.L12 (fun z θ => f z θ - g z θ) 0 / pzNorm := by
    rw [hcdef, ← hL12]
  have hcsq : c ^ 2 ≤ C₁ ^ 2 / pzNorm ^ 2
      * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) := by
    have hL := hC₁ α hα (fun z θ => f z θ - g z θ) hmem
    have hS : 0 ≤ Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) :=
      Work.FTS.StrongEps.EpsSq_nonneg α _
    have hsq : (Work.Construction.L12 (fun z θ => f z θ - g z θ) 0) ^ 2
        ≤ (C₁ * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ))) ^ 2 := by
      rcases abs_le.mp hL with ⟨hlo, hhi⟩
      exact sq_le_sq' hlo hhi
    have hrhs : (C₁ * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ))) ^ 2
        = C₁ ^ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) := by
      rw [mul_pow, Real.sq_sqrt hS]
    rw [hc, div_pow]
    calc (Work.Construction.L12 (fun z θ => f z θ - g z θ) 0) ^ 2 / pzNorm ^ 2
        ≤ (C₁ ^ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ)) / pzNorm ^ 2 :=
          div_le_div_of_nonneg_right (by rw [← hrhs]; exact hsq) (sq_nonneg pzNorm)
      _ = C₁ ^ 2 / pzNorm ^ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) := by
          ring
  constructor
  · exact EpsMem_congr (fun z θ => (hpt z θ).symm) hmem'
  · calc Work.FTS.StrongEps.EpsSq α
          (fun z θ => Work.FTS.StrongEps.Pz f z θ - Work.FTS.StrongEps.Pz g z θ)
        = Work.FTS.StrongEps.EpsSq α
            (fun z θ => (f z θ - g z θ) - c * Work.FTS.StrongEps.bump z θ) :=
          Work.FTS.StrongEps.EpsSq_congr (fun z θ => hpt z θ)
      _ ≤ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) + B * c ^ 2 := hbd
      _ ≤ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ)
            + B * (C₁ ^ 2 / pzNorm ^ 2
                * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ)) :=
          (by linarith [mul_le_mul_of_nonneg_left hcsq hBpos.le])
      _ = (2 + B * C₁ ^ 2 / pzNorm ^ 2)
            * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) := by ring

end Work.FTS.StrongEps.EpsSqTools
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_mixed_Jeps_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## The weight `epsW` is continuous on the open quadrant -/

theorem continuousOn_epsW_quad (α : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.FTS.StrongEps.epsW α q.1 q.2)
      Work.FTS.StrongEps.Quad :=
  (Work.FTS.StrongEps.JepsHkMem.continuousOn_Wt α).congr
    (fun _ hq => epsW_eq_Wt_of_mem_Iθ ⟨hq.2.1.le, hq.2.2.le⟩)

/-! ## `EpsSq` against the iterated `lintegral` of its integrand -/

theorem ofReal_EpsSq_le_iter (α : ℝ) (g : ℝ → ℝ → ℝ) :
    ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α g)
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) := by
  have hψ : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have h1 : ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α g)
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) :=
    Work.FTS.StrongEps.StepFacts.ofReal_integral_le_lintegral_ofReal hψ
  refine h1.trans (lintegral_mono fun z => ?_)
  exact Work.FTS.StrongEps.StepFacts.ofReal_integral_le_lintegral_ofReal
    (fun θ => sq_nonneg _)

/-! ## The integration chain -/

theorem iter_le_of_pointwise
    {α c δ C₀ Kmass : ℝ} {Λ : ℝ × ℝ → ℝ} {f g : ℝ → ℝ → ℝ}
    (hC₀ : 0 ≤ C₀) (hKmass : 0 ≤ Kmass) (hΛ0 : ∀ p : ℝ × ℝ, 0 ≤ Λ p)
    (hΛfin : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|)))
      ≤ ENNReal.ofReal Kmass)
    (hMemF : Work.FTS.StrongEps.EpsMem α f)
    (hJac : ∀ s ζ p₁ p₂ : ℝ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac (s - p₁) (ζ - p₂))
    (hFcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2)
      Work.FTS.StrongEps.Quad)
    (hAe : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2)
        * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
              (Work.FTS.StrongEps.thShift z.1.2 z.2.2)
            * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
                (Work.FTS.StrongEps.thShift z.1.2 z.2.2)) ^ 2))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume))
    (hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal ((g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ ENNReal.ofReal C₀ * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2))
      ≤ ENNReal.ofReal (C₀ * Kmass * Work.FTS.StrongEps.EpsSq α f) := by
  have hEpsSq0 : 0 ≤ Work.FTS.StrongEps.EpsSq α f := Work.FTS.StrongEps.EpsSq_nonneg α f
  -- Step 1: the pointwise bound, integrated twice
  have h1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal C₀ * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
    MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)
      (fun z hz => MeasureTheory.setLIntegral_mono'
        (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) (fun θ hθ => hP z hz θ hθ))
  -- Step 2: the constant `C₀` comes out of the two integrations
  have h2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal C₀ * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2))
      = ENNReal.ofReal C₀ * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)) := by
    have hinner : ∀ z : ℝ, (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal C₀
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)))
        = ENNReal.ofReal C₀ * ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
      fun z => MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    simp only [hinner]
    exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Step 3: Tonelli -- the `p`-integration is exchanged with the `(z,θ)`-integration
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Λ p) * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2))
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (∫⁻ z in Work.Spaces.Iz,
          ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)
              * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)) := by
    have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Λ p) * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)
              * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) ^ 2))
        = ∫⁻ q : ℝ × ℝ, (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift q.1 p.1)
                  (Work.FTS.StrongEps.thShift q.2 p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift q.1 p.1)
                    (Work.FTS.StrongEps.thShift q.2 p.2)) ^ 2))
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
              (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
      exact (MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ∫⁻ p : ℝ × ℝ,
            ENNReal.ofReal (Λ p) * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift q.1 p.1)
                  (Work.FTS.StrongEps.thShift q.2 p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift q.1 p.1)
                    (Work.FTS.StrongEps.thShift q.2 p.2)) ^ 2))
        (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
          rw [← Measure.prod_restrict (μ := MeasureTheory.volume)
            (ν := MeasureTheory.volume) _ _]
          exact hAe.lintegral_prod_right')).symm
    rw [hL]
    rw [MeasureTheory.lintegral_lintegral_swap
      (μ := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (ν := MeasureTheory.volume) hAe]
    refine lintegral_congr fun p => ?_
    rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Λ p)) _ ENNReal.ofReal_ne_top]
    congr 1
    rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
            (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
    exact MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ENNReal.ofReal
        ((f (Work.FTS.StrongEps.zShift q.1 p.1) (Work.FTS.StrongEps.thShift q.2 p.2)
          * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift q.1 p.1)
              (Work.FTS.StrongEps.thShift q.2 p.2)) ^ 2))
      (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
        rw [← Measure.prod_restrict (μ := MeasureTheory.volume)
          (ν := MeasureTheory.volume) _ _]
        exact Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_slice (G := fun z θ =>
          (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) (hFcont.pow 2) p)
  -- Step 4: the shift step
  have h4 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (∫⁻ z in Work.Spaces.Iz,
        ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)))
      ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (ENNReal.ofReal
          (Real.exp (δ * (|p.1| + |p.2|))) * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)) :=
    lintegral_mono fun p => mul_le_mul_of_nonneg_left
      (Work.FTS.StrongEps.EpsSqTools.shift_step (f := f) hMemF (δ := δ) hJac p) zero_le
  -- Step 5: combine the two exponentials and pull `EpsSq α f` out
  have h5 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (ENNReal.ofReal
        (Real.exp (δ * (|p.1| + |p.2|))) * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)))
      = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f) := by
    rw [← MeasureTheory.lintegral_mul_const' (ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)) _
      ENNReal.ofReal_ne_top]
    refine lintegral_congr fun p => ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (hΛ0 p)]
  have h6 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|))))
      * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)
      ≤ ENNReal.ofReal Kmass * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f) :=
    mul_le_mul_of_nonneg_right hΛfin zero_le
  have h7 : ENNReal.ofReal Kmass * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)
      = ENNReal.ofReal (Kmass * Work.FTS.StrongEps.EpsSq α f) :=
    (ENNReal.ofReal_mul hKmass).symm
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal C₀ * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := h1
    _ = ENNReal.ofReal C₀ * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Λ p) * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)
              * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)) := h2
    _ = ENNReal.ofReal C₀ * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (∫⁻ z in Work.Spaces.Iz,
          ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)
              * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) ^ 2))) := by rw [h3]
    _ ≤ ENNReal.ofReal C₀ * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (ENNReal.ofReal
          (Real.exp (δ * (|p.1| + |p.2|))) * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f))) :=
        mul_le_mul_of_nonneg_left h4 zero_le
    _ = ENNReal.ofReal C₀ * ((∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p
          * Real.exp (δ * (|p.1| + |p.2|))))
            * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)) := by rw [h5]
    _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal Kmass
          * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)) :=
        mul_le_mul_of_nonneg_left h6 zero_le
    _ = ENNReal.ofReal C₀ * ENNReal.ofReal (Kmass * Work.FTS.StrongEps.EpsSq α f) := by rw [h7]
    _ = ENNReal.ofReal (C₀ * (Kmass * Work.FTS.StrongEps.EpsSq α f)) :=
        (ENNReal.ofReal_mul hC₀).symm
    _ = ENNReal.ofReal (C₀ * Kmass * Work.FTS.StrongEps.EpsSq α f) := by rw [mul_assoc]

/-! ## The main theorem (development copy) -/

theorem EpsSq_mixed_Jeps_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
      ∀ f : Work.FTS.Galerkin.Fn,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) →
        Work.FTS.StrongEps.EpsMem α f →
        ∀ j i : ℕ, j + i ≤ 3 →
          Work.FTS.StrongEps.EpsSq α
              (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f))
            ≤ C * (C / ε) ^ (2 * (j + i)) * Work.FTS.StrongEps.EpsSq α f := by
  obtain ⟨c, hcpos, hWc⟩ := Work.FTS.StrongEps.HkSqAux.Wt_shift_le
  obtain ⟨δ, hδpos, hJac0⟩ := Work.FTS.StrongEps.HkSqAux.logJac_shift_le
  have hc0 : 0 ≤ c := hcpos.le
  have hδ0 : 0 ≤ δ := hδpos.le
  obtain ⟨kscale, ksm_le, kint, ksupp, kmom⟩ := KdKFacts ρ hρ
  set Cv : ℝ := max 1 (64 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
    * Real.exp (2 * (2 * c + δ))) with hCv
  have hCv1 : 1 ≤ Cv := le_max_left _ _
  have hCvpos : 0 < Cv := lt_of_lt_of_le zero_lt_one hCv1
  have hCvbig : 64 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
      * Real.exp (2 * (2 * c + δ)) ≤ Cv := le_max_right _ _
  refine ⟨Cv, hCvpos, ?_⟩
  intro α hα ε hε f hf hfmem j i hji
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  have hα0 : 0 < α := hα.1
  have hi3 : i ≤ 3 := by omega
  have hj3 : j ≤ 3 := by omega
  set A : ℝ := ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| with hAdef
  set Λ : ℝ × ℝ → ℝ := fun p =>
    |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| * Real.exp (2 * c * (|p.1| + |p.2|)) with hΛdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg fun p => abs_nonneg _
  have hΛ0 : ∀ p : ℝ × ℝ, 0 ≤ Λ p := by
    intro p
    rw [hΛdef]
    exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  -- the pointwise bound on the open quadrant
  have hpt : ∀ {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
            * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ ENNReal.ofReal (4 ^ i * A) * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
    intro z θ hz hθ
    exact MixedJepsEpsWpt ρ hρ (ε := ε) (α := α) (c := c) hε0 (f := f) hf hz hθ
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
    · rw [epsW_eq_zero_of_not_mem_quad hα0 hz hθ hc', mul_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero]
      exact zero_le
  -- the mass bound for the density
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
  -- continuity and measurability
  have hfcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2) Work.FTS.StrongEps.Quad :=
    (hf 0).continuousOn
  have hFcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2
      * Work.FTS.StrongEps.epsW α q.1 q.2) Work.FTS.StrongEps.Quad :=
    hfcont.mul (continuousOn_epsW_quad α)
  have hΛcont : Continuous Λ := by
    rw [hΛdef]
    refine (Work.FTS.StrongEps.EpsE4Thr.KdK_continuous hρ ε j i).abs.mul ?_
    refine Real.continuous_exp.comp ?_
    exact continuous_const.mul
      ((continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd))
  have hFmeas : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal
      ((f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2))
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hfmem.aestronglyMeasurable.aemeasurable
  have hAe : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2)
      * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
            (Work.FTS.StrongEps.thShift z.1.2 z.2.2)
          * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
              (Work.FTS.StrongEps.thShift z.1.2 z.2.2)) ^ 2))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
    have h2 := aemeasurable_shift_comp'
      (F := fun q : ℝ × ℝ => ENNReal.ofReal
        ((f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)) hFmeas
    have h1 : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
      (ENNReal.measurable_ofReal.comp hΛcont.measurable).comp_aemeasurable
        measurable_snd.aemeasurable
    exact h1.mul h2
  -- the chain
  have hC₀ : 0 ≤ 4 ^ i * A := mul_nonneg (by positivity) hA0
  have hKmass : 0 ≤ Real.exp (2 * (2 * c + δ)) * A :=
    mul_nonneg (Real.exp_pos _).le hA0
  have hZ := iter_le_of_pointwise (α := α) (c := c) (δ := δ) (Λ := Λ)
      (C₀ := 4 ^ i * A) (Kmass := Real.exp (2 * (2 * c + δ)) * A)
      (f := f) (g := Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f))
      hC₀ hKmass hΛ0 hΛfin hfmem hJac0 hFcont hAe hP
  have hfin : Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f))
      ≤ (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
          * Work.FTS.StrongEps.EpsSq α f := by
    refine (ENNReal.ofReal_le_ofReal_iff ?_).mp ?_
    · exact mul_nonneg (mul_nonneg hC₀ hKmass) (Work.FTS.StrongEps.EpsSq_nonneg α f)
    · exact (ofReal_EpsSq_le_iter α _).trans hZ
  -- the constants
  have hKsm0 : 0 ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3 :=
    Work.FTS.StrongEps.EpsE4Thr.Ksm_nonneg hρ 1 3
  have hA_bound : A ≤ ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3 := by
    rw [hAdef, kscale hε0 j i]
    exact mul_le_mul_of_nonneg_left (ksm_le hj3 hi3) (by positivity)
  have hAA : A ^ 2 ≤ (ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2 :=
    pow_le_pow_left₀ hA0 hA_bound 2
  have h4i : (4 : ℝ) ^ i ≤ 64 := by
    have h1 : (4 : ℝ) ^ i ≤ 4 ^ 3 := pow_le_pow_right₀ (by norm_num) hi3
    norm_num at h1
    exact h1
  have hexp2 : (ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
      = ε⁻¹ ^ (2 * (j + i)) * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm]
  have hconst : (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
      ≤ Cv * ε⁻¹ ^ (2 * (j + i)) := by
    have h2 : A ^ 2 ≤ ε⁻¹ ^ (2 * (j + i))
        * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2 := by
      rw [← hexp2]
      exact hAA
    calc (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
        = (4 ^ i * Real.exp (2 * (2 * c + δ))) * A ^ 2 := by ring
      _ ≤ (4 ^ i * Real.exp (2 * (2 * c + δ)))
            * (ε⁻¹ ^ (2 * (j + i)) * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (4 ^ i * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
              * Real.exp (2 * (2 * c + δ))) * ε⁻¹ ^ (2 * (j + i)) := by ring
      _ ≤ (64 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
              * Real.exp (2 * (2 * c + δ))) * ε⁻¹ ^ (2 * (j + i)) := by
          have hfe : (4 : ℝ) ^ i * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
                * Real.exp (2 * (2 * c + δ))
              = (4 : ℝ) ^ i * ((Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
                  * Real.exp (2 * (2 * c + δ))) := by ring
          have hfe2 : 64 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
                * Real.exp (2 * (2 * c + δ))
              = 64 * ((Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
                  * Real.exp (2 * (2 * c + δ))) := by ring
          rw [hfe, hfe2]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right h4i (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ ≤ Cv * ε⁻¹ ^ (2 * (j + i)) := mul_le_mul_of_nonneg_right hCvbig (by positivity)
  have hCeps : Cv * ε⁻¹ ^ (2 * (j + i)) ≤ Cv * (Cv / ε) ^ (2 * (j + i)) := by
    refine mul_le_mul_of_nonneg_left ?_ hCvpos.le
    rw [div_eq_mul_inv]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    simpa using mul_le_mul_of_nonneg_right hCv1 (by positivity : (0 : ℝ) ≤ ε⁻¹)
  calc Work.FTS.StrongEps.EpsSq α
          (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f))
      ≤ (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
          * Work.FTS.StrongEps.EpsSq α f := hfin
    _ ≤ (Cv * ε⁻¹ ^ (2 * (j + i))) * Work.FTS.StrongEps.EpsSq α f :=
        mul_le_mul_of_nonneg_right hconst (Work.FTS.StrongEps.EpsSq_nonneg α f)
    _ ≤ (Cv * (Cv / ε) ^ (2 * (j + i))) * Work.FTS.StrongEps.EpsSq α f :=
        mul_le_mul_of_nonneg_right hCeps (Work.FTS.StrongEps.EpsSq_nonneg α f)

end

end Work.FTS.StrongEps.EpsSqTools
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.wprod_field_winf5 =====
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
open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- `√(x⁻¹) = x^(-1/2)` for `x > 0`. -/
theorem sqrt_inv_eq_rpow_neg_half5 {x : ℝ} (hx : 0 < x) :
    Real.sqrt x⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  congr 1
  ring

/-- **The level-`5` `𝒲^{5,∞}`-priced product rule** — the literal level-`5` analogue of the
proved `Work.FTS.OpenPkg.wprod_field_winf` (the same statement with `4 → 5` and `Xn → HkNorm α 5`).

*Statement.*  There is a universal `C > 0` such that for every `α ∈ (0,1]`, every `f` smooth on
the open quadrant with `WlInfMem α 5 f` and every `g` of class `HQo α 5`,

`HkMem α 5 (f·g) ∧ HkNorm α 5 (f·g) ≤ C α^{-1/2} |f|_{𝒲^{5,∞}} |g|_{ℋ⁵}`.

*Why the pointwise version against `HkIntegrand α 5 g` is FALSE and the integrated statement is the
right one.*  If all the `θ`-derivatives of a mixed product slot `mixed j i (f·g)` sit on `f`, the
`g`-side carries the weight `Wt = w sin(2θ)^{-γ/2}` (`γ = 1 + α/10`) whereas the matching `g`-slot
of `HkIntegrand α 5 g` is a *pure* slot with weight `w sin(2θ)^{-η/2}` (`η = 99/100`), and
`sin^{-γ/2} > sin^{-η/2}`: the residual `sin(2θ)^{3α/10 - 1/100}` blows up for `α < 1/30`.  This is
exactly why the level-4 proof compares against the *majorant* `WProdWin.GmajW` (with its
`(γ-1)^{-1}` mean-term block and the angular factor `TW = (α+sin2θ)²sin(2θ)^{2α/5-γ}`) and then
*integrates* in `θ`.

*Route.*  Re-run `Submission/Work/FTS/OpenPkg/wprod_field_winf.lean` and
`Submission/Work/FTS/OpenPkg/WProdWin/` (`zslot_le_winf`, `dzIter_w_mean_le`, `mslot_le_winf`,
`Basic`) with `4 → 5`: the pure `D_z`-slots of `f·g` up to order `5` and the mixed slots with
`i + j ≤ 5`, using `WlInf α 5 f` and `HkIntegrand α 5 g`.  Note `WProdWin/dzIter_w_mean_le` is
*not* reusable verbatim (it is stated for `d ≤ 3` with `HkMem α 4 g`; at level `5` one needs
`d ≤ 4` and `HkMem α 5 g`, the same `sob_theta_mean` argument).  `WlInf_z_bound` /
`WlInf_mixed_bound` (`Spaces/WlInf_terms.lean`) give the slot bounds of `f` (note
`|DzIter b f| ≤ (Σ_k |scoef b k|) · WlInf α 5 f` from `Spaces.DzIter_eq_sum_scoef` and
`z^k ≤ (1+z)^k`), `ProdOpen.leibniz_open_Dz` / `leibniz_open_mixed` the Leibniz expansions, and
`Nonlinear.N4Fields.HkSq_le_of_integrand_le` + `LocData.HkMem_of_majorant` (continuity from
`Cert.smoothOpen_mul_bsl`) the integration and the membership.

*Consumer.*  The star coefficients `((z+1)/z)ℛ(Φ̃_*)`, `((z+1)/z)U(Φ̃_*)/sin 2θ`,
`((z+1)/z)V(Φ̃_*)` carry `𝒲^{6,∞}`-bounds (`StrongPersist.StarPkg6`), whence
`WlInf α 5 R_s ≤ WlInf α 6 R_s ≤ Cs·α`; with this rule the pieces of `N α (F_tot+…)` that carry a
star coefficient are priced at level `5` **without any derivative data of `f`**, which is what
makes the level-`5` `N`-block provable. -/
theorem wprod_field_winf5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 5 f →
      Work.FTS.VocabO.HQo α 5 g →
      Work.Spaces.HkMem α 5 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 5 f * Work.Spaces.HkNorm α 5 g := by
  obtain ⟨Cz, hCz0, hzslot⟩ := WProd5.zslot_le_winf5
  obtain ⟨CB, _hCB0, hCmean⟩ := WProd5.dzIter_w_mean_le5
  obtain ⟨Cm, hCm0, hmslot⟩ := WProd5.mslot_le_winf5 CB
  refine ⟨Real.sqrt (35701 * (6 * Cz + 36 * Cm)) + 1, by positivity, ?_⟩
  intro α hα hα1 f g hf hfm hg
  obtain ⟨hgsm, hgm⟩ := hg
  set K : ℝ := 6 * Cz + 36 * Cm with hKdef
  set Kg : ℝ := 1 + 700 * (1 + 5 * (gam α - 1)⁻¹) with hKgdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKgpos : 0 < Kg := by
    rw [hKgdef]
    have h1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
    have h2 : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr h1.le
    linarith
  have hWnn : 0 ≤ WlInf α 5 f := WlInf_nonneg α 5 f hfm
  have hfgsm : SmoothOpen (fun z θ => f z θ * g z θ) := hf.mul hgsm
  -- the pointwise majorant, with the two slot lemmas instantiated
  have hmajor : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ
        ≤ K * (WlInf α 5 f) ^ 2 * WProd5.GmajW5 α g z θ := by
    have h := WProd5.prod_majorant_winf5 hα hα1 hf hfm hgsm hgm hCz0 hCm0
      (fun i hi z θ hz hθ1 hθ2 => hzslot α f g hα hα1 hf hfm hgsm i hi z θ hz hθ1 hθ2)
      (fun I J hI hIJ z θ hz hθ1 hθ2 =>
        hmslot α f g hα hα1 hf hfm hgsm hgm
          (fun d hd z' θ' hz' hθ1' hθ2' =>
            hCmean α g d hα hα1 hgsm hgm hd z' θ' hz' hθ1' hθ2')
          I J hI hIJ z θ hz hθ1 hθ2)
    intro z hz θ hθ
    rw [hKdef]
    exact h z hz θ hθ
  -- integrability of the angular slices of the product's integrand
  have hslice : ∀ z ∈ Iz, IntegrableOn (fun θ => HkIntegrand α 5
      (fun z θ => f z θ * g z θ) z θ) Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      have hzero : (fun θ => HkIntegrand α 5 (fun z θ => f z θ * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_z α 5 _ θ
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono'
        ((WProd5.GmajW5_integrableOn_theta hα hα1 hgm hz).const_mul (K
          * (WlInf α 5 f) ^ 2)) ?_ ?_
      · exact aesm_slice_of_continuousOn_Qd _
          (hfgsm.continuousOn_HkIntegrand α 5) hzpos
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (HkIntegrand_nonneg α 5 _ z θ)]
        exact hmajor z hz θ hθ
  -- the angular integral of the majorant at every radius
  have hinner : ∀ z ∈ Iz,
      (∫ θ in Iθ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (WlInf α 5 f) ^ 2 * (Kg * WProd5.HgInt5 α g z) := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K * (WlInf α 5 f) ^ 2)
        * WProd5.GmajW5 α g z θ) Iθ :=
      (WProd5.GmajW5_integrableOn_theta hα hα1 hgm hz).const_mul _
    have h1 : (∫ θ in Iθ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
        ≤ ∫ θ in Iθ, (K * (WlInf α 5 f) ^ 2) * WProd5.GmajW5 α g z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => HkIntegrand_nonneg α 5 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Iθ, WProd5.GmajW5 α g z θ) ≤ Kg * WProd5.HgInt5 α g z := by
      simpa only [hKgdef] using WProd5.GmajW5_theta_integral_le (α := α) (g := g) hα hα1 hgm hz
    calc (∫ θ in Iθ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (WlInf α 5 f) ^ 2) * (∫ θ in Iθ, WProd5.GmajW5 α g z θ) := h1
      _ ≤ (K * (WlInf α 5 f) ^ 2) * (Kg * WProd5.HgInt5 α g z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hKpos.le (sq_nonneg _))
  -- the dominating function of the `z`-integral
  have hbdd : ∀ z ∈ Iz,
      (∫ θ in Iθ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (WlInf α 5 f) ^ 2 * Kg) * WProd5.HgInt5 α g z := by
    intro z hz
    have h1 := hinner z hz
    calc (∫ θ in Iθ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (WlInf α 5 f) ^ 2 * (Kg * WProd5.HgInt5 α g z) := h1
      _ = (K * (WlInf α 5 f) ^ 2 * Kg) * WProd5.HgInt5 α g z := by ring
  have hdom : IntegrableOn (fun z => (K * (WlInf α 5 f) ^ 2 * Kg)
      * WProd5.HgInt5 α g z) Iz :=
    hgm.2.const_mul (K * (WlInf α 5 f) ^ 2 * Kg)
  -- a.e. strong measurability of the `z`-slice integral
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Iθ,
      HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ)
      (volume.restrict Iz) := by
    have h := (aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => HkIntegrand α 5 (fun z θ => f z θ * g z θ) p.1 p.2)
      (hfgsm.continuousOn_HkIntegrand α 5)).integral_prod_right'
    have hfun : (fun z => ∫ θ, HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ
          ∂(volume.restrict Iθ))
        = (fun z => ∫ θ in Iθ,
            HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ) := rfl
    rw [← hfun]
    exact h
  have hzg : IntegrableOn (fun z => ∫ θ in Iθ,
      HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ) Iz := by
    refine Integrable.mono' hdom haesm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
      HkIntegrand_nonneg α 5 _ z θ)]
    exact hbdd z hz
  refine ⟨⟨hslice, hzg⟩, ?_⟩
  have hSq : HkSq α 5 (fun z θ => f z θ * g z θ)
      ≤ (K * (WlInf α 5 f) ^ 2 * Kg) * HkSq α 5 g := by
    have h1 : HkSq α 5 (fun z θ => f z θ * g z θ)
        ≤ ∫ z in Iz, (K * (WlInf α 5 f) ^ 2 * Kg) * WProd5.HgInt5 α g z := by
      rw [HkSq]
      exact setIntegral_mono_of_nonneg
        (fun z _ => integral_nonneg fun θ => HkIntegrand_nonneg α 5 _ z θ)
        (fun z hz => hbdd z hz) hdom
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul, WProd5.HgInt5_z_integral]
  -- the passage to the `ℋ⁵`-norm
  have hXn : HkNorm α 5 (fun z θ => f z θ * g z θ)
      ≤ Real.sqrt (K * Kg) * WlInf α 5 f * HkNorm α 5 g := by
    have h1 : HkNorm α 5 (fun z θ => f z θ * g z θ)
        ≤ Real.sqrt ((K * Kg) * (WlInf α 5 f) ^ 2 * HkSq α 5 g) := by
      rw [show HkNorm α 5 (fun z θ => f z θ * g z θ)
            = Real.sqrt (HkSq α 5 (fun z θ => f z θ * g z θ)) from rfl]
      refine Real.sqrt_le_sqrt ?_
      calc HkSq α 5 (fun z θ => f z θ * g z θ)
          ≤ (K * (WlInf α 5 f) ^ 2 * Kg) * HkSq α 5 g := hSq
        _ = (K * Kg) * (WlInf α 5 f) ^ 2 * HkSq α 5 g := by ring
    refine le_trans h1 (le_of_eq ?_)
    rw [show HkNorm α 5 g = Real.sqrt (HkSq α 5 g) from rfl,
      Real.sqrt_mul (show (0 : ℝ) ≤ (K * Kg) * (WlInf α 5 f) ^ 2 by positivity),
      Real.sqrt_mul (show (0 : ℝ) ≤ K * Kg by positivity),
      Real.sqrt_sq hWnn]
  refine le_trans hXn ?_
  -- `√(K Kg) ≤ √(35701 K) α^{-1/2}`
  have hKg_le : Kg ≤ 35701 * α⁻¹ := by
    have h1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
    have hginv : (gam α - 1)⁻¹ = 10 / α := by
      rw [gam_sub_one, inv_div]
    have hαinv : (1 : ℝ) ≤ α⁻¹ := by rw [one_le_inv₀ hα]; exact hα1
    rw [hKgdef, hginv, div_eq_mul_inv]
    ring_nf
    nlinarith [hαinv]
  have hsqrt : Real.sqrt (K * Kg) ≤ Real.sqrt (35701 * K) * α ^ (-(1 / 2 : ℝ)) := by
    have h1 : K * Kg ≤ 35701 * K * α⁻¹ := by
      calc K * Kg ≤ K * (35701 * α⁻¹) := mul_le_mul_of_nonneg_left hKg_le hKpos.le
        _ = 35701 * K * α⁻¹ := by ring
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [show (35701 : ℝ) * K * α⁻¹ = (35701 * K) * α⁻¹ from by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ 35701 * K by positivity),
      sqrt_inv_eq_rpow_neg_half5 hα]
  have hmain : Real.sqrt (K * Kg) * WlInf α 5 f * HkNorm α 5 g
      ≤ Real.sqrt (35701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 5 f
        * HkNorm α 5 g := by
    calc Real.sqrt (K * Kg) * WlInf α 5 f * HkNorm α 5 g
        = Real.sqrt (K * Kg) * (WlInf α 5 f * HkNorm α 5 g) := by ring
      _ ≤ (Real.sqrt (35701 * K) * α ^ (-(1 / 2 : ℝ)))
            * (WlInf α 5 f * HkNorm α 5 g) :=
          mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hWnn (Real.sqrt_nonneg _))
      _ = Real.sqrt (35701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 5 f
            * HkNorm α 5 g := by ring
  calc Real.sqrt (K * Kg) * WlInf α 5 f * HkNorm α 5 g
      ≤ Real.sqrt (35701 * K) * α ^ (-(1 / 2 : ℝ)) * WlInf α 5 f
          * HkNorm α 5 g := hmain
    _ = Real.sqrt (35701 * (6 * Cz + 36 * Cm)) * α ^ (-(1 / 2 : ℝ))
          * WlInf α 5 f * HkNorm α 5 g := by rw [hKdef]
    _ ≤ (Real.sqrt (35701 * (6 * Cz + 36 * Cm)) + 1) * α ^ (-(1 / 2 : ℝ))
          * WlInf α 5 f * HkNorm α 5 g := by
        have h1 : (0 : ℝ) ≤ Real.sqrt (35701 * (6 * Cz + 36 * Cm)) := Real.sqrt_nonneg _
        have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
        have h3 : (0 : ℝ) ≤ WlInf α 5 f := hWnn
        have h4 : (0 : ℝ) ≤ HkNorm α 5 g := Real.sqrt_nonneg _
        nlinarith [mul_nonneg (mul_nonneg h2 h3) h4,
          mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4]

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn Fam slice dynRHS)
open Work.FTS.StrongPersist.H6Pair6Aux

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers for the constant bookkeeping -/

/-- `√x ≤ 1 + x` for `x ≥ 0`. -/
theorem sqrt_le_one_add_c6 {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  have h1 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have h2 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith [h1, h2, sq_nonneg (Real.sqrt x - 1)]

/-- Inflate a product by a factor `≥ 1`: `a·b ≤ a·c·b`. -/
theorem mul_le_mul_insert_one_c6 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 1 ≤ c) :
    a * b ≤ a * c * b := by
  have h := mul_le_mul_of_nonneg_right hc ha
  calc a * b = (1 * a) * b := by ring
    _ ≤ (c * a) * b := mul_le_mul_of_nonneg_right h hb
    _ = a * c * b := by ring

/-- The two scalar shapes of the row right-hand sides agree:
`ScalRHS · (1 + Sq6) = RowRHS`. -/
theorem ScalRHS_mul_eq_RowRHS_c6 (α M Ce Cs : ℝ) (f : Fn) :
    ScalRHS α M Ce Cs * (1 + Sq6 α f) = RowRHS α M Ce Cs f := by
  rw [ScalRHS, RowRHS]

/-- `(1 + |Ce| + |Cs|)^4 ≥ 1`. -/
theorem one_le_Cpow_c6 (Ce Cs : ℝ) : (1 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 :=
  one_le_pow₀ (by have h1 := abs_nonneg Ce; have h2 := abs_nonneg Cs; linarith)

/-- The row shape `K (1+|Ce|+|Cs|)^4 α^{-10} (1+M)^4` is `K · ScalRHS`. -/
theorem scalRow_eq_c6 (K α M Ce Cs : ℝ) :
    K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
      = K * ScalRHS α M Ce Cs := by
  rw [ScalRHS]; ring

/-- `α^{-10}` is nonnegative for `α > 0`. -/
theorem rpow_neg_ten_nonneg_c6 {α : ℝ} (hα : 0 < α) : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) :=
  Real.rpow_nonneg hα.le _

/-! ## The finite-smoothness splitting of the pairing

`IP6_split4` of `H6Pair6Aux.assembly_core` splits the pairing over a four-fold sum, but asks for
`SmoothOpen` (i.e. `C^∞`) of the four summands.  The rows of the `C⁶` version of the assembly
supply only `ContDiffOn ℝ 6`, which is exactly what the finite-order additivity `IP6AddFin`
consumes; the only extra input is the `ℋ⁶`-membership of the *partial* sums, which is
`HkAddFin` (closure of `ℋ⁶` under addition at finite smoothness). -/

/-- **`IP6 1 … 1` splits over a four-fold sum, at finite smoothness.** -/
theorem IP6_split4_fin {α : ℝ} (hα : 0 < α) {u₁ u₂ u₃ u₄ v : Fn}
    (hs₁ : ContDiffOn ℝ 6 (Function.uncurry u₁) Work.FTS.EllipticEst.Q0)
    (hs₂ : ContDiffOn ℝ 6 (Function.uncurry u₂) Work.FTS.EllipticEst.Q0)
    (hs₃ : ContDiffOn ℝ 6 (Function.uncurry u₃) Work.FTS.EllipticEst.Q0)
    (hs₄ : ContDiffOn ℝ 6 (Function.uncurry u₄) Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ 6 (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (hm₁ : Work.Spaces.HkMem α 6 u₁) (hm₂ : Work.Spaces.HkMem α 6 u₂)
    (hm₃ : Work.Spaces.HkMem α 6 u₃) (hm₄ : Work.Spaces.HkMem α 6 u₄)
    (hmv : Work.Spaces.HkMem α 6 v) :
    Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
        (fun z θ => u₁ z θ + u₂ z θ + u₃ z θ + u₄ z θ) v
      = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u₁ v
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u₂ v
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u₃ v
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u₄ v := by
  have hs₁₂ : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => u₁ z θ + u₂ z θ))
      Work.FTS.EllipticEst.Q0 := by
    have h : Function.uncurry (fun z θ => u₁ z θ + u₂ z θ)
        = fun p : ℝ × ℝ => Function.uncurry u₁ p + Function.uncurry u₂ p := rfl
    rw [h]
    exact hs₁.add hs₂
  have hs₁₂₃ : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ))
      Work.FTS.EllipticEst.Q0 := by
    have h : Function.uncurry (fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ)
        = fun p : ℝ × ℝ => Function.uncurry (fun z θ => u₁ z θ + u₂ z θ) p
            + Function.uncurry u₃ p := rfl
    rw [h]
    exact hs₁₂.add hs₃
  have hm₁₂ : Work.Spaces.HkMem α 6 (fun z θ => u₁ z θ + u₂ z θ) :=
    (HkAddFin (k := 6) hs₁ hs₂ hm₁ hm₂).1
  have hm₁₂₃ : Work.Spaces.HkMem α 6 (fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ) :=
    (HkAddFin (k := 6) hs₁₂ hs₃ hm₁₂ hm₃).1
  rw [IP6AddFin (u := fun z θ => (u₁ z θ + u₂ z θ) + u₃ z θ) (v := u₄) (w := v)
      hα hs₁₂₃ hs₄ hv hm₁₂₃ hm₄ hmv,
    IP6AddFin (u := fun z θ => u₁ z θ + u₂ z θ) (v := u₃) (w := v)
      hα hs₁₂ hs₃ hv hm₁₂ hm₃ hmv,
    IP6AddFin (u := u₁) (v := u₂) (w := v) hα hs₁ hs₂ hv hm₁ hm₂ hmv]

/-! ## The assembly of `H6Pair` from the four rows, with the `C⁶` hypothesis

`dynRHS = -μ̄·AK + N₀ + N + N_*`, and the rows bound each of the four summands.  The only
smoothness input that the argument needs beyond `L6Ctx` is `C⁶`-smoothness of `N₀` and of `N`
(the two pieces the elliptic solver produces, available from `HkMem α 7 f` by
`EllipticEst.UopHk.contDiffOn_L12_k`); the pieces `-μ̄·AK` and `N_*` are `C^∞` on the open
quadrant, and the profile `f = slice g τ` is `SmoothOpen` by `H6Adm`. -/
theorem H6Pair_of_rows_C6 {Ce : ℝ} (hCe : 0 < Ce)
    (hN0 : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
        Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f → Work.FTS.Nonlin.Xn α f ≤ M →
        Work.Spaces.HkMem α 6
            (Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) ∧
        |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) f|
          ≤ K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Sq6 α f))
    (hN : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ) (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn), 0 ≤ τ →
        Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α M Ce Cs E Φs g Φ τ →
        Work.Spaces.HkMem α 6
            (Work.Construction.N α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice Φ τ)) ∧
        |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.Construction.N α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice Φ τ)) (Work.FTS.Galerkin.slice g τ)|
          ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4
              * (1 + Work.FTS.StrongPersist.Sq6 α (Work.FTS.Galerkin.slice g τ)))
    (hS : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ) (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn), 0 ≤ τ →
        Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α M Ce Cs E Φs g Φ τ →
        |Work.FTS.Galerkin.muDyn α Φ g τ|
            ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 ∧
        |Work.Construction.mubar
            (Work.Construction.N0 α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice g τ))
            (Work.Construction.N α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice Φ τ))|
          ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4)
    (hN0c : ∃ α₂ : ℝ, 0 < α₂ ∧ α₂ ≤ 1 ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ) (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn), 0 ≤ τ →
        Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α M Ce Cs E Φs g Φ τ →
        ContDiffOn ℝ 6 (Function.uncurry
            (Work.Construction.N0 α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice g τ))) Work.FTS.EllipticEst.Q0 ∧
        ContDiffOn ℝ 6 (Function.uncurry
            (Work.Construction.N α (Work.Construction.Ftau α g τ)
              (Work.FTS.Galerkin.slice Φ τ))) Work.FTS.EllipticEst.Q0) :
    ∃ α₂ Cp : ℝ, 0 < Cp ∧ 0 < α₂ ∧
      Work.FTS.StrongPersist.H6Pair (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1) α₂ Ce Cp := by
  obtain ⟨K0r, α0r, hK0r, hα0r, _hα0rle, hN0r⟩ := hN0
  obtain ⟨KNr, αNr, hKNr, hαNr, _hαNrle, hNr⟩ := hN
  obtain ⟨KSr, αSr, hKSr, hαSr, _hαSrle, hSr⟩ := hS
  obtain ⟨αSm, hαSm, _hαSmle, hSmr⟩ := hN0c
  obtain ⟨KAK6, hKAK60, hAK6b⟩ := Work.FTS.StrongPersist.AK6_mem_norm
  obtain ⟨CC6, hCC60, hCS6⟩ :=
    Work.FTS.StrongPersist.IP6_cs_coeffs 1 1 1 1 1 1 1 1 1 1 1 one_pos
  obtain ⟨Cns, αns, hCns0, hαns0, hnsb⟩ := Work.FTS.StrongPersist.nstar_pair_le
  -- the two output constants
  set A2 : ℝ := min (min (min (min α0r αNr) (min αSr αSm)) αns) 1 with hA2def
  set Cp : ℝ :=
    2 * ((CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr)) + 1 with hCpdef
  have hA20 : 0 < A2 := by
    rw [hA2def]
    exact lt_min (lt_min (lt_min (lt_min hα0r hαNr) (lt_min hαSr hαSm)) hαns0) one_pos
  have hA21 : A2 ≤ 1 := by rw [hA2def]; exact min_le_right _ _
  have hA2a : A2 ≤ min (min (min α0r αNr) (min αSr αSm)) αns := by
    rw [hA2def]; exact min_le_left _ _
  have hA2b : min (min (min α0r αNr) (min αSr αSm)) αns
      ≤ min (min α0r αNr) (min αSr αSm) := min_le_left _ _
  have hA2c : min (min α0r αNr) (min αSr αSm) ≤ min α0r αNr := min_le_left _ _
  have hA2d : min (min α0r αNr) (min αSr αSm) ≤ min αSr αSm := min_le_right _ _
  have hA2e : A2 ≤ αns := le_trans hA2a (min_le_right _ _)
  have hA2f : A2 ≤ α0r := le_trans hA2a (le_trans hA2b (le_trans hA2c (min_le_left _ _)))
  have hA2g : A2 ≤ αNr := le_trans hA2a (le_trans hA2b (le_trans hA2c (min_le_right _ _)))
  have hA2h : A2 ≤ αSr := le_trans hA2a (le_trans hA2b (le_trans hA2d (min_le_left _ _)))
  have hA2i : A2 ≤ αSm := le_trans hA2a (le_trans hA2b (le_trans hA2d (min_le_right _ _)))
  have hCp0 : 0 < Cp := by
    rw [hCpdef]
    have h1 : 0 < (CC6 * KAK6) * KSr := mul_pos (mul_pos hCC60 hKAK60) hKSr
    have h2 : 0 < Cns * KSr := mul_pos hCns0 hKSr
    linarith
  have hCs : (CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr) ≤ Cp := by
    rw [hCpdef]
    have h0 : 0 ≤ (CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr) := by
      have h1 : 0 < (CC6 * KAK6) * KSr := mul_pos (mul_pos hCC60 hKAK60) hKSr
      have h2 : 0 < Cns * KSr := mul_pos hCns0 hKSr
      linarith
    linarith
  refine ⟨A2, Cp, hCp0, hA20, ⟨⟨hCp0, hA20⟩, ?_⟩⟩
  rintro α hα g Φ τ M Cs E Φs hτ hctx
  have hαpos : 0 < α := hα.1
  have hαA2 : α ≤ A2 := hα.2
  have hα1' : α ≤ 1 := le_trans hαA2 hA21
  have hα0r' : α ∈ Set.Ioc 0 α0r := ⟨hαpos, le_trans hαA2 hA2f⟩
  have hαNr' : α ∈ Set.Ioc 0 αNr := ⟨hαpos, le_trans hαA2 hA2g⟩
  have hαSr' : α ∈ Set.Ioc 0 αSr := ⟨hαpos, le_trans hαA2 hA2h⟩
  have hαSm' : α ∈ Set.Ioc 0 αSm := ⟨hαpos, le_trans hαA2 hA2i⟩
  have hαns' : α ∈ Set.Ioc 0 αns := ⟨hαpos, le_trans hαA2 hA2e⟩
  -- the abbreviations of the statement
  set f : Fn := slice g τ with hf
  set Ψ : Fn := slice Φ τ with hΨ
  set F : Fn := Work.Construction.Ftau α g τ with hF
  set μbar : ℝ :=
    Work.Construction.mubar (Work.Construction.N0 α F f) (Work.Construction.N α F Ψ) with hμbar
  set μ : ℝ := Work.FTS.Galerkin.muDyn α Φ g τ with hμdef
  set lam : ℝ := Work.FTS.Galerkin.lamDyn α Φ g τ with hlamdef
  set p1 : Fn := Work.FTS.StrongPersist.H6Pair6Aux.P1 α g Φ τ with hp1
  set p2 : Fn := Work.FTS.StrongPersist.H6Pair6Aux.P2 α g τ with hp2
  set p3 : Fn := Work.FTS.StrongPersist.H6Pair6Aux.P3 α g Φ τ with hp3
  set p4 : Fn := Work.FTS.StrongPersist.H6Pair6Aux.P4 α Φ g τ with hp4
  -- the interface data
  have hreg : Work.FTS.StrongPersist.H6Adm α f := hctx.hreg
  have h7 : Work.Spaces.HkMem α 7 f := hctx.h7
  have hbdM : Work.FTS.Nonlin.Xn α f ≤ M := hctx.hbdd
  have h6 : Work.Spaces.HkMem α 6 f := hreg.reg.2
  have hsmf : Work.FTS.EllipticEst.SmoothOpen f := hreg.reg.1
  have hQof : Work.FTS.VocabO.HQo α 6 f := ⟨hsmf, h6⟩
  have hSq0 : 0 ≤ Sq6 α f := Work.FTS.StrongPersist.Sq6_nonneg α f
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdM
  -- smoothness and `ℋ⁶`-membership of the four summands
  have hsm23 := hSmr α hαSm' g Φ τ M Cs E Φs hτ hctx
  have hs1 : Work.FTS.EllipticEst.SmoothOpen p1 :=
    smoothOpen_const_mul_loc (-μbar) (Work.FTS.StrongPersist.AK_smoothO α)
  have hm1 : Work.Spaces.HkMem α 6 p1 :=
    Work.FTS.LocData.HkMem_const_mul α 6 (-μbar) (hAK6b α hαpos hα1').1
  have hs2 : ContDiffOn ℝ 6 (Function.uncurry p2) Work.FTS.EllipticEst.Q0 := hsm23.1
  have hm2 : Work.Spaces.HkMem α 6 p2 := (hN0r α hα0r' f M hreg h7 hbdM).1
  have hs3 : ContDiffOn ℝ 6 (Function.uncurry p3) Work.FTS.EllipticEst.Q0 := hsm23.2
  have hm3 : Work.Spaces.HkMem α 6 p3 := (hNr α hαNr' g Φ τ M Cs E Φs hτ hctx).1
  have hs4 : Work.FTS.EllipticEst.SmoothOpen p4 :=
    (P4_smooth_mem hsmf h6 h7).1
  have hm4 : Work.Spaces.HkMem α 6 p4 := (P4_smooth_mem hsmf h6 h7).2
  -- the decomposition `dynRHS = p1 + p2 + p3 + p4`
  have hdec : dynRHS α Φ g τ = fun z θ => p1 z θ + p2 z θ + p3 z θ + p4 z θ := by
    rw [dynRHS_eq_sum]
  have hsplit_eq : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (dynRHS α Φ g τ) f
      = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f := by
    rw [hdec]
    exact IP6_split4_fin (α := α) (u₁ := p1) (u₂ := p2) (u₃ := p3) (u₄ := p4) (v := f)
      hαpos (hs1.forall 6) hs2 hs3 (hs4.forall 6) (hsmf.forall 6) hm1 hm2 hm3 hm4 h6
  have htri : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (dynRHS α Φ g τ) f|
      ≤ |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f| := by
    rw [hsplit_eq]
    have h1 := abs_add_le
      (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f)
      (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f)
    have h2 := abs_add_le
      (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f)
      (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f)
    have h3 := abs_add_le (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f)
      (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f)
    linarith
  -- the scalar bounds of the rows
  have hμbarbd : |μbar| ≤ KSr * ScalRHS α M Ce Cs := by
    have h := (hSr α hαSr' g Φ τ M Cs E Φs hτ hctx).2
    calc |μbar| ≤ KSr * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := h
      _ = KSr * ScalRHS α M Ce Cs := scalRow_eq_c6 KSr α M Ce Cs
  have hμbd : |μ| ≤ KSr * ScalRHS α M Ce Cs := by
    have h := (hSr α hαSr' g Φ τ M Cs E Φs hτ hctx).1
    calc |μ| ≤ KSr * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 := h
      _ = KSr * ScalRHS α M Ce Cs := scalRow_eq_c6 KSr α M Ce Cs
  have hlamid : |μ + lam + μ * lam| = |μ| :=
    Work.FTS.StrongPersist.H6Pair6Aux.abs_add_lamfun μ
  have hbc : |μ| + |μ + lam + μ * lam| = 2 * |μ| := by
    rw [hlamid]; ring
  -- the four pairing bounds, all with the `RowRHS`-shape
  have hb1 : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
      ≤ (CC6 * KAK6 * KSr) * RowRHS α M Ce Cs f := by
    have hcs := hCS6 α ⟨hαpos, hα1'⟩ p1 f ⟨hs1, hm1⟩ hQof
    have hXn1 : Xn6 α p1 ≤ |μbar| * KAK6 := by
      have hk : Work.Spaces.HkNorm α 6 (fun z θ => -μbar * Work.Construction.AK α z θ)
          = |μbar| * Work.Spaces.HkNorm α 6 (Work.Construction.AK α) := by
        have h0 := Work.FTS.EllipticEst.HkNorm_const_mul α 6 (-μbar)
          (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall
            (fun z θ => Work.Construction.AK α z θ)).mp
              (Work.FTS.StrongPersist.AK_smoothO α) n)
        rw [abs_neg] at h0
        exact h0
      calc Xn6 α p1
          = Work.Spaces.HkNorm α 6 (fun z θ => -μbar * Work.Construction.AK α z θ) := rfl
        _ = |μbar| * Work.Spaces.HkNorm α 6 (Work.Construction.AK α) := hk
        _ ≤ |μbar| * KAK6 :=
            mul_le_mul_of_nonneg_left (hAK6b α hαpos hα1').2 (abs_nonneg μbar)
    have hXn6f : Xn6 α f ≤ 1 + Sq6 α f := sqrt_le_one_add_c6 hSq0
    have hstep1 : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
        ≤ CC6 * (|μbar| * KAK6) * (1 + Sq6 α f) := by
      calc |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
          ≤ CC6 * Xn6 α p1 * Xn6 α f := hcs
        _ ≤ CC6 * (|μbar| * KAK6) * (1 + Sq6 α f) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hXn1 hCC60.le) hXn6f
              (Work.Spaces.HkNorm_nonneg α 6 f) ?_
            exact mul_nonneg hCC60.le (mul_nonneg (abs_nonneg μbar) hKAK60.le)
    have hmu : CC6 * (|μbar| * KAK6) ≤ (CC6 * KAK6 * KSr) * ScalRHS α M Ce Cs := by
      calc CC6 * (|μbar| * KAK6) ≤ CC6 * ((KSr * ScalRHS α M Ce Cs) * KAK6) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hμbarbd hKAK60.le) hCC60.le
        _ = (CC6 * KAK6 * KSr) * ScalRHS α M Ce Cs := by ring
    have hstep2 : CC6 * (|μbar| * KAK6) * (1 + Sq6 α f)
        ≤ (CC6 * KAK6 * KSr) * RowRHS α M Ce Cs f := by
      rw [← ScalRHS_mul_eq_RowRHS_c6]
      calc CC6 * (|μbar| * KAK6) * (1 + Sq6 α f)
          ≤ ((CC6 * KAK6 * KSr) * ScalRHS α M Ce Cs) * (1 + Sq6 α f) :=
            mul_le_mul_of_nonneg_right hmu (by linarith [hSq0])
        _ = (CC6 * KAK6 * KSr) * (ScalRHS α M Ce Cs * (1 + Sq6 α f)) := by ring
    exact le_trans hstep1 hstep2
  have hb2 : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
      ≤ K0r * RowRHS α M Ce Cs f := by
    have h' : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
        ≤ K0r * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) :=
      (hN0r α hα0r' f M hreg h7 hbdM).2
    rw [← ScalRHS_mul_eq_RowRHS_c6]
    have hb : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) :=
      mul_nonneg (mul_nonneg (rpow_neg_ten_nonneg_c6 hαpos) (by positivity)) (by linarith [hSq0])
    have h1 : K0r * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)
        = K0r * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)) := by ring
    have h1' : K0r * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f))
        ≤ K0r * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)) :=
      mul_le_mul_insert_one_c6 hK0r.le hb (one_le_Cpow_c6 Ce Cs)
    have h2 : K0r * (1 + |Ce| + |Cs|) ^ 4 * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f))
        = K0r * (ScalRHS α M Ce Cs * (1 + Sq6 α f)) := by
      rw [ScalRHS]; ring
    linarith [h', h1.le, h1.ge, h1', h2.le, h2.ge]
  have hb3 : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
      ≤ KNr * RowRHS α M Ce Cs f := by
    have h' : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
        ≤ KNr * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) :=
      (hNr α hαNr' g Φ τ M Cs E Φs hτ hctx).2
    rw [← ScalRHS_mul_eq_RowRHS_c6]
    have h1 : KNr * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f)
        = KNr * (ScalRHS α M Ce Cs * (1 + Sq6 α f)) := by
      rw [ScalRHS]; ring
    rw [h1] at h'
    exact h'
  have hb4 : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f|
      ≤ (2 * (Cns * KSr)) * RowRHS α M Ce Cs f := by
    have h' : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f|
        ≤ Cns * (|μ| + |μ + lam + μ * lam|) * Sq6 α f :=
      hnsb α hαns' μ lam f hQof h7
    rw [hbc] at h'
    rw [← ScalRHS_mul_eq_RowRHS_c6]
    have hμ2 : 2 * |μ| ≤ 2 * (KSr * ScalRHS α M Ce Cs) :=
      mul_le_mul_of_nonneg_left hμbd (by norm_num)
    have hstep : Cns * (2 * |μ|) * Sq6 α f
        ≤ (2 * (Cns * KSr)) * (ScalRHS α M Ce Cs * (1 + Sq6 α f)) := by
      calc Cns * (2 * |μ|) * Sq6 α f
          ≤ Cns * (2 * (KSr * ScalRHS α M Ce Cs)) * Sq6 α f :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμ2 hCns0.le) hSq0
        _ = (2 * (Cns * KSr)) * (ScalRHS α M Ce Cs * Sq6 α f) := by ring
        _ ≤ (2 * (Cns * KSr)) * (ScalRHS α M Ce Cs * (1 + Sq6 α f)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (by linarith [hSq0]) (ScalRHS_nonneg hαpos))
              (by have h := mul_pos hCns0 hKSr; linarith)
    exact le_trans h' hstep
  -- the four bounds combine
  have hsum : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f|
      ≤ ((CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr)) * RowRHS α M Ce Cs f := by
    have h12 := add_le_add hb1 hb2
    have h123 := add_le_add h12 hb3
    have h1234 := add_le_add h123 hb4
    calc |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
          + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
          + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
          + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f|
        ≤ (CC6 * KAK6 * KSr) * RowRHS α M Ce Cs f + K0r * RowRHS α M Ce Cs f
          + KNr * RowRHS α M Ce Cs f + (2 * (Cns * KSr)) * RowRHS α M Ce Cs f := h1234
      _ = ((CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr)) * RowRHS α M Ce Cs f := by ring
  -- assemble
  calc |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (dynRHS α Φ g τ) f|
      ≤ |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p1 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p2 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p3 f|
        + |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α p4 f| := htri
    _ ≤ ((CC6 * KAK6) * KSr + K0r + KNr + 2 * (Cns * KSr)) * RowRHS α M Ce Cs f := hsum
    _ ≤ Cp * RowRHS α M Ce Cs f :=
        mul_le_mul_of_nonneg_right hCs (RowRHS_nonneg (f := f) hαpos)
    _ = Cp * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Sq6 α f) := by
        rw [← ScalRHS_mul_eq_RowRHS_c6, ScalRHS]; ring

end Work.FTS.StrongPersist.H6Rows
end
end
