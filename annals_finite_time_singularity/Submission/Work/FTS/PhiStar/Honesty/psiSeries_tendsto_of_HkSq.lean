import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Honesty.hcoef_psiSeries
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all
import Submission.Work.FTS.ClassCHon.Hcoef.cmode_L2_bound
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.EllipticEst.ModalSolution.radGreen_abs_le
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.PhiStar.Honesty.DiffGreen.radGreen_diff_abs_le
import Submission.Work.FTS.PhiStar.Honesty.DiffGreen.cmode_sub
import Submission.Work.FTS.PhiStar.Honesty.DiffGreen.sum_sqrt_eNorm_le

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
