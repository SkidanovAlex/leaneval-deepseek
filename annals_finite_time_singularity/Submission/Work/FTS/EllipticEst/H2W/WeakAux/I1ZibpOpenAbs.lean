import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.I1_defs
import Submission.Work.FTS.EllipticEst.AngClean.I1_cut_alt
import Submission.Work.FTS.EllipticEst.AngClean.I1_ibp
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.remov.I1_ibp_identity_fts
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.niceSliceIBPOpen
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.AngSecond.I1_honesty
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.WeakAux

open MeasureTheory Set Filter
open scoped Real Topology ContDiff

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

abbrev Qd0 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

abbrev muP : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-! ## The `k = 0` integrand is a single weighted square -/

theorem HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

theorem HkIntegrand_zero_eq' (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ := by
  rw [HkIntegrand_zero_eq]
  exact Work.FTS.EllipticEst.AngSecond.sq_mul_W g hθ

theorem w2_zero : Work.FTS.EllipticEst.AngSecond.w2 0 = 0 := by
  simp [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]

theorem sig_rpow_eq (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ := by
  have h := Work.FTS.EllipticEst.AngSecond.sq_mul_W (fun _ _ : ℝ => (1 : ℝ))
    (z := z) (θ := θ) hθ
  simpa using h

/-! ## The pointwise AM–GM bound -/

theorem abs_mul_le_Hk_sum (α : ℝ) (f h : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |f z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ|
      ≤ (Work.Spaces.HkIntegrand α 0 f z θ + Work.Spaces.HkIntegrand α 0 h z θ) * (1 / 2) := by
  have hWs : (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ :=
    sig_rpow_eq z θ hθ
  have hL : |f z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ|
      = |f z θ| * |h z θ| * (Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Work.FTS.EllipticEst.AngSecond.w2_nonneg z),
      abs_of_nonneg (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)]
    ring
  have hR : (f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        + (h z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = (f z θ ^ 2 + h z θ ^ 2)
        * (Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [mul_pow, mul_pow, hWs]; ring
  rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq, hL, hR]
  have hAM : 2 * (|f z θ| * |h z θ|) ≤ f z θ ^ 2 + h z θ ^ 2 := by
    nlinarith [sq_nonneg (|f z θ| - |h z θ|), sq_abs (f z θ), sq_abs (h z θ)]
  have hW : 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z
      * Work.FTS.EllipticEst.AngSecond.sig θ :=
    mul_nonneg (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
      (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)
  have := mul_le_mul_of_nonneg_right hAM hW
  linarith

/-! ## Joint integrability of a mixed product on the quadrant -/

theorem prod_integrable_mul {α : ℝ} {f h : ℝ → ℝ → ℝ}
    (hfc : ContinuousOn (Function.uncurry f) Qd0)
    (hhc : ContinuousOn (Function.uncurry h) Qd0)
    (hf : Work.Spaces.HkMem α 0 f) (hh : Work.Spaces.HkMem α 0 h) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => f p.1 p.2 * h p.1 p.2
        * Work.FTS.EllipticEst.AngSecond.w2 p.1 * Work.FTS.EllipticEst.AngSecond.sig p.2)
      muP := by
  let F : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * h p.1 p.2
    * Work.FTS.EllipticEst.AngSecond.w2 p.1 * Work.FTS.EllipticEst.AngSecond.sig p.2
  show MeasureTheory.Integrable F muP
  have hcont : ContinuousOn F Qd0 := by
    show ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * h p.1 p.2
      * Work.FTS.EllipticEst.AngSecond.w2 p.1
      * Work.FTS.EllipticEst.AngSecond.sig p.2) Qd0
    exact ((hfc.mul hhc).mul Work.FTS.EllipticEst.AngSecond.continuousOn_w2_Qd).mul
      Work.FTS.EllipticEst.AngSecond.continuousOn_sig_Qd
  have haesm : AEStronglyMeasurable F muP := Work.Spaces.aesm_of_continuousOn_Qd F hcont
  rw [MeasureTheory.integrable_prod_iff haesm]
  constructor
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero
        (fun θ _ => ?_) measurableSet_Icc
      show (0 : ℝ) = F (0, θ)
      simp [F, w2_zero]
    · have hκm : Measurable (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) :=
        Work.FTS.EllipticEst.AngSecond.measurable_sig.const_mul _
      have hκnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
        fun θ hθ => mul_nonneg (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
          (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)
      have hf2 : MeasureTheory.IntegrableOn (fun θ => f z θ * f z θ
          * (Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ :=
        (hf.1 z hz).congr (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
          show Work.Spaces.HkIntegrand α 0 f z θ = f z θ * f z θ
            * (Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
          rw [HkIntegrand_zero_eq' α f hθ]; ring))
      have hh2 : MeasureTheory.IntegrableOn (fun θ => h z θ * h z θ
          * (Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ :=
        (hh.1 z hz).congr (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
          show Work.Spaces.HkIntegrand α 0 h z θ = h z θ * h z θ
            * (Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
          rw [HkIntegrand_zero_eq' α h hθ]; ring))
      refine (Work.AngSecond.integrableOn_mul_of_sq_aux (s := Work.Spaces.Iθ)
        (F := fun θ => f z θ) (G := fun θ => h z θ)
        (κ := fun θ => Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
        measurableSet_Icc ?_ ?_ hκm hκnn hf2 hh2).congr (Eventually.of_forall (fun θ => ?_))
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hfc hzpos
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry h) hhc hzpos
      · show f z θ * h z θ * (Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) = F (z, θ)
        simp only [F]; ring
  · have haesm2 : AEStronglyMeasurable
        (fun z : ℝ => ∫ θ, ‖F (z, θ)‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      haesm.norm.integral_prod_right'
    refine MeasureTheory.Integrable.mono' (((hf.2.add hh.2).const_mul (1 / 2))) haesm2 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hFnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, ‖F (z, θ)‖ :=
      integral_nonneg (fun θ => norm_nonneg (F (z, θ)))
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
    simp only [Real.norm_eq_abs]
    change (∫ θ in Work.Spaces.Iθ, |F (z, θ)|) ≤ (1 / 2) *
      ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h z θ))
    have h2 : (∫ θ in Work.Spaces.Iθ, |F (z, θ)|)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 0 f z θ
            + Work.Spaces.HkIntegrand α 0 h z θ) * (1 / 2) := by
      refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun θ => abs_nonneg _))
        (((hf.1 z hz).add (hh.1 z hz)).mul_const (1 / 2)) ?_
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      show |F (z, θ)| ≤ (Work.Spaces.HkIntegrand α 0 f z θ
        + Work.Spaces.HkIntegrand α 0 h z θ) * (1 / 2)
      simp only [F]
      exact abs_mul_le_Hk_sum α f h hθ
    have h3 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 0 f z θ
            + Work.Spaces.HkIntegrand α 0 h z θ) * (1 / 2))
        = ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h z θ)) * (1 / 2) := by
      rw [MeasureTheory.integral_mul_const,
        MeasureTheory.integral_add (hf.1 z hz) (hh.1 z hz)]
    calc (∫ θ in Work.Spaces.Iθ, |F (z, θ)|)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α 0 f z θ
            + Work.Spaces.HkIntegrand α 0 h z θ) * (1 / 2) := h2
      _ = ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h z θ)) * (1 / 2) := h3
      _ = _ := by ring

/-! ## Mixed honesty from the diagonal honesties, in the open class -/

theorem IPMem_of_diag_open {g h : ℝ → ℝ → ℝ}
    (hgc : ContinuousOn (Function.uncurry g) Qd0)
    (hhc : ContinuousOn (Function.uncurry h) Qd0)
    (hg : Work.FTS.EllipticEst.AngSecond.IPMem g g)
    (hh : Work.FTS.EllipticEst.AngSecond.IPMem h h) :
    Work.FTS.EllipticEst.AngSecond.IPMem g h := by
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero
        (fun θ _ => ?_) measurableSet_Icc
      show (0 : ℝ) = g 0 θ * h 0 θ * Work.FTS.EllipticEst.AngSecond.w2 0
        * Work.FTS.EllipticEst.AngSecond.sig θ
      simp [w2_zero]
    · have hκm : Measurable (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) :=
        Work.FTS.EllipticEst.AngSecond.measurable_sig.const_mul _
      have hκnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
        fun θ hθ => mul_nonneg (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
          (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)
      have hg2 : MeasureTheory.IntegrableOn (fun θ => g z θ * g z θ
          * (Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ :=
        (hg.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
      have hh2 : MeasureTheory.IntegrableOn (fun θ => h z θ * h z θ
          * (Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ)) Work.Spaces.Iθ :=
        (hh.1 z hz).congr (Eventually.of_forall (fun θ => by ring))
      refine (Work.AngSecond.integrableOn_mul_of_sq_aux (s := Work.Spaces.Iθ)
        (F := fun θ => g z θ) (G := fun θ => h z θ)
        (κ := fun θ => Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
        measurableSet_Icc ?_ ?_ hκm hκnn hg2 hh2).congr (Eventually.of_forall (fun θ => ?_))
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hgc hzpos
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry h) hhc hzpos
      · show g z θ * h z θ * (Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
          = (fun θ' => g z θ' * h z θ' * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ') θ
        ring
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2
        * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2) Qd0 :=
      (((hgc.mul hhc)).mul Work.FTS.EllipticEst.AngSecond.continuousOn_w2_Qd).mul
        Work.FTS.EllipticEst.AngSecond.continuousOn_sig_Qd
    have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
          * Work.FTS.EllipticEst.AngSecond.sig p.2) muP :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    refine MeasureTheory.Integrable.mono' (((hg.2.add hh.2).const_mul (1 / 2)))
      hjoint.integral_prod_right' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    change ‖∫ θ in Work.Spaces.Iθ, g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ‖ ≤ (1 / 2) *
      ((∫ θ in Work.Spaces.Iθ, g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
        + (∫ θ in Work.Spaces.Iθ, h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ))
    have h2 : |∫ θ in Work.Spaces.Iθ, g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ|
        ≤ ∫ θ in Work.Spaces.Iθ, (g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ
            + h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) * (1 / 2) := by
      refine le_trans abs_integral_le_integral_abs ?_
      refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun θ => abs_nonneg _))
        (((hg.1 z hz).add (hh.1 z hz)).mul_const (1 / 2)) ?_
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      show |g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ|
          ≤ (g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ
              + h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) * (1 / 2)
      have hw2 : 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z :=
        Work.FTS.EllipticEst.AngSecond.w2_nonneg z
      have hs : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
        Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
      have hAM : 2 * (|g z θ| * |h z θ|) ≤ g z θ * g z θ + h z θ * h z θ := by
        nlinarith [sq_nonneg (|g z θ| - |h z θ|), sq_abs (g z θ), sq_abs (h z θ)]
      have hstep : |g z θ| * |h z θ| ≤ (g z θ * g z θ + h z θ * h z θ) / 2 := by linarith
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hw2, abs_of_nonneg hs]
      have hkey := mul_le_mul_of_nonneg_right hstep (mul_nonneg hw2 hs)
      calc |g z θ| * |h z θ| * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ
          = |g z θ| * |h z θ| * (Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
        _ ≤ ((g z θ * g z θ + h z θ * h z θ) / 2)
              * (Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) := hkey
        _ = (g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ
              + h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) * (1 / 2) := by ring
    have h3 : (∫ θ in Work.Spaces.Iθ, (g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ
            + h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) * (1 / 2))
        = ((∫ θ in Work.Spaces.Iθ, g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ)
            + (∫ θ in Work.Spaces.Iθ, h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ)) * (1 / 2) := by
      rw [MeasureTheory.integral_mul_const,
        MeasureTheory.integral_add (hg.1 z hz) (hh.1 z hz)]
    rw [Real.norm_eq_abs]
    calc |∫ θ in Work.Spaces.Iθ, g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ|
        ≤ ∫ θ in Work.Spaces.Iθ, (g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ
            + h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) * (1 / 2) := h2
      _ = ((∫ θ in Work.Spaces.Iθ, g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ)
            + (∫ θ in Work.Spaces.Iθ, h z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ)) * (1 / 2) := h3
      _ = _ := by ring

/-! ## Smoothness helpers -/

theorem smoothOpen_fst : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) :=
  contDiff_fst.contDiffOn

theorem continuousOn_uncurry_of_smoothOpen {F : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen F) : ContinuousOn (Function.uncurry F) Qd0 :=
  h.continuousOn

theorem smoothOpen_sq_mul_pzIter {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
  (smoothOpen_fst.pow 2).mul (h.pzIter 2)

theorem smoothOpen_fst_mul_pz {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
  smoothOpen_fst.mul h.pz

theorem smoothOpen_pthIter_two {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := by
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h.pth.pth

theorem smoothOpen_fst_mul_pz_pthIter_two {Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) :=
  smoothOpen_fst.mul (smoothOpen_pthIter_two h).pz

/-! ## The angular weight at the two angular endpoints -/

theorem sig_zero : Work.FTS.EllipticEst.AngSecond.sig 0 = 0 := by
  rw [Work.FTS.EllipticEst.AngSecond.sig]
  simp only [mul_zero, Real.sin_zero]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

theorem sig_pi_half : Work.FTS.EllipticEst.AngSecond.sig (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.AngSecond.sig]
  have h2 : 2 * (Real.pi / 2) = Real.pi := by ring
  rw [h2, Real.sin_pi]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
/-! ## A triangle-inequality helper -/

theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  simpa using abs_add_le a (-b)

theorem continuousOn_fst_Qd0 : ContinuousOn (fun p : ℝ × ℝ => p.1) Qd0 :=
  continuous_fst.continuousOn

theorem continuousOn_sig_Qd0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.2) Qd0 :=
  Work.FTS.EllipticEst.AngSecond.continuousOn_sig_Qd

theorem continuousOn_w2_Qd0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p.1) Qd0 :=
  Work.FTS.EllipticEst.AngSecond.continuousOn_w2_Qd

/-! ## The pointwise bound on `σ · nice` -/

theorem abs_sig_nice_le (α K : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hKnn : 0 ≤ K)
    (hK : ∀ z : ℝ, |z * deriv (Work.FTS.EllipticEst.cut n) z| ≤ K)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.FTS.EllipticEst.AngSecond.sig θ * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ|
      ≤ 12 * (1 + K) * (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ) := by
  have hGs : Work.Spaces.Dz Ψ = Work.FTS.EllipticEst.AngSecond.G Ψ := rfl
  have hPs : Work.Spaces.pthIter 2 Ψ = Work.FTS.EllipticEst.AngSecond.Phi Ψ := rfl
  have hHs : (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
      = Work.FTS.EllipticEst.AngSecond.H Ψ := rfl
  rw [hHs, hPs, hGs]
  have hsb : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
    Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
  have hwb : 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z :=
    Work.FTS.EllipticEst.AngSecond.w2_nonneg z
  have hc0 : 0 ≤ Work.FTS.EllipticEst.cut n z := Work.FTS.EllipticEst.cut_nonneg n z
  have hc1 : |Work.FTS.EllipticEst.cut n z| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith, Work.FTS.EllipticEst.cut_le_one n z⟩
  have h1z : 0 < 1 + z := by linarith
  have hABnn : 0 ≤ |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
      * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
      + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
        * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ| :=
    add_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hBr : |2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
        + Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
        - 4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
          * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z)|
      ≤ 6 * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|) := by
    have h1 : |2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
          + Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.H Ψ z θ|
        ≤ 2 * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)
          + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ| := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have h3 : |4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z)|
        ≤ 4 * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|) := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos h1z,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      rw [div_le_iff₀ h1z]
      have h0 : (0 : ℝ) ≤ 4 * |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
          * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ| * z :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _)) hz
      nlinarith [h0]
    refine ((abs_sub_le_add
      (2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
        + Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.H Ψ z θ)
      (4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z))).trans
        (add_le_add h1 h3)).trans ?_
    nlinarith [mul_nonneg (abs_nonneg (Work.FTS.EllipticEst.AngSecond.G Ψ z θ))
      (abs_nonneg (Work.FTS.EllipticEst.AngSecond.H Ψ z θ))]
  have hnice : |Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ|
      ≤ 12 * (1 + K) * (Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)) := by
    have hU : |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.w2 z
          * (2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
              * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
            + Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
            - 4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
              * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z))|
        ≤ 6 * (Work.FTS.EllipticEst.AngSecond.w2 z
            * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
              + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hwb, abs_of_nonneg hc0]
      have hb := mul_le_mul hc1 hBr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have hb2 := mul_le_mul_of_nonneg_right hb hwb
      calc Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.w2 z
            * |2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
                * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
              + Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
              - 4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
                * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z)|
          = (|Work.FTS.EllipticEst.cut n z|
              * |2 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
                  * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
                + Work.FTS.EllipticEst.AngSecond.G Ψ z θ
                  * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
                - 4 * Work.FTS.EllipticEst.AngSecond.G Ψ z θ
                  * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ / (1 + z)|)
              * Work.FTS.EllipticEst.AngSecond.w2 z := by
            rw [abs_of_nonneg hc0]; ring
        _ ≤ (1 * (6 * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)))
              * Work.FTS.EllipticEst.AngSecond.w2 z := hb2
        _ = 6 * (Work.FTS.EllipticEst.AngSecond.w2 z
            * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
              + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)) := by ring
    have hV : |Work.FTS.EllipticEst.AngSecond.w2 z
          * (Work.FTS.EllipticEst.AngSecond.G Ψ z θ * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ)
          * (z * deriv (Work.FTS.EllipticEst.cut n) z)|
        ≤ K * (Work.FTS.EllipticEst.AngSecond.w2 z
            * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hwb]
      have hb := mul_le_mul_of_nonneg_left (hK z)
        (mul_nonneg hwb (mul_nonneg (abs_nonneg (Work.FTS.EllipticEst.AngSecond.G Ψ z θ))
          (abs_nonneg (Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ))))
      calc Work.FTS.EllipticEst.AngSecond.w2 z
            * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)
            * |z * deriv (Work.FTS.EllipticEst.cut n) z|
          ≤ (Work.FTS.EllipticEst.AngSecond.w2 z
              * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)) * K := hb
        _ = K * (Work.FTS.EllipticEst.AngSecond.w2 z
            * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)) := by ring
    rw [Work.FTS.EllipticEst.AngSecond.nice]
    refine ((abs_add_le _ _).trans (add_le_add hU hV)).trans ?_
    have hYX : Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|)
        ≤ Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|) :=
      mul_le_mul_of_nonneg_left (by
        have h1 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.G Ψ z θ)
        have h2 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ)
        have h3 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.H Ψ z θ)
        nlinarith) hwb
    have hYnn : 0 ≤ Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|) :=
      mul_nonneg hwb (by
        have h1 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.G Ψ z θ)
        have h2 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ)
        have h3 := abs_nonneg (Work.FTS.EllipticEst.AngSecond.H Ψ z θ)
        nlinarith)
    have hKY : K * (Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|))
        ≤ K * (Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)) :=
      mul_le_mul_of_nonneg_left hYX hKnn
    have hlast : (6 + K) * (Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|))
        ≤ 12 * (1 + K) * (Work.FTS.EllipticEst.AngSecond.w2 z
          * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
            + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
              * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|)) :=
      mul_le_mul_of_nonneg_right (by linarith) hYnn
    linarith [hKY, hlast]
  have hsum : |Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|
          + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|
      ≤ Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.G Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.Phi Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.H Ψ) z θ := by
    have h1 := abs_mul_le_Hk_sum α (Work.FTS.EllipticEst.AngSecond.G Ψ)
      (Work.FTS.EllipticEst.AngSecond.Phi Ψ) (z := z) hθ
    have h2 := abs_mul_le_Hk_sum α (Work.FTS.EllipticEst.AngSecond.G Ψ)
      (Work.FTS.EllipticEst.AngSecond.H Ψ) (z := z) hθ
    have h3 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.FTS.EllipticEst.AngSecond.G Ψ) z θ
    have h4 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.FTS.EllipticEst.AngSecond.Phi Ψ) z θ
    have h5 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.FTS.EllipticEst.AngSecond.H Ψ) z θ
    linarith
  have he1 : |Work.FTS.EllipticEst.AngSecond.G Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|
      = |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
        * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hwb, abs_of_nonneg hsb]
  have he2 : |Work.FTS.EllipticEst.AngSecond.G Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|
      = |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
        * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hwb, abs_of_nonneg hsb]
  have hcoef : (0 : ℝ) ≤ 12 * (1 + K) := by linarith
  calc |Work.FTS.EllipticEst.AngSecond.sig θ * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ|
      = Work.FTS.EllipticEst.AngSecond.sig θ
          * |Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ| := by
        rw [abs_mul, abs_of_nonneg hsb]
    _ ≤ Work.FTS.EllipticEst.AngSecond.sig θ
          * (12 * (1 + K) * (Work.FTS.EllipticEst.AngSecond.w2 z
              * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                  * |Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ|
                + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ|
                  * |Work.FTS.EllipticEst.AngSecond.H Ψ z θ|))) :=
        mul_le_mul_of_nonneg_left hnice hsb
    _ = 12 * (1 + K) * (|Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|
          + |Work.FTS.EllipticEst.AngSecond.G Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.H Ψ z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ|) := by
        rw [he1, he2]; ring
    _ ≤ 12 * (1 + K) * (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.G Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.Phi Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AngSecond.H Ψ) z θ) :=
        mul_le_mul_of_nonneg_left hsum hcoef

/-! ## Joint integrability of `cut n · Akern` and of `σ · nice` -/

theorem prod_integrable_cut_akern (α : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1
        * Work.FTS.EllipticEst.AngSecond.Akern Ψ p.1 p.2) muP := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hbase := prod_integrable_mul (α := α)
    (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
    (h := Work.Spaces.pthIter 2 Ψ)
    (continuousOn_uncurry_of_smoothOpen (smoothOpen_sq_mul_pzIter hΨ))
    (continuousOn_uncurry_of_smoothOpen (smoothOpen_pthIter_two hΨ)) hQ hΦ
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1
      * Work.FTS.EllipticEst.AngSecond.Akern Ψ p.1 p.2) Qd0 := by
    have hQc : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2) Qd0 :=
      (continuousOn_fst_Qd0.pow 2).mul (continuousOn_uncurry_of_smoothOpen (hΨ.pzIter 2))
    have hΦc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2) Qd0 :=
      continuousOn_uncurry_of_smoothOpen (smoothOpen_pthIter_two hΨ)
    have hcut : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1) Qd0 :=
      ((Work.FTS.EllipticEst.cut_contDiff n).continuous.comp continuous_fst).continuousOn
    have hmid : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2
        * Work.Spaces.pthIter 2 Ψ p.1 p.2 * Work.FTS.EllipticEst.AngSecond.w2 p.1
        * Work.FTS.EllipticEst.AngSecond.sig p.2) Qd0 :=
      ((hQc.mul hΦc).mul continuousOn_w2_Qd0).mul continuousOn_sig_Qd0
    exact hcut.mul hmid
  refine (hbase.norm).mono' (Work.Spaces.aesm_of_continuousOn_Qd _ hcont) ?_
  filter_upwards with p
  have hc1 : |Work.FTS.EllipticEst.cut n p.1| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [Work.FTS.EllipticEst.cut_nonneg n p.1],
      Work.FTS.EllipticEst.cut_le_one n p.1⟩
  have hEq : Work.FTS.EllipticEst.cut n p.1 * Work.FTS.EllipticEst.AngSecond.Akern Ψ p.1 p.2
      = Work.FTS.EllipticEst.cut n p.1
          * ((fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) p.1 p.2
            * (Work.Spaces.pthIter 2 Ψ) p.1 p.2
            * Work.FTS.EllipticEst.AngSecond.w2 p.1
            * Work.FTS.EllipticEst.AngSecond.sig p.2) := by
    simp only [Work.FTS.EllipticEst.AngSecond.Akern]
  rw [hEq, norm_mul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) hc1

theorem prod_integrable_sig_nice (α : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hG : Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.2
        * Work.FTS.EllipticEst.AngSecond.nice n Ψ p.1 p.2) muP := by
  obtain ⟨K, hKpos, hKb, -, -⟩ := Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
  have hKnn : (0 : ℝ) ≤ K := le_of_lt hKpos
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  let F : ℝ × ℝ → ℝ := fun p => Work.FTS.EllipticEst.AngSecond.sig p.2
    * Work.FTS.EllipticEst.AngSecond.nice n Ψ p.1 p.2
  show MeasureTheory.Integrable F muP
  have hcont : ContinuousOn F Qd0 := by
    have hGc : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz Ψ p.1 p.2) Qd0 :=
      continuousOn_fst_Qd0.mul (continuousOn_uncurry_of_smoothOpen hΨ.pz)
    have hPc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2) Qd0 :=
      continuousOn_uncurry_of_smoothOpen (smoothOpen_pthIter_two hΨ)
    have hHc : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
        Qd0 :=
      continuousOn_fst_Qd0.mul (continuousOn_uncurry_of_smoothOpen (smoothOpen_pthIter_two hΨ).pz)
    have hcut : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1) Qd0 :=
      ((Work.FTS.EllipticEst.cut_contDiff n).continuous.comp continuous_fst).continuousOn
    have hdcut : ContinuousOn (fun p : ℝ × ℝ => deriv (Work.FTS.EllipticEst.cut n) p.1) Qd0 :=
      ((Work.FTS.EllipticEst.AngSecond.continuous_deriv_cut n).comp continuous_fst).continuousOn
    have hone : ContinuousOn (fun p : ℝ × ℝ => (1 : ℝ) + p.1) Qd0 :=
      (continuous_const.add continuous_fst).continuousOn
    have hne : ∀ p ∈ Qd0, (1 : ℝ) + p.1 ≠ 0 := by
      rintro ⟨z, θ⟩ hzp
      have h1 : (0 : ℝ) < z := hzp.1
      linarith
    have hfrac : ContinuousOn (fun p : ℝ × ℝ => 4 * (p.1 * Work.Spaces.pz Ψ p.1 p.2)
        * (Work.Spaces.pthIter 2 Ψ p.1 p.2) / (1 + p.1)) Qd0 :=
      (((continuousOn_const (c := (4 : ℝ))).mul hGc).mul hPc).div hone hne
    have hsum : ContinuousOn (fun p : ℝ × ℝ => 2 * (p.1 * Work.Spaces.pz Ψ p.1 p.2)
          * (Work.Spaces.pthIter 2 Ψ p.1 p.2)
        + (p.1 * Work.Spaces.pz Ψ p.1 p.2)
          * (p.1 * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
        - 4 * (p.1 * Work.Spaces.pz Ψ p.1 p.2)
          * (Work.Spaces.pthIter 2 Ψ p.1 p.2) / (1 + p.1)) Qd0 :=
      (((continuousOn_const (c := (2 : ℝ))).mul hGc).mul hPc).add (hGc.mul hHc) |>.sub hfrac
    have hinner : ContinuousOn (fun p : ℝ × ℝ =>
        Work.FTS.EllipticEst.cut n p.1 * Work.FTS.EllipticEst.AngSecond.w2 p.1
          * (2 * (p.1 * Work.Spaces.pz Ψ p.1 p.2) * (Work.Spaces.pthIter 2 Ψ p.1 p.2)
            + (p.1 * Work.Spaces.pz Ψ p.1 p.2)
              * (p.1 * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
            - 4 * (p.1 * Work.Spaces.pz Ψ p.1 p.2)
              * (Work.Spaces.pthIter 2 Ψ p.1 p.2) / (1 + p.1))
        + Work.FTS.EllipticEst.AngSecond.w2 p.1
          * ((p.1 * Work.Spaces.pz Ψ p.1 p.2) * (Work.Spaces.pthIter 2 Ψ p.1 p.2))
          * (p.1 * deriv (Work.FTS.EllipticEst.cut n) p.1)) Qd0 :=
      ((hcut.mul continuousOn_w2_Qd0).mul hsum).add
        ((continuousOn_w2_Qd0.mul (hGc.mul hPc)).mul (continuousOn_fst_Qd0.mul hdcut))
    exact continuousOn_sig_Qd0.mul hinner
  have haesm : AEStronglyMeasurable F muP := Work.Spaces.aesm_of_continuousOn_Qd F hcont
  rw [MeasureTheory.integrable_prod_iff haesm]
  constructor
  · filter_upwards [Work.FTS.EllipticEst.AngSecond.ae_pos_of_Iz,
      MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hzpos hz
    have hz0 : 0 ≤ z := le_of_lt hzpos
    have hdom : MeasureTheory.IntegrableOn (fun θ => 12 * (1 + K)
        * (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ))
        Work.Spaces.Iθ :=
      ((((hG.1 z hz).add (hΦ.1 z hz)).add (hH.1 z hz))).const_mul _
    refine hdom.mono' (Work.Spaces.aesm_slice_of_continuousOn_Qd F hcont hzpos) ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have hFval : F (z, θ) = Work.FTS.EllipticEst.AngSecond.sig θ
        * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ := rfl
    rw [hFval, Real.norm_eq_abs]
    exact abs_sig_nice_le α K n Ψ hKnn (hKb n) hz0 hθ
  · have haesm2 : AEStronglyMeasurable
        (fun z : ℝ => ∫ θ, ‖F (z, θ)‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      haesm.norm.integral_prod_right'
    have hdom2 : MeasureTheory.Integrable (fun z : ℝ => 12 * (1 + K)
        * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.const_mul (((hG.2.add hΦ.2)).add hH.2) _
    refine hdom2.mono' haesm2 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hz0 : 0 ≤ z := Set.mem_Ici.mp hz
    have hFnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, ‖F (z, θ)‖ :=
      integral_nonneg (fun θ => norm_nonneg (F (z, θ)))
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, ‖F (z, θ)‖ ≤ 12 * (1 + K)
        * (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ
          + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
          + Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ) := by
      intro θ hθ
      have hFval : F (z, θ) = Work.FTS.EllipticEst.AngSecond.sig θ
          * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ := rfl
      rw [hFval, Real.norm_eq_abs]
      exact abs_sig_nice_le α K n Ψ hKnn (hKb n) hz0 hθ
    have hmono : (∫ θ in Work.Spaces.Iθ, ‖F (z, θ)‖)
        ≤ ∫ θ in Work.Spaces.Iθ, 12 * (1 + K)
          * (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz Ψ) z θ
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
            + Work.Spaces.HkIntegrand α 0
                (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z θ) :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun θ => norm_nonneg _))
        ((((hG.1 z hz).add (hΦ.1 z hz)).add (hH.1 z hz)).const_mul _)
        (ae_restrict_of_forall_mem measurableSet_Icc hpt)
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const_mul]
    have h1 := MeasureTheory.integral_add ((hG.1 z hz).add (hΦ.1 z hz)) (hH.1 z hz)
    have h2 := MeasureTheory.integral_add (hG.1 z hz) (hΦ.1 z hz)
    simp only [Pi.add_apply] at h1 h2
    rw [h1, h2]
end

/-! ## The two Fubini swaps -/

theorem swap_cut_akern (α : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ :=
  MeasureTheory.integral_integral_swap (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun z θ => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ)
    (prod_integrable_cut_akern α n Ψ hsm hQ hΦ)

theorem swap_sig_nice (α : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hG : Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ
        * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.sig θ
          * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ :=
  MeasureTheory.integral_integral_swap (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun z θ => Work.FTS.EllipticEst.AngSecond.sig θ
      * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ)
    (prod_integrable_sig_nice α n Ψ hsm hG hΦ hH)

/-! ## The cut-off identity in the open class -/

theorem I1_cutoff_identity_open (α : ℝ) (n : ℕ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hG : Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
        (Work.Spaces.pthIter 2 Ψ)
      = - ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.AngSecond.sig θ
            * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ := by
  calc Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
        (Work.Spaces.pthIter 2 Ψ)
      = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.Afun Ψ z :=
        Work.FTS.EllipticEst.AngSecond.IP_cut_eq n Ψ
    _ = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        rw [Work.FTS.EllipticEst.AngSecond.Afun, MeasureTheory.integral_const_mul]
    _ = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ := swap_cut_akern α n Ψ hsm hQ hΦ
    _ = ∫ θ in Work.Spaces.Iθ,
          -(∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.sig θ
              * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
        rcases eq_or_ne θ 0 with rfl | hθ0
        · have hz1 : (fun z : ℝ => Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.Akern Ψ z 0) = fun _ : ℝ => (0 : ℝ) := by
            funext z
            simp only [Work.FTS.EllipticEst.AngSecond.Akern, sig_zero, mul_zero]
          have hz2 : (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.sig 0
              * Work.FTS.EllipticEst.AngSecond.nice n Ψ z 0) = fun _ : ℝ => (0 : ℝ) := by
            funext z
            simp only [sig_zero, zero_mul]
          rw [hz1, hz2]
          simp
        · rcases eq_or_ne θ (Real.pi / 2) with rfl | hθπ
          · have hz1 : (fun z : ℝ => Work.FTS.EllipticEst.cut n z
                * Work.FTS.EllipticEst.AngSecond.Akern Ψ z (Real.pi / 2))
                = fun _ : ℝ => (0 : ℝ) := by
              funext z
              simp only [Work.FTS.EllipticEst.AngSecond.Akern, sig_pi_half, mul_zero]
            have hz2 : (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.sig (Real.pi / 2)
                * Work.FTS.EllipticEst.AngSecond.nice n Ψ z (Real.pi / 2))
                = fun _ : ℝ => (0 : ℝ) := by
              funext z
              simp only [sig_pi_half, zero_mul]
            rw [hz1, hz2]
            simp
          · have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
              ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0),
                lt_of_le_of_ne hθ.2 hθπ⟩
            rw [show (fun z : ℝ => Work.FTS.EllipticEst.cut n z
                  * Work.FTS.EllipticEst.AngSecond.Akern Ψ z θ)
                = fun z : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ
                    * (Work.Spaces.pzIter 2 Ψ z θ
                      * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ
                        * Work.FTS.EllipticEst.cut n z
                        * Work.FTS.EllipticEst.AngSecond.w2 z)) from by
              funext z
              simp only [Work.FTS.EllipticEst.AngSecond.Akern]
              ring]
            rw [MeasureTheory.integral_const_mul]
            rw [show (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.sig θ
                  * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ)
                = Work.FTS.EllipticEst.AngSecond.sig θ
                  * ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ from
                MeasureTheory.integral_const_mul _ _]
            rw [Work.FTS.EllipticEst.H2W.AeWAux.niceSliceIBPOpen n Ψ hsm hθIoo]
            ring
    _ = - ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.AngSecond.sig θ
            * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ := by
        rw [MeasureTheory.integral_neg, (swap_sig_nice α n Ψ hsm hG hΦ hH).symm]

/-! ## The radial integration by parts of `I₁`, in the open class -/

theorem I1_ibp_identity_open (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Ψ) Qd0)
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hG : Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (Work.Spaces.pthIter 2 Ψ)
      = - Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (Work.FTS.EllipticEst.AngSecond.H Ψ)
        - Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hGc : ContinuousOn (Function.uncurry (Work.FTS.EllipticEst.AngSecond.G Ψ)) Qd0 :=
    continuousOn_uncurry_of_smoothOpen (smoothOpen_fst_mul_pz hΨ)
  have hΦc : ContinuousOn (Function.uncurry (Work.FTS.EllipticEst.AngSecond.Phi Ψ)) Qd0 :=
    continuousOn_uncurry_of_smoothOpen (smoothOpen_pthIter_two hΨ)
  have hHc : ContinuousOn (Function.uncurry (Work.FTS.EllipticEst.AngSecond.H Ψ)) Qd0 :=
    continuousOn_uncurry_of_smoothOpen (smoothOpen_fst_mul_pz_pthIter_two hΨ)
  have hGm : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.G Ψ)
      (Work.FTS.EllipticEst.AngSecond.G Ψ) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hG
  have hΦm : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.Phi Ψ)
      (Work.FTS.EllipticEst.AngSecond.Phi Ψ) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hΦ
  have hHm : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.H Ψ)
      (Work.FTS.EllipticEst.AngSecond.H Ψ) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hH
  have hQΦ : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ) :=
    IPMem_of_diag_open
      (continuousOn_uncurry_of_smoothOpen (smoothOpen_sq_mul_pzIter hΨ)) hΦc
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hQ) hΦm
  have hGΦ : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.G Ψ)
      (Work.FTS.EllipticEst.AngSecond.Phi Ψ) :=
    IPMem_of_diag_open hGc hΦc hGm hΦm
  have hGH : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.AngSecond.G Ψ)
      (Work.FTS.EllipticEst.AngSecond.H Ψ) :=
    IPMem_of_diag_open hGc hHc hGm hHm
  have hAfun : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngSecond.Afun Ψ)
      Work.Spaces.Iz := Work.FTS.EllipticEst.AngSecond.integrableOn_Afun Ψ hQΦ
  have hPhi1 : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngSecond.Phi1 Ψ)
      Work.Spaces.Iz := Work.FTS.EllipticEst.AngSecond.integrableOn_Phi1 Ψ hGΦ
  have hBfun : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngSecond.Bfun Ψ)
      Work.Spaces.Iz := Work.FTS.EllipticEst.AngSecond.integrableOn_Bfun Ψ hGΦ hGH
  have hkey : ∀ n : ℕ, (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.Afun Ψ z)
      = (- (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.Bfun Ψ z))
        - (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z
            * (z * deriv (Work.FTS.EllipticEst.cut n) z)) := by
    intro n
    have h1 := I1_cutoff_identity_open α n Ψ hsm hQ hG hΦ hH
    rw [Work.FTS.EllipticEst.AngSecond.IP_cut_eq n Ψ] at h1
    have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.AngSecond.sig θ
            * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ)
        = (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.Bfun Ψ z)
          + (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z
              * (z * deriv (Work.FTS.EllipticEst.cut n) z)) := by
      rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.AngSecond.sig θ
              * Work.FTS.EllipticEst.AngSecond.nice n Ψ z θ)
          = ∫ z in Work.Spaces.Iz, (Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.Bfun Ψ z
              + Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z
                * (z * deriv (Work.FTS.EllipticEst.cut n) z)) from
          MeasureTheory.setIntegral_congr_fun measurableSet_Ici
            (fun z hz => Work.FTS.EllipticEst.AngSecond.nfun_eq n Ψ hGΦ hGH hz)]
      exact MeasureTheory.integral_add
        (Work.FTS.EllipticEst.AngSecond.integrableOn_cut_mul hBfun n)
        (Work.FTS.EllipticEst.AngSecond.integrableOn_cutDeriv_mul hPhi1 n)
    rw [h1, h2]
    ring
  have htA := Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cut_mul hAfun
  have htB := Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cut_mul hBfun
  have htC := Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cutDeriv_mul hPhi1
  have hseq : (fun n : ℕ => ∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.Afun Ψ z)
      = fun n : ℕ => (- (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.Bfun Ψ z))
          - (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z
              * (z * deriv (Work.FTS.EllipticEst.cut n) z)) :=
    funext hkey
  rw [hseq] at htA
  have hlim : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Afun Ψ z)
      = (- (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Bfun Ψ z)) - 0 :=
    tendsto_nhds_unique htA (htB.neg.sub htC)
  have hA : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Afun Ψ z)
      = Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          (Work.Spaces.pthIter 2 Ψ) := by
    rw [Work.FTS.EllipticEst.AngSecond.IP]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ _ => by simp only [Work.FTS.EllipticEst.AngSecond.Akern])
  have hPhi1c : (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z)
      = Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ) := by
    rw [show (∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z)
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Cwfun Ψ z from
        MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => by
          rw [Work.FTS.EllipticEst.AngSecond.Cwfun, Work.FTS.EllipticEst.AngSecond.Phi1,
            ← MeasureTheory.integral_const_mul]
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
            (fun θ _ => by ring))]
    rw [Work.FTS.EllipticEst.AngSecond.IP]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ =>
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring))
  have hBHc : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.BHfun Ψ z)
      = Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
          (Work.FTS.EllipticEst.AngSecond.H Ψ) := by
    rw [Work.FTS.EllipticEst.AngSecond.IP]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ =>
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring))
  have hBZ : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Bfun Ψ z)
      = Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (Work.FTS.EllipticEst.AngSecond.H Ψ)
        + Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ) := by
    have hsplit : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Bfun Ψ z)
        = ∫ z in Work.Spaces.Iz, (Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AngSecond.Phi1 Ψ z
            + Work.FTS.EllipticEst.AngSecond.BHfun Ψ z) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ici
        (fun z hz => Work.FTS.EllipticEst.AngSecond.Bfun_eq Ψ hGΦ hGH hz)
    rw [hsplit, MeasureTheory.integral_add
      (Work.FTS.EllipticEst.AngSecond.integrableOn_cwPhi1 Ψ hPhi1)
      (Work.FTS.EllipticEst.AngSecond.integrableOn_BHfun Ψ hGH), hPhi1c, hBHc]
    ring
  have hgoal : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.Afun Ψ z)
      = - Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (Work.FTS.EllipticEst.AngSecond.H Ψ)
        - Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AngSecond.G Ψ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngSecond.Phi Ψ z θ) := by
    rw [hlim, hBZ]
    ring
  rw [← hA]
  exact hgoal

theorem I1ZibpOpenAbs (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ z : ℝ, Ψ z 0 = 0) (hπ : ∀ z : ℝ, Ψ z (Real.pi / 2) = 0)
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hG : Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ))
    (hΦ : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :
    Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (Work.Spaces.pthIter 2 Ψ)
      = - Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.Dz Ψ)
            (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
        - Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.Dz Ψ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * Work.Spaces.pthIter 2 Ψ z θ) :=
  I1_ibp_identity_open α Ψ hsm hQ hG hΦ hH

end Work.FTS.EllipticEst.H2W.WeakAux
