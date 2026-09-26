/-
# The smoothness and `r`-seminorm bundles for the layer pieces `PSum`

This file assembles `Work.Asymptotics.PSum` (the explicit right-hand side of the funnel
decomposition of the CKMRV layer) from the five pieces

  `layerLow`, `sinSq · preT(·²)`, `sinSq · spikeT(·²)`, `sinSq · tailT(·²)`, `highTailClosed`,

proving that each is smooth in the Fourier variable `r` and inheriting their `c · (scale τ)^N`
seminorm bounds.
-/
import Mathlib
import Submission.Work.Asymptotics.FunnelAsm.funnelDefs
import Submission.Work.Asymptotics.funnelPreSeminorm
import Submission.Work.Asymptotics.funnelSpikeSeminorm
import Submission.Work.Asymptotics.funnelTailSeminorm
import Submission.Work.Asymptotics.FunnelAsm.highTailClosedSeminorm
import Submission.Work.Asymptotics.FunnelAsm.funnelLayerLowSeminorm
import Submission.Work.Asymptotics.layerPieces_smooth
import Submission.Work.Asymptotics.paperLayer_smooth
import Submission.Work.Asymptotics.measurable_Kfun_snd_all
import Submission.Work.Asymptotics.jInvariant_level_null
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Asymptotics.FunnelAsm

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology ContDiff

set_option maxHeartbeats 4000000

private lemma imagAxis_eq_ofComplex' (t : ℝ) (ht : 0 < t) :
    Work.Kernels.imagAxis t ht = (UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) : ℍ) := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos]
  · exact UpperHalfPlane.ext rfl
  · simpa [Complex.mul_im] using ht

/-- `layerLow` is smooth in the `r`-variable on the funnel (the a.e. flatness of the kernel at
the cusp `0` suffices). -/
theorem layerLow_contDiff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n : ℕ) {τ : UpperHalfPlane} (hτ : Work.Asymptotics.Funnel τ) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) := by
  obtain ⟨C, c, m, hCpos, hcpos, hm0, hflat⟩ := HalfFunnel.funnelFlat ℓ d hd
  obtain ⟨K, hKpos, hK⟩ := MFix.exp_neg_div_le_mul_rpow c m hcpos
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
      (volume.restrict (Set.Ioc 0 1)) :=
    (Work.Asymptotics.measurable_Kaxis_of_measurable (Work.Kernels.Kfun ℓ d) τ
      (Work.Asymptotics.measurable_Kfun_snd_all ℓ d hd τ)).aestronglyMeasurable
  have hB0 : (0 : ℝ) ≤ C * 2 ^ m * K := by positivity
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C * 2 ^ m * K := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [(measure_eq_zero_iff_ae_notMem.mp (Work.Asymptotics.jInvariant_level_null τ))]
      with u hu huIoc
    have hu0 : 0 < u := huIoc.1
    have hu1 : u ≤ 1 := huIoc.2
    have hne : Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis u hu0) := fun hcon =>
      hu ⟨hu0, by rwa [imagAxis_eq_ofComplex' u hu0] at hcon⟩
    have hb := hflat τ u hu0 hτ.1 hτ.2 hu1 hne
    have hKbd : Real.exp (-(c / u)) ≤ K * u ^ m := hK u hu0 hu1
    have hfac : (1 + 1 / u) ^ m * u ^ m ≤ 2 ^ m := by
      rw [← Real.mul_rpow (by positivity) hu0.le]
      refine Real.rpow_le_rpow (by positivity) ?_ hm0
      have : (1 + 1 / u) * u = u + 1 := by field_simp
      rw [this]; linarith
    have hstep : (1 + 1 / u) ^ m * Real.exp (-(c / u)) ≤ 2 ^ m * K := by
      calc (1 + 1 / u) ^ m * Real.exp (-(c / u)) ≤ (1 + 1 / u) ^ m * (K * u ^ m) :=
            mul_le_mul_of_nonneg_left hKbd (by positivity)
        _ = ((1 + 1 / u) ^ m * u ^ m) * K := by ring
        _ ≤ 2 ^ m * K := mul_le_mul_of_nonneg_right hfac hKpos.le
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ u‖
        ≤ C * (1 + 1 / u) ^ m * Real.exp (-(c / u)) := hb
      _ ≤ C * (2 ^ m * K) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hstep hCpos.le
      _ = C * 2 ^ m * K := by ring
  have hcd := Work.Asymptotics.contDiff_omega_intervalIntegral_exp (κ := fun t : ℝ =>
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) hB0 hmeas hbound
  have hsin : ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s) :=
    ContDiff.of_le Work.Asymptotics.contDiff_omega_sinSq le_top
  have hfun : (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s)
      = fun s : ℝ => Work.Asymptotics.sinSq s * ∫ t in (0:ℝ)..1,
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))) := rfl
  rw [hfun]
  exact hsin.mul (ContDiff.of_le hcd le_top)

/-- `preT` is smooth on `(-1,∞)`. -/
theorem preT_contDiffOn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n : ℕ) {τ : UpperHalfPlane} (hτ : Work.Asymptotics.Funnel τ) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun y : ℝ => Work.Asymptotics.preT ℓ d τ y)
      (Set.Ioi (-1)) := by
  obtain ⟨c, N, hc, hN, hb⟩ := Work.Asymptotics.preT_deriv_bound ℓ d hd n
  exact (hb τ hτ).1

/-- `spikeT` is smooth on `(-1,∞)`. -/
theorem spikeT_contDiffOn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n : ℕ) {τ : UpperHalfPlane} (hτ : Work.Asymptotics.Funnel τ) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Asymptotics.spikeT ℓ d τ) (Set.Ioi (-1)) := by
  obtain ⟨B, hB0, hBw⟩ := Work.Asymptotics.spikeWindow_bound ℓ d hd τ hτ
  have hab : τ.im - 1 ≤ τ.im + 1 := by linarith
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
      (volume.restrict (Set.Ioc (τ.im - 1) (τ.im + 1))) :=
    (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable
  have hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (τ.im - 1) (τ.im + 1))),
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ B := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact hBw t (le_of_lt ht.1) ht.2
  have hfun : Work.Asymptotics.spikeT ℓ d τ = fun y : ℝ => ∫ t in (τ.im - 1)..(τ.im + 1),
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * (Real.exp (-(Real.pi * y * t)) : ℂ) := by
    funext y
    rw [Work.Asymptotics.spikeT]
    apply intervalIntegral.integral_congr
    intro t _
    show Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.wgt y t
      = Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * (Real.exp (-(Real.pi * y * t)) : ℂ)
    rw [Work.Asymptotics.wgt_apply, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hfun]
  exact Work.Asymptotics.contDiffOn_intervalIntegral_exp_bound _ _ _ hab hmeas hB0 hbd n

/-- `tailT` is smooth on `(-1,∞)`: after shifting the contour by `Im τ` it becomes an explicit
exponential times the `tailIntegral` machine of `Work.Asymptotics.tailIntegral`. -/
theorem tailT_contDiffOn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n : ℕ) {τ : UpperHalfPlane} (hτ : Work.Asymptotics.Funnel τ) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Asymptotics.tailT ℓ d τ) (Set.Ioi (-1)) := by
  set c : ℝ := τ.im with hcdef
  have hc0 : (0 : ℝ) ≤ c := by rw [hcdef]; exact τ.im_pos.le
  set h : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
    - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t with hhdef
  set g : ℝ → ℂ := fun u => h (u + c) with hgdef
  obtain ⟨C, N, M, hC0, hN0, hM0, hbd⟩ := Work.Asymptotics.funnelKernelTailGcuspW ℓ d hd
  have hhmeas : Measurable h := by
    rw [hhdef]
    have h1 : Measurable (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) := by
      unfold Work.Asymptotics.Aexp
      fun_prop
    exact (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub h1
  have hgmeas : AEStronglyMeasurable g (volume.restrict (Set.Ici (1:ℝ))) :=
    (hhmeas.comp (measurable_id.add_const c)).aestronglyMeasurable
  have hgbd : ∀ᵐ u ∂(volume.restrict (Set.Ici (1:ℝ))),
      ‖g u‖ ≤ (C * (Work.Kernels.scale τ) ^ N * (1 + c) ^ M * 2 ^ M) * u ^ M
        * Real.exp (-(Real.pi * u)) := by
    rw [ae_restrict_iff' measurableSet_Ici]
    filter_upwards with u hu
    have hu1 : 1 ≤ u := hu
    have hcu : τ.im + 1 ≤ u + c := by rw [hcdef]; linarith
    have hb := hbd τ (u + c) hτ hcu
    have htc : u + c - τ.im = u := by rw [hcdef]; ring
    rw [htc] at hb
    rw [hgdef]
    have hfac : (1 + (u + c)) ^ M ≤ (1 + c) ^ M * (2 ^ M * u ^ M) := by
      have h1 : 1 + (u + c) ≤ (1 + c) * (1 + u) := by nlinarith [hc0, hu1]
      calc (1 + (u + c)) ^ M ≤ ((1 + c) * (1 + u)) ^ M :=
            Real.rpow_le_rpow (by linarith) h1 hM0
        _ = (1 + c) ^ M * (1 + u) ^ M := Real.mul_rpow (by linarith) (by linarith)
        _ ≤ (1 + c) ^ M * (2 * u) ^ M := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) M)
            exact Real.rpow_le_rpow (by linarith) (by linarith) hM0
        _ = (1 + c) ^ M * (2 ^ M * u ^ M) := by
            rw [Real.mul_rpow (by norm_num) (by linarith)]
    have hsc : (0 : ℝ) ≤ C * (Work.Kernels.scale τ) ^ N :=
      mul_nonneg hC0 (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N)
    calc ‖h (u + c)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + (u + c)) ^ M * Real.exp (-(Real.pi * u)) := hb
      _ ≤ C * (Work.Kernels.scale τ) ^ N * ((1 + c) ^ M * (2 ^ M * u ^ M))
            * Real.exp (-(Real.pi * u)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hsc)
            (Real.exp_nonneg _)
      _ = (C * (Work.Kernels.scale τ) ^ N * (1 + c) ^ M * 2 ^ M) * u ^ M
            * Real.exp (-(Real.pi * u)) := by ring
  have hC' : (0:ℝ) ≤ C * (Work.Kernels.scale τ) ^ N * (1 + c) ^ M * 2 ^ M := by
    have h1 : (0:ℝ) ≤ (1 + c) ^ M := Real.rpow_nonneg (by linarith) M
    have h2 : (0:ℝ) ≤ (2:ℝ) ^ M := Real.rpow_nonneg (by norm_num) M
    exact mul_nonneg (mul_nonneg (mul_nonneg hC0
      (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N)) h1) h2
  have hcd := Work.Asymptotics.tailIntegral_contDiffOn n g hgmeas hC' hM0 hgbd
  have hexp : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun x : ℝ => ((Real.exp (-(Real.pi * c * x)) : ℝ) : ℂ)) (Set.Ioi (-1)) := by
    have h1 : ContDiff ℝ (n : WithTop ℕ∞)
        (fun x : ℝ => Real.exp (-(Real.pi * c * x))) := by fun_prop
    exact (Complex.ofRealCLM.contDiff.comp h1).contDiffOn
  have hmul := hcd.mul hexp
  have hshift : ∀ x : ℝ, Work.Asymptotics.tailT ℓ d τ x
      = ((Real.exp (-(Real.pi * c * x)) : ℝ) : ℂ) * Work.Asymptotics.tailIntegral g x := by
    intro x
    have hstep1 : ∫ t in Set.Ioi (c + 1), h t * Work.Asymptotics.wgt x t
        = ∫ t in Set.Ici (c + 1), h t * Work.Asymptotics.wgt x t := by
      refine MeasureTheory.setIntegral_congr_set ?_
      rw [MeasureTheory.ae_eq_set]
      refine ⟨?_, ?_⟩
      · have hdiff : Set.Ioi (c + 1) \ Set.Ici (c + 1) = ∅ := by
          ext y
          constructor
          · rintro ⟨h1, h2⟩
            simp only [Set.mem_Ici] at h2
            exact absurd (le_of_lt h1) h2
          · intro h; exact absurd h (by simp)
        rw [hdiff]; simp
      · have hsingle : Set.Ici (c + 1) \ Set.Ioi (c + 1) = {c + 1} := by
          ext y
          simp only [Set.mem_diff, Set.mem_Ici, Set.mem_Ioi, Set.mem_singleton_iff]
          constructor
          · rintro ⟨h1, h2⟩; linarith
          · intro hh; subst hh; exact ⟨le_rfl, lt_irrefl _⟩
        rw [hsingle]; simp
    have hstep2 : ∫ t in Set.Ici (c + 1), h t * Work.Asymptotics.wgt x t
        = ∫ u in Set.Ici (1:ℝ), h (u + c) * Work.Asymptotics.wgt x (u + c) := by
      rw [(MeasureTheory.integral_indicator measurableSet_Ici).symm]
      rw [(MeasureTheory.integral_add_right_eq_self (fun t => (Set.Ici (c + 1)).indicator
        (fun t' => h t' * Work.Asymptotics.wgt x t') t) c).symm]
      rw [(MeasureTheory.integral_indicator measurableSet_Ici).symm]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
      simp only [Set.indicator_apply, Set.mem_Ici]
      by_cases ha : (1:ℝ) ≤ a
      · rw [if_pos ha, if_pos (by linarith : c + 1 ≤ a + c)]
      · rw [if_neg ha, if_neg (by linarith : ¬ (c + 1 ≤ a + c))]
    have hstep3 : ∫ u in Set.Ici (1:ℝ), h (u + c) * Work.Asymptotics.wgt x (u + c)
        = ((Real.exp (-(Real.pi * c * x)) : ℝ) : ℂ) * Work.Asymptotics.tailIntegral g x := by
      rw [Work.Asymptotics.tailIntegral]
      rw [show (∫ u in Set.Ici (1:ℝ), h (u + c) * Work.Asymptotics.wgt x (u + c))
          = ∫ u in Set.Ici (1:ℝ), ((Real.exp (-(Real.pi * c * x)) : ℝ) : ℂ)
              * (g u * (Real.exp (-(Real.pi * x * u)) : ℂ)) from ?_]
      · rw [MeasureTheory.integral_const_mul]
      · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun u _ => ?_)
        rw [hgdef]
        simp only
        rw [Work.Asymptotics.wgt_apply]
        rw [show (-(↑(Real.pi * x * (u + c)) : ℂ)) = ((-(Real.pi * x * (u + c)) : ℝ) : ℂ) by
          push_cast; ring]
        have hexp : Complex.exp ((-(Real.pi * x * (u + c)) : ℝ) : ℂ)
            = ((Real.exp (-(Real.pi * x * u)) : ℝ) : ℂ)
              * ((Real.exp (-(Real.pi * c * x)) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add]
          congr 1
          ring
        rw [hexp]
        ring
    have htail : Work.Asymptotics.tailT ℓ d τ x
        = ∫ t in Set.Ioi (c + 1), h t * Work.Asymptotics.wgt x t := by
      rw [Work.Asymptotics.tailT, hhdef, hcdef]
    rw [htail, hstep1, hstep2, hstep3]
  refine hmul.congr (fun x hx => ?_)
  rw [hshift x]; ring

/-- `highTailClosed` is smooth in `r` (it is an explicit elementary function). -/
theorem highTailClosed_contDiff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (n : ℕ)
    (τ : UpperHalfPlane) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) := by
  have hpsi : ContDiff ℝ (n : WithTop ℕ∞)
      (fun x : ℝ => ((Work.Asymptotics.psi1 x : ℝ) : ℂ)) :=
    ContDiff.of_le Work.Asymptotics.psi1_contDiff (WithTop.coe_le_coe.mpr le_top)
  have hpolyR : ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => Real.pi * s ^ 2) := by fun_prop
  have hpoly2R : ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => Real.pi * s ^ 2 - 2 * Real.pi) := by
    fun_prop
  have hL : ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => ((Real.pi * s ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hpolyR
  have hM : ContDiff ℝ (n : WithTop ℕ∞)
      (fun s : ℝ => ((Real.pi * s ^ 2 - 2 * Real.pi : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hpoly2R
  have h1 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun s : ℝ => ((Work.Asymptotics.psi1 (Real.pi * s ^ 2) : ℝ) : ℂ)) := hpsi.comp hpolyR
  have h2 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun s : ℝ => ((Work.Asymptotics.psi1 (Real.pi * s ^ 2 - 2 * Real.pi) : ℝ) : ℂ)) :=
    hpsi.comp hpoly2R
  have h3 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun s : ℝ => (Real.exp (-((Real.pi * s ^ 2 * (τ.im + 1) : ℝ))) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (by fun_prop))
  have h4 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun s : ℝ => (Real.exp (-(((Real.pi * s ^ 2 - 2 * Real.pi) * (τ.im + 1)) : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (by fun_prop))
  have hc : (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) = fun s : ℝ =>
      ((Real.pi * s ^ 2 : ℝ) : ℂ) * ((Work.Asymptotics.psi1 (Real.pi * s ^ 2) : ℝ) : ℂ)
        * (Real.exp (-((Real.pi * s ^ 2 * (τ.im + 1) : ℝ))) : ℂ)
        * Work.Asymptotics.Gcusp ℓ d 0 0 τ
      + Complex.I * ((Work.Asymptotics.psi1 (Real.pi * s ^ 2) : ℝ) : ℂ)
        * (1 + ((Real.pi * s ^ 2 : ℝ) : ℂ) * ((τ.im + 1 : ℝ) : ℂ))
        * (Real.exp (-((Real.pi * s ^ 2 * (τ.im + 1) : ℝ))) : ℂ)
        * Work.Asymptotics.Gcusp ℓ d 0 1 τ
      + ((Real.pi * s ^ 2 - 2 * Real.pi : ℝ) : ℂ)
        * ((Work.Asymptotics.psi1 (Real.pi * s ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
        * (Real.exp (-(((Real.pi * s ^ 2 - 2 * Real.pi) * (τ.im + 1)) : ℝ)) : ℂ)
        * Work.Asymptotics.Gcusp ℓ d 1 0 τ
      + Complex.I * ((Work.Asymptotics.psi1 (Real.pi * s ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
        * (1 + ((Real.pi * s ^ 2 - 2 * Real.pi : ℝ) : ℂ) * ((τ.im + 1 : ℝ) : ℂ))
        * (Real.exp (-(((Real.pi * s ^ 2 - 2 * Real.pi) * (τ.im + 1)) : ℝ)) : ℂ)
        * Work.Asymptotics.Gcusp ℓ d 1 1 τ := by
    funext s
    simp only [Work.Asymptotics.highTailClosed]
    rw [show (-(((Real.pi * s ^ 2 : ℝ) : ℂ) * ((τ.im + 1 : ℝ) : ℂ)))
          = ((-(Real.pi * s ^ 2 * (τ.im + 1)) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp]
    rw [show (-(((Real.pi * s ^ 2 - 2 * Real.pi : ℝ) : ℂ) * ((τ.im + 1 : ℝ) : ℂ)))
          = ((-((Real.pi * s ^ 2 - 2 * Real.pi) * (τ.im + 1)) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp]
  rw [hc]
  have ht1 : ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ =>
      ((Real.pi * s ^ 2 : ℝ) : ℂ) * ((Work.Asymptotics.psi1 (Real.pi * s ^ 2) : ℝ) : ℂ)
        * (Real.exp (-((Real.pi * s ^ 2 * (τ.im + 1) : ℝ))) : ℂ)
        * Work.Asymptotics.Gcusp ℓ d 0 0 τ) := (((hL.mul h1).mul h3).mul contDiff_const)
  have ht2 : ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ =>
      Complex.I * ((Work.Asymptotics.psi1 (Real.pi * s ^ 2) : ℝ) : ℂ)
        * (1 + ((Real.pi * s ^ 2 : ℝ) : ℂ) * ((τ.im + 1 : ℝ) : ℂ))
        * (Real.exp (-((Real.pi * s ^ 2 * (τ.im + 1) : ℝ))) : ℂ)
        * Work.Asymptotics.Gcusp ℓ d 0 1 τ) :=
    ((((contDiff_const.mul h1).mul (contDiff_const.add (hL.mul contDiff_const))).mul h3).mul
      contDiff_const)
  have ht3 : ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ =>
      ((Real.pi * s ^ 2 - 2 * Real.pi : ℝ) : ℂ)
        * ((Work.Asymptotics.psi1 (Real.pi * s ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
        * (Real.exp (-(((Real.pi * s ^ 2 - 2 * Real.pi) * (τ.im + 1)) : ℝ)) : ℂ)
        * Work.Asymptotics.Gcusp ℓ d 1 0 τ) := (((hM.mul h2).mul h4).mul contDiff_const)
  have ht4 : ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ =>
      Complex.I * ((Work.Asymptotics.psi1 (Real.pi * s ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
        * (1 + ((Real.pi * s ^ 2 - 2 * Real.pi : ℝ) : ℂ) * ((τ.im + 1 : ℝ) : ℂ))
        * (Real.exp (-(((Real.pi * s ^ 2 - 2 * Real.pi) * (τ.im + 1)) : ℝ)) : ℂ)
        * Work.Asymptotics.Gcusp ℓ d 1 1 τ) :=
    ((((contDiff_const.mul h2).mul (contDiff_const.add (hM.mul contDiff_const))).mul h4).mul
      contDiff_const)
  exact ((ht1.add ht2).add ht3).add ht4

/-- The decomposition of `PSum` into its five explicit pieces. -/
theorem PSum_eq_sum (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) :
    (fun s : ℝ => Work.Asymptotics.PSum ℓ d τ s)
      = (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s)
        + (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.preT ℓ d τ (s ^ 2))
        + (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s ^ 2))
        + (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s ^ 2))
        + (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) := by
  funext s
  simp only [Work.Asymptotics.PSum, Pi.add_apply]
  ring

/-- **The smoothness and seminorm bundle for `PSum`** consumed by
`Work.Asymptotics.funnel_target_of_pieces`. -/
theorem psumData (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    (∀ (τ : UpperHalfPlane), Work.Asymptotics.Funnel τ →
      Differentiable ℝ (fun s : ℝ => Work.Asymptotics.PSum ℓ d τ s)) ∧
    (∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), Work.Asymptotics.Funnel τ → (d = 8 ∨ 2 ≤ r ^ 2) →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.PSum ℓ d τ s) r‖
          ≤ c * (Work.Kernels.scale τ) ^ N) := by
  have hpieces : ∀ (τ : UpperHalfPlane), Work.Asymptotics.Funnel τ → ∀ (n : ℕ),
      ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) ∧
      ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s
        * Work.Asymptotics.preT ℓ d τ (s ^ 2)) ∧
      ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s
        * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) ∧
      ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s
        * Work.Asymptotics.tailT ℓ d τ (s ^ 2)) ∧
      ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) := by
    intro τ hτ n
    have hsin : ContDiff ℝ (n : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s) :=
      ContDiff.of_le Work.Asymptotics.contDiff_omega_sinSq le_top
    have hsq : ContDiffOn ℝ (n : WithTop ℕ∞) (fun s : ℝ => s ^ 2) Set.univ :=
      (contDiff_id.pow 2).contDiffOn
    refine ⟨layerLow_contDiff ℓ d hd n hτ, ?_, ?_, ?_, highTailClosed_contDiff ℓ d n τ⟩
    · have hpre : ContDiffOn ℝ (n : WithTop ℕ∞)
          (fun s : ℝ => Work.Asymptotics.preT ℓ d τ (s ^ 2)) Set.univ :=
        (preT_contDiffOn ℓ d hd n hτ).comp hsq (fun s _ => by
          simp only [Set.mem_Ioi]; linarith [sq_nonneg s])
      exact hsin.mul (contDiffOn_univ.mp hpre)
    · have hsp : ContDiffOn ℝ (n : WithTop ℕ∞)
          (fun s : ℝ => Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) Set.univ :=
        (spikeT_contDiffOn ℓ d hd n hτ).comp hsq (fun s _ => by
          simp only [Set.mem_Ioi]; linarith [sq_nonneg s])
      exact hsin.mul (contDiffOn_univ.mp hsp)
    · have htl : ContDiffOn ℝ (n : WithTop ℕ∞)
          (fun s : ℝ => Work.Asymptotics.tailT ℓ d τ (s ^ 2)) Set.univ :=
        (tailT_contDiffOn ℓ d hd n hτ).comp hsq (fun s _ => by
          simp only [Set.mem_Ioi]; linarith [sq_nonneg s])
      exact hsin.mul (contDiffOn_univ.mp htl)
  constructor
  · intro τ hτ
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpieces τ hτ 1
    have hsum := PSum_eq_sum ℓ d τ
    have hcd : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.PSum ℓ d τ s) := by
      rw [hsum]
      exact ((((h1.add h2).add h3).add h4).add h5)
    exact hcd.differentiable (by simp)
  · intro k l
    obtain ⟨cA, NA, hcA, hNA, hbA⟩ := Work.Asymptotics.funnelLayerLowSeminorm ℓ d hd k l
    obtain ⟨cB, NB, hcB, hNB, hbB⟩ := Work.Asymptotics.funnelPreSeminorm ℓ d hd k l
    obtain ⟨cC, NC, hcC, hNC, hbC⟩ := Work.Asymptotics.funnelSpikeSeminorm ℓ d hd k l
    obtain ⟨cD, ND, hcD, hND, hbD⟩ := Work.Asymptotics.funnelTailSeminorm ℓ d hd k l
    obtain ⟨cE, NE, hcE, hNE, hbE⟩ := Work.Asymptotics.highTailClosedSeminorm ℓ d hd k l
    refine ⟨cA + cB + cC + cD + cE, max (max (max (max NA NB) NC) ND) NE, by positivity,
      by positivity, ?_⟩
    intro τ r hτ hreg
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpieces τ hτ l
    have hsum := PSum_eq_sum ℓ d τ
    have hN1 : NA ≤ max (max (max (max NA NB) NC) ND) NE :=
      le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
        (le_max_left _ _)))
    have hN2 : NB ≤ max (max (max (max NA NB) NC) ND) NE :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
        (le_max_left _ _)))
    have hN3 : NC ≤ max (max (max (max NA NB) NC) ND) NE :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    have hN4 : ND ≤ max (max (max (max NA NB) NC) ND) NE :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hN5 : NE ≤ max (max (max (max NA NB) NC) ND) NE := le_max_right _ _
    have hs1 : 1 ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hs0 : 0 ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
    have hrpow : ∀ {a b : ℝ}, a ≤ b → (Work.Kernels.scale τ) ^ a ≤ (Work.Kernels.scale τ) ^ b :=
      fun h => Real.rpow_le_rpow_of_exponent_le hs1 h
    have hcdA : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r :=
      h1.contDiffAt
    have hcdB : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s
        * Work.Asymptotics.preT ℓ d τ (s ^ 2)) r := h2.contDiffAt
    have hcdC : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s
        * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) r := h3.contDiffAt
    have hcdD : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s
        * Work.Asymptotics.tailT ℓ d τ (s ^ 2)) r := h4.contDiffAt
    have hcdE : ContDiffAt ℝ (l : WithTop ℕ∞)
        (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) r := h5.contDiffAt
    have hab : ContDiffAt ℝ (l : WithTop ℕ∞) ((fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s)
        + (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.preT ℓ d τ (s ^ 2))) r :=
      hcdA.add hcdB
    have habc : ContDiffAt ℝ (l : WithTop ℕ∞) (((fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s)
        + (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.preT ℓ d τ (s ^ 2)))
        + (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s ^ 2))) r :=
      hab.add hcdC
    have habcd : ContDiffAt ℝ (l : WithTop ℕ∞) ((((fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s)
        + (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.preT ℓ d τ (s ^ 2)))
        + (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)))
        + (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s ^ 2))) r :=
      habc.add hcdD
    have e1 := hbA τ r hτ
    have e2 := hbB τ r hτ hreg
    have e3 := hbC τ r hτ
    have e4 := hbD τ r hτ
    have e5 := hbE τ r hτ hreg
    rw [hsum]
    rw [iteratedDeriv_add habcd hcdE, iteratedDeriv_add habc hcdD, iteratedDeriv_add hab hcdC,
      iteratedDeriv_add hcdA hcdB]
    have hnorm : ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.preT ℓ d τ (s ^ 2)) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.tailT ℓ d τ (s ^ 2)) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) r‖
        ≤ ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.preT ℓ d τ (s ^ 2)) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.tailT ℓ d τ (s ^ 2)) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) r‖ := by
      have g1 := norm_add_le (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
            * Work.Asymptotics.preT ℓ d τ (s ^ 2)) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
            * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
            * Work.Asymptotics.tailT ℓ d τ (s ^ 2)) r)
        (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) r)
      have g2 := norm_add_le (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
            * Work.Asymptotics.preT ℓ d τ (s ^ 2)) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
            * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) r)
        (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
            * Work.Asymptotics.tailT ℓ d τ (s ^ 2)) r)
      have g3 := norm_add_le (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
            * Work.Asymptotics.preT ℓ d τ (s ^ 2)) r)
        (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
            * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) r)
      have g4 := norm_add_le (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r)
        (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
            * Work.Asymptotics.preT ℓ d τ (s ^ 2)) r)
      have n1 := norm_nonneg (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r)
      have n2 := norm_nonneg (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
        * Work.Asymptotics.preT ℓ d τ (s ^ 2)) r)
      have n3 := norm_nonneg (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
        * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) r)
      have n4 := norm_nonneg (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
        * Work.Asymptotics.tailT ℓ d τ (s ^ 2)) r)
      have n5 := norm_nonneg (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) r)
      linarith
    have hNmax0 : (0 : ℝ) ≤ max (max (max (max NA NB) NC) ND) NE :=
      le_trans hNA (hN1)
    calc |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.preT ℓ d τ (s ^ 2)) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.tailT ℓ d τ (s ^ 2)) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) r‖
        ≤ |r| ^ k * (‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.preT ℓ d τ (s ^ 2)) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.tailT ℓ d τ (s ^ 2)) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) r‖) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
          + |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.preT ℓ d τ (s ^ 2)) r‖
          + |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.spikeT ℓ d τ (s ^ 2)) r‖
          + |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s
              * Work.Asymptotics.tailT ℓ d τ (s ^ 2)) r‖
          + |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highTailClosed ℓ d τ s) r‖ :=
          by ring
      _ ≤ cA * (Work.Kernels.scale τ) ^ NA + cB * (Work.Kernels.scale τ) ^ NB
          + cC * (Work.Kernels.scale τ) ^ NC + cD * (Work.Kernels.scale τ) ^ ND
          + cE * (Work.Kernels.scale τ) ^ NE := add_le_add (add_le_add (add_le_add (add_le_add
            e1 e2) e3) e4) e5
      _ ≤ (cA + cB + cC + cD + cE) * (Work.Kernels.scale τ)
            ^ (max (max (max (max NA NB) NC) ND) NE) := by
          have f1 := mul_le_mul_of_nonneg_left (hrpow hN1) hcA
          have f2 := mul_le_mul_of_nonneg_left (hrpow hN2) hcB
          have f3 := mul_le_mul_of_nonneg_left (hrpow hN3) hcC
          have f4 := mul_le_mul_of_nonneg_left (hrpow hN4) hcD
          have f5 := mul_le_mul_of_nonneg_left (hrpow hN5) hcE
          have hcomb : cA * (Work.Kernels.scale τ) ^ (max (max (max (max NA NB) NC) ND) NE)
              + cB * (Work.Kernels.scale τ) ^ (max (max (max (max NA NB) NC) ND) NE)
              + cC * (Work.Kernels.scale τ) ^ (max (max (max (max NA NB) NC) ND) NE)
              + cD * (Work.Kernels.scale τ) ^ (max (max (max (max NA NB) NC) ND) NE)
              + cE * (Work.Kernels.scale τ) ^ (max (max (max (max NA NB) NC) ND) NE)
              = (cA + cB + cC + cD + cE)
                * (Work.Kernels.scale τ) ^ (max (max (max (max NA NB) NC) ND) NE) := by ring
          linarith [f1, f2, f3, f4, f5, hcomb]

end Work.Asymptotics.FunnelAsm
