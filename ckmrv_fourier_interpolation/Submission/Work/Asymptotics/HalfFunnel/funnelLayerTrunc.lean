import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.funnelKernelTail
import Submission.Work.Asymptotics.FunnelAsm.funnelDefs
import Submission.Work.Asymptotics.funnelSpikeSeminorm
import Submission.Work.Asymptotics.funnelTailSeminorm
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.HalfFunnel.funnelPreDeclash
import Submission.Work.Asymptotics.HalfFunnel.spike_model_integral
import Submission.Work.Asymptotics.paperLayer_smooth
import Submission.Work.Asymptotics.layerTrunc_seminorm
import Submission.Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun

namespace Work.Asymptotics.HalfFunnel

open MeasureTheory
open scoped ContDiff

/-- `Complex.exp (-(π s² t))` in terms of `Real.exp`. -/
lemma truncExp_eq (s t : ℝ) :
    Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))) = (Real.exp (-(Real.pi * s^2 * t)) : ℂ) := by
  rw [show -(Real.pi * (s:ℂ)^2 * (t:ℂ)) = ((-(Real.pi * s^2 * t) : ℝ) : ℂ) from by push_cast; ring,
    Complex.ofReal_exp]

/-- `wgt x t` in terms of `Real.exp`. -/
lemma truncWgt_eq (x t : ℝ) : Work.Asymptotics.wgt x t = (Real.exp (-(Real.pi * x * t)) : ℂ) := by
  rw [Work.Asymptotics.wgt_apply, ← Complex.ofReal_neg (Real.pi * x * t)]
  exact (Complex.ofReal_exp (-(Real.pi * x * t))).symm

lemma im_le_scale (τ : UpperHalfPlane) : τ.im ≤ Work.Kernels.scale τ :=
  le_trans (Work.Kernels.im_le_coe_norm τ) (Work.Kernels.coe_norm_le_scale τ)

/-- **Analyticity of the compact-interval parametric Laplace integral.**
If `κ` is a.e. strongly measurable and bounded by `B` on `(a,b]`, then
`r ↦ ∫_a^b κ t e^{-π r² t} dt` is analytic (in fact entire in `r²`).  This is the
general-interval version of `Work.Asymptotics.contDiff_omega_intervalIntegral_exp`. -/
theorem laplace_interval_contDiff_omega {κ : ℝ → ℂ} {B : ℝ} {a b : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    (hmeas : AEStronglyMeasurable κ (volume.restrict (Set.Ioc a b)))
    (hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖κ t‖ ≤ B) :
    ContDiff ℝ ⊤ (fun r : ℝ => ∫ t in a..b, κ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
  set M : ℝ := max |a| |b| with hMdef
  have hM0 : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left |a| |b|)
  have htnorm : ∀ t ∈ Set.Ioc a b, |t| ≤ M := by
    intro t ht
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : |a| ≤ M := le_max_left |a| |b|
      have h2 : -M ≤ -|a| := neg_le_neg h1
      have h3 : -|a| ≤ a := neg_abs_le a
      linarith [ht.1]
    · have h1 : b ≤ M := le_trans (le_abs_self b) (le_max_right |a| |b|)
      linarith [ht.2]
  have hconv : ∀ f : ℝ → ℂ, (∫ t in a..b, f t) = ∫ t, f t ∂(volume.restrict (Set.Ioc a b)) := by
    intro f; rw [intervalIntegral.integral_of_le hab]
  have hcont_exp : ∀ w : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(Real.pi * w * (t:ℂ))))
      (volume.restrict (Set.Ioc a b)) := by
    intro w
    exact (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal).neg).aestronglyMeasurable
  have hcont_lin : Continuous (fun t : ℝ => -(Real.pi * (t:ℂ))) :=
    (continuous_const.mul Complex.continuous_ofReal).neg
  have hnormpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [show ‖(Real.pi:ℂ)‖ = |Real.pi| from by
      rw [Complex.norm_def, Complex.normSq_ofReal]; simpa [sq] using Real.sqrt_sq_eq_abs Real.pi]
    exact abs_of_pos Real.pi_pos
  have hdiff : Differentiable ℂ
      (fun z : ℂ => ∫ t in a..b, κ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) := by
    intro z
    have h_int : Integrable (fun t : ℝ => κ t * Complex.exp (-(Real.pi * z * (t:ℂ))))
        (volume.restrict (Set.Ioc a b)) := by
      refine Integrable.mono' (integrable_const (B * Real.exp (Real.pi * |z.re| * M))) ?_ ?_
      · exact hmeas.mul (hcont_exp z)
      · filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hbnd ht
        rw [norm_mul, Complex.norm_exp]
        have hexp : (-(Real.pi * z * (t:ℂ))).re = -(Real.pi * z.re * t) := by
          simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        rw [hexp]
        have h3 : -(z.re * t) ≤ |z.re| * M := by
          calc -(z.re * t) ≤ |z.re * t| := neg_le_abs _
            _ = |z.re| * |t| := abs_mul _ _
            _ ≤ |z.re| * M := mul_le_mul_of_nonneg_left (htnorm t ht) (abs_nonneg _)
        have h1 : -(Real.pi * z.re * t) ≤ Real.pi * (|z.re| * M) := by
          have hh : -(Real.pi * z.re * t) = Real.pi * (-(z.re * t)) := by ring
          rw [hh]
          exact mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
        have h2 : Real.exp (-(Real.pi * z.re * t)) ≤ Real.exp (Real.pi * |z.re| * M) := by
          apply Real.exp_le_exp.mpr
          have hh : Real.pi * |z.re| * M = Real.pi * (|z.re| * M) := by ring
          rw [hh]; exact h1
        exact mul_le_mul hbnd h2 (Real.exp_nonneg _) hB
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ w ∈ Metric.ball z 1,
        ‖κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * w * (t:ℂ)))‖
          ≤ B * Real.pi * M * Real.exp (Real.pi * (|z.re| + 1) * M) := by
      filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hbnd ht
      intro w hw
      rw [Metric.mem_ball, Complex.dist_eq] at hw
      have hre2 : |w.re| ≤ |z.re| + 1 := by
        have h1 := abs_sub_abs_le_abs_sub w.re z.re
        have h2 := Complex.abs_re_le_norm (w - z)
        rw [Complex.sub_re] at h2
        linarith
      rw [norm_mul, norm_mul, Complex.norm_exp, norm_neg]
      have hexp : (-(Real.pi * w * (t:ℂ))).re = -(Real.pi * w.re * t) := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [hexp]
      have htM : |t| ≤ M := htnorm t ht
      have hnpi : ‖(Real.pi : ℂ) * (t:ℂ)‖ = Real.pi * |t| := by
        rw [Complex.norm_mul, hnormpi, Complex.norm_real, Real.norm_eq_abs]
      rw [hnpi]
      have hexple : Real.exp (-(Real.pi * w.re * t)) ≤ Real.exp (Real.pi * (|z.re| + 1) * M) := by
        apply Real.exp_le_exp.mpr
        have h4 : -(w.re * t) ≤ |w.re| * |t| := by
          calc -(w.re * t) ≤ |w.re * t| := neg_le_abs _
            _ = |w.re| * |t| := abs_mul _ _
        have h5 : |w.re| * |t| ≤ (|z.re| + 1) * M := by
          nlinarith [abs_nonneg w.re, abs_nonneg t, hre2, htM]
        nlinarith [Real.pi_pos]
      have hstep1 : ‖κ t‖ * (Real.pi * |t|) ≤ B * (Real.pi * M) :=
        mul_le_mul hbnd (mul_le_mul_of_nonneg_left htM Real.pi_pos.le)
          (mul_nonneg Real.pi_pos.le (abs_nonneg t)) hB
      calc ‖κ t‖ * (Real.pi * |t|) * Real.exp (-(Real.pi * w.re * t))
          ≤ (B * (Real.pi * M)) * Real.exp (Real.pi * (|z.re| + 1) * M) :=
            mul_le_mul hstep1 hexple (Real.exp_nonneg _) (by positivity)
        _ = B * Real.pi * M * Real.exp (Real.pi * (|z.re| + 1) * M) := by ring
    have h_diff : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ w ∈ Metric.ball z 1,
        HasDerivAt (fun w : ℂ => κ t * Complex.exp (-(Real.pi * w * (t:ℂ))))
          (κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * w * (t:ℂ)))) w := by
      filter_upwards with t
      intro w _
      have hlin : HasDerivAt (fun w : ℂ => Real.pi * w * (t:ℂ)) (Real.pi * (t:ℂ)) w := by
        have h := (hasDerivAt_id w).const_mul (Real.pi : ℂ)
        simpa using h.mul_const (t:ℂ)
      have hneg : HasDerivAt (fun w : ℂ => -(Real.pi * w * (t:ℂ))) (-(Real.pi * (t:ℂ))) w :=
        hlin.neg
      have hexp2 : HasDerivAt (fun w : ℂ => Complex.exp (-(Real.pi * w * (t:ℂ))))
          (Complex.exp (-(Real.pi * w * (t:ℂ))) * (-(Real.pi * (t:ℂ)))) w :=
        (Complex.hasDerivAt_exp (-(Real.pi * w * (t:ℂ)))).comp w hneg
      have h3 : HasDerivAt (fun w : ℂ => κ t * Complex.exp (-(Real.pi * w * (t:ℂ))))
          (κ t * (Complex.exp (-(Real.pi * w * (t:ℂ))) * (-(Real.pi * (t:ℂ))))) w :=
        hexp2.const_mul (κ t)
      have heq : κ t * (Complex.exp (-(Real.pi * w * (t:ℂ))) * (-(Real.pi * (t:ℂ))))
          = κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * w * (t:ℂ))) := by ring
      rw [heq] at h3
      exact h3
    have hF'_meas : AEStronglyMeasurable
        (fun t : ℝ => κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ))))
        (volume.restrict (Set.Ioc a b)) := by
      apply AEStronglyMeasurable.mul ?_ (hcont_exp z)
      exact AEStronglyMeasurable.mul hmeas hcont_lin.aestronglyMeasurable
    obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioc a b))
      (F := fun z t => κ t * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (F' := fun z t => κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (bound := fun _ => B * Real.pi * M * Real.exp (Real.pi * (|z.re| + 1) * M))
      (x₀ := z) (s := Metric.ball z 1)
      (Metric.ball_mem_nhds z one_pos)
      (Filter.Eventually.of_forall (fun w => hmeas.mul (hcont_exp w)))
      h_int hF'_meas h_bound (integrable_const _) h_diff
    have hfun : (fun n : ℂ => ∫ s, κ s * Complex.exp (-(Real.pi * n * (s:ℂ)))
          ∂(volume.restrict (Set.Ioc a b)))
        = fun n : ℂ => ∫ t in a..b, κ t * Complex.exp (-(Real.pi * n * (t:ℂ))) :=
      funext (fun n => (hconv _).symm)
    rw [hfun] at hderiv
    exact hderiv.differentiableAt
  have hcdR : ContDiff ℝ ⊤ (fun z : ℂ => ∫ t in a..b, κ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) :=
    ((hdiff.differentiableOn.analyticOnNhd isOpen_univ).contDiff).restrict_scalars ℝ
  have hsq : ContDiff ℝ ⊤ (fun r : ℝ => ((r:ℂ))^2) := Complex.ofRealCLM.contDiff.pow 2
  exact hcdR.comp hsq

/-! ## The window piece `[1, Im τ - 1]` -/

/-- **The `[1, Im τ - 1]` window piece of the CKMRV `trunc` layer on the funnel.** -/
theorem truncWindowPiece (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hwin : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
    (k l : ℕ) :
    ∃ c N : ℝ, 0 ≤ c ∧
      (∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.sinSq s *
          ∫ t in (1:ℝ)..(τ.im - 1),
            (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
              * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))) ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s *
          ∫ t in (1:ℝ)..(τ.im - 1),
            (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
              * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))) r‖
          ≤ c * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨C, N, M, hC, hN, hM, hw⟩ := hwin
  obtain ⟨c₀, hc₀, H⟩ := Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound k l
  refine ⟨c₀ * (C * Real.pi ^ l), N + M + (l : ℝ) + 1, by positivity, ?_, ?_⟩
  · intro τ hτ h2
    have hY : (1:ℝ) ≤ τ.im - 1 := by linarith
    have hSpos : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
    set A : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t with hAdef
    have hmeasA : AEStronglyMeasurable A (volume.restrict (Set.Ioc (1:ℝ) (τ.im - 1))) := by
      rw [hAdef]
      exact ((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
        (by unfold Work.Asymptotics.Aexp; fun_prop)).aestronglyMeasurable
    have hB0 : 0 ≤ C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M :=
      mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hSpos.le N))
        (Real.rpow_nonneg (by linarith) M)
    have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1:ℝ) (τ.im - 1))),
        ‖A t‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [hAdef]
      have ht1 : (1:ℝ) ≤ t := le_of_lt ht.1
      have ht2 : t ≤ τ.im - 1 := ht.2
      have h1 := hw τ t hτ h2 ht1 ht2
      refine h1.trans ?_
      have hle : 1 + t ≤ 1 + (τ.im - 1) := by linarith
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith) hle hM)
        (mul_nonneg hC.le (Real.rpow_nonneg hSpos.le N))
    have hcd := laplace_interval_contDiff_omega (κ := A) hY hB0 hmeasA hbdd
    simpa [hAdef] using Work.Asymptotics.contDiff_omega_sinSq.mul hcd
  · intro τ r hτ h2
    have hY : (1:ℝ) ≤ τ.im - 1 := by linarith
    have hSpos : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
    have hS1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hYim : τ.im ≤ Work.Kernels.scale τ := im_le_scale τ
    set A : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t with hAdef
    set F : ℝ → ℂ := fun x => ∫ t in (1:ℝ)..(τ.im - 1),
      A t * (Real.exp (-(Real.pi * x * t)) : ℂ) with hFdef
    have hmeasA : AEStronglyMeasurable A (volume.restrict (Set.Ioc (1:ℝ) (τ.im - 1))) := by
      rw [hAdef]
      exact ((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
        (by unfold Work.Asymptotics.Aexp; fun_prop)).aestronglyMeasurable
    have hB0 : 0 ≤ C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M :=
      mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hSpos.le N))
        (Real.rpow_nonneg (by linarith) M)
    have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1:ℝ) (τ.im - 1))),
        ‖A t‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [hAdef]
      have ht1 : (1:ℝ) ≤ t := le_of_lt ht.1
      have ht2 : t ≤ τ.im - 1 := ht.2
      have h1 := hw τ t hτ h2 ht1 ht2
      refine h1.trans ?_
      have hle : 1 + t ≤ 1 + (τ.im - 1) := by linarith
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith) hle hM)
        (mul_nonneg hC.le (Real.rpow_nonneg hSpos.le N))
    have hcdF : ContDiffOn ℝ (l : WithTop ℕ∞) F (Set.Ioi (-1)) := by
      rw [hFdef]
      exact Work.Asymptotics.contDiffOn_intervalIntegral_exp_bound A 1 (τ.im - 1) hY hmeasA hB0 hbdd l
    have hderiv : ∀ m : ℕ, m ≤ l → ∀ x : ℝ, 0 ≤ x →
        ‖iteratedDeriv m F x‖
          ≤ (C * Real.pi ^ l * (Work.Kernels.scale τ) ^ (N + M + (l : ℝ) + 1))
              * Real.exp (-(Real.pi * x)) := by
      intro m hm x hx
      rw [hFdef, Work.Asymptotics.iteratedDeriv_intervalIntegral_exp_bound A 1 (τ.im - 1)
        hY hmeasA hB0 hbdd m x]
      have hpt : ∀ y ∈ Set.uIoc (1:ℝ) (τ.im - 1),
          ‖A y * (((-(Real.pi * y) : ℝ)) : ℂ) ^ m * (Real.exp (-(Real.pi * x * y)) : ℂ)‖
            ≤ (C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M) * (Real.pi * (τ.im - 1)) ^ m
                * Real.exp (-(Real.pi * x)) := by
        intro y hy
        have hy1 : 1 ≤ y := by
          rw [Set.uIoc_of_le hY] at hy; exact le_of_lt hy.1
        have hy2 : y ≤ τ.im - 1 := by
          rw [Set.uIoc_of_le hY] at hy; exact hy.2
        have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
        have hAy : ‖A y‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M := by
          have h1 := hw τ y hτ h2 hy1 hy2
          rw [hAdef]
          refine h1.trans ?_
          have hle : 1 + y ≤ 1 + (τ.im - 1) := by linarith
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by linarith) hle hM)
            (mul_nonneg hC.le (Real.rpow_nonneg hSpos.le N))
        rw [norm_mul, norm_mul]
        have hfac : ‖((( -(Real.pi * y)) : ℝ) : ℂ) ^ m‖ = (Real.pi * y) ^ m := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
            abs_of_pos Real.pi_pos, abs_of_pos hy0]
        rw [hfac, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have hexpy : Real.exp (-(Real.pi * x * y)) ≤ Real.exp (-(Real.pi * x)) := by
          apply Real.exp_le_exp.mpr
          have hle : x ≤ x * y := le_mul_of_one_le_right hx hy1
          have hle2 : Real.pi * x ≤ Real.pi * x * y := by
            have h := mul_le_mul_of_nonneg_left hle Real.pi_pos.le
            simpa [mul_assoc] using h
          linarith
        have hpowy : (Real.pi * y) ^ m ≤ (Real.pi * (τ.im - 1)) ^ m :=
          pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos, hy2]) m
        have hbase : 0 ≤ C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M := by positivity
        have hstep : ‖A y‖ * (Real.pi * y) ^ m ≤
            (C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M) * (Real.pi * (τ.im - 1)) ^ m :=
          mul_le_mul hAy hpowy (by positivity) hbase
        calc ‖A y‖ * (Real.pi * y) ^ m * Real.exp (-(Real.pi * x * y))
            ≤ ((C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M)
                * (Real.pi * (τ.im - 1)) ^ m) * Real.exp (-(Real.pi * x)) :=
              mul_le_mul hstep hexpy (Real.exp_nonneg _) (by positivity)
          _ = (C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M)
                * (Real.pi * (τ.im - 1)) ^ m * Real.exp (-(Real.pi * x)) := by ring
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      refine hnorm.trans ?_
      have hlen : |(τ.im - 1) - 1| = τ.im - 2 := by rw [abs_of_nonneg (by linarith)]; ring
      have hC0 : 0 ≤ C := hC.le
      have he : 0 < Real.exp (-(Real.pi * x)) := Real.exp_pos _
      have hτm : (τ.im - 1) ^ m ≤ (Work.Kernels.scale τ) ^ m :=
        pow_le_pow_left₀ (by linarith) (by linarith [hYim]) m
      have hτl : (Work.Kernels.scale τ) ^ m ≤ (Work.Kernels.scale τ) ^ l :=
        pow_le_pow_right₀ hS1 hm
      have hτM : (1 + (τ.im - 1)) ^ M ≤ (Work.Kernels.scale τ) ^ M := by
        have : (1 + (τ.im - 1)) = τ.im := by ring
        rw [this]
        exact Real.rpow_le_rpow (by linarith) hYim hM
      have hpil : Real.pi ^ m ≤ Real.pi ^ l :=
        pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hm
      have hτ2 : τ.im - 2 ≤ Work.Kernels.scale τ := by linarith
      have hprod : (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M
            * (Real.pi * (τ.im - 1)) ^ m * (τ.im - 2)
          ≤ Real.pi ^ l * (Work.Kernels.scale τ) ^ (N + M + (l : ℝ) + 1) := by
        have hA : (1 + (τ.im - 1)) ^ M ≤ (Work.Kernels.scale τ) ^ M := by
          have heq : (1 + (τ.im - 1)) = τ.im := by ring
          rw [heq]
          exact Real.rpow_le_rpow (by linarith) hYim hM
        have hB : (Real.pi * (τ.im - 1)) ^ m
            ≤ Real.pi ^ l * (Work.Kernels.scale τ) ^ (m : ℝ) := by
          rw [mul_pow]
          have h1 : (τ.im - 1) ^ m ≤ (Work.Kernels.scale τ) ^ (m : ℝ) := by
            rw [Real.rpow_natCast]
            exact pow_le_pow_left₀ (by linarith) (by linarith [hYim]) m
          exact mul_le_mul hpil h1 (by positivity) (by positivity)
        have hC2 : τ.im - 2 ≤ (Work.Kernels.scale τ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]; linarith
        have hstep1 : (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M
              * (Real.pi * (τ.im - 1)) ^ m * (τ.im - 2)
            ≤ (Work.Kernels.scale τ) ^ N * (Work.Kernels.scale τ) ^ M
              * (Real.pi ^ l * (Work.Kernels.scale τ) ^ (m : ℝ)) * (Work.Kernels.scale τ) ^ (1 : ℝ) := by
          gcongr
        have hstep2 : (Work.Kernels.scale τ) ^ N * (Work.Kernels.scale τ) ^ M
              * (Real.pi ^ l * (Work.Kernels.scale τ) ^ (m : ℝ)) * (Work.Kernels.scale τ) ^ (1 : ℝ)
            = Real.pi ^ l * (Work.Kernels.scale τ) ^ (N + M + (m : ℝ) + 1) := by
          rw [show (Work.Kernels.scale τ) ^ N * (Work.Kernels.scale τ) ^ M
                * (Real.pi ^ l * (Work.Kernels.scale τ) ^ (m : ℝ)) * (Work.Kernels.scale τ) ^ (1 : ℝ)
              = Real.pi ^ l * ((Work.Kernels.scale τ) ^ N * (Work.Kernels.scale τ) ^ M
                * (Work.Kernels.scale τ) ^ (m : ℝ) * (Work.Kernels.scale τ) ^ (1 : ℝ)) from by ring]
          rw [← Real.rpow_add hSpos N M, ← Real.rpow_add hSpos (N + M) (m : ℝ),
            ← Real.rpow_add hSpos (N + M + (m : ℝ)) 1]
        have hstep3 : Real.pi ^ l * (Work.Kernels.scale τ) ^ (N + M + (m : ℝ) + 1)
            ≤ Real.pi ^ l * (Work.Kernels.scale τ) ^ (N + M + (l : ℝ) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          apply Real.rpow_le_rpow_of_exponent_le hS1
          have : (m : ℝ) ≤ (l : ℝ) := by exact_mod_cast hm
          linarith
        exact hstep1.trans (hstep2.trans_le hstep3)
      have hgoal : (C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M)
            * (Real.pi * (τ.im - 1)) ^ m * Real.exp (-(Real.pi * x)) * (τ.im - 2)
          ≤ (C * Real.pi ^ l * (Work.Kernels.scale τ) ^ (N + M + (l : ℝ) + 1))
              * Real.exp (-(Real.pi * x)) := by
        have := mul_le_mul_of_nonneg_right hprod he.le
        calc (C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M)
              * (Real.pi * (τ.im - 1)) ^ m * Real.exp (-(Real.pi * x)) * (τ.im - 2)
            = C * ((Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M
                * (Real.pi * (τ.im - 1)) ^ m * (τ.im - 2)) * Real.exp (-(Real.pi * x)) := by ring
          _ ≤ C * (Real.pi ^ l * (Work.Kernels.scale τ) ^ (N + M + (l : ℝ) + 1))
                * Real.exp (-(Real.pi * x)) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hC0) he.le
          _ = (C * Real.pi ^ l * (Work.Kernels.scale τ) ^ (N + M + (l : ℝ) + 1))
                * Real.exp (-(Real.pi * x)) := by ring
      calc (C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M) * (Real.pi * (τ.im - 1)) ^ m
            * Real.exp (-(Real.pi * x)) * |(τ.im - 1) - 1|
          = (C * (Work.Kernels.scale τ) ^ N * (1 + (τ.im - 1)) ^ M)
            * (Real.pi * (τ.im - 1)) ^ m * Real.exp (-(Real.pi * x)) * (τ.im - 2) := by rw [hlen]
        _ ≤ _ := hgoal
    have hfun : (fun s : ℝ => Work.Asymptotics.sinSq s * ∫ t in (1:ℝ)..(τ.im - 1),
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
            * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))
        = fun s : ℝ => (2 - 2 * ((Real.cos (Real.pi * s ^ 2)) : ℂ)) * F (s ^ 2) := by
      funext s
      rw [Work.Asymptotics.sinSq_eq, hFdef]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      simp only [hAdef, truncExp_eq]
    rw [hfun]
    have := H F (C * Real.pi ^ l * (Work.Kernels.scale τ) ^ (N + M + (l : ℝ) + 1))
      (by positivity) hcdF hderiv r
    refine this.trans (le_of_eq ?_)
    ring

/-! ## The `𝒢`-correction on the middle window `[Im τ - 1, Im τ + 1]` -/

/-- **`Aexp (Gcusp ℓ d)` is polynomially bounded on the middle window.**
On `[Im τ - 1, Im τ + 1]` (with `Im τ ≥ 2`) the `i = 0` row is `O((scale τ)^N)` by moderate growth
(`GcuspInP`), while the `i = 1` row carries the factor `e^{2π t} ≤ e^{2π(Im τ + 1)}` which is
beaten by the exponential smallness `hG1`. -/
lemma aexp_mid_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (_hd : d = 8 ∨ d = 24)
    (hG1 : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (j : Fin 2),
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
      ‖Work.Asymptotics.Gcusp ℓ d 1 j τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      Work.Asymptotics.Funnel τ → τ.im - 1 ≤ t → t ≤ τ.im + 1 →
        ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨Cg, Ng, hCg, hNg, hG⟩ := hG1
  obtain ⟨a₀, N₀, ha₀, hN₀, hG00⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale _ _).mp (Work.Asymptotics.GcuspInP ℓ d 0 0)
  obtain ⟨a₁, N₁, ha₁, hN₁, hG01⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale _ _).mp (Work.Asymptotics.GcuspInP ℓ d 0 1)
  refine ⟨a₀ + 2 * a₁ + 3 * Real.exp (2 * Real.pi) * Cg,
    max (max N₀ N₁) Ng + 1, by positivity, by positivity, ?_⟩
  intro τ t hτ ht1 ht2
  have hD : τ ∈ Work.Asymptotics.DomainD := hτ.1
  have h2 : 2 ≤ τ.im := hτ.2
  have hS1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hSpos : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hYim : τ.im ≤ Work.Kernels.scale τ := im_le_scale τ
  have hY2 : τ.im + 1 ≤ 2 * Work.Kernels.scale τ := by linarith
  have htpos : 0 < t := by linarith
  have hle₁ : N₀ ≤ max (max N₀ N₁) Ng + 1 := by
    have : N₀ ≤ max (max N₀ N₁) Ng := le_trans (le_max_left N₀ N₁) (le_max_left _ _)
    linarith
  have hle₂ : N₁ + 1 ≤ max (max N₀ N₁) Ng + 1 := by
    have : N₁ ≤ max (max N₀ N₁) Ng := le_trans (le_max_right N₀ N₁) (le_max_left _ _)
    linarith
  have hle₃ : Ng + 1 ≤ max (max N₀ N₁) Ng + 1 := by
    have : Ng ≤ max (max N₀ N₁) Ng := le_max_right _ _
    linarith
  have hS0 : (0:ℝ) < Work.Kernels.scale τ := hSpos
  have htC : ‖((t : ℂ) * Complex.I)‖ = t := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos]
  have hexp1 : ‖Complex.exp (2 * (Real.pi : ℂ) * (t : ℂ))‖ = Real.exp (2 * Real.pi * t) := by
    rw [show 2 * (Real.pi : ℂ) * (t : ℂ) = (((2 * Real.pi * t : ℝ)) : ℂ) from by push_cast; ring,
      Complex.norm_exp, Complex.ofReal_re]
  have hG00b : ‖Work.Asymptotics.Gcusp ℓ d 0 0 τ‖ ≤ a₀ * (Work.Kernels.scale τ) ^ N₀ :=
    hG00 τ hD
  have hG01b : ‖Work.Asymptotics.Gcusp ℓ d 0 1 τ‖ ≤ a₁ * (Work.Kernels.scale τ) ^ N₁ :=
    hG01 τ hD
  have hG10b : ‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖
      ≤ Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im)) := hG τ 0 hD h2
  have hG11b : ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖
      ≤ Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im)) := hG τ 1 hD h2
  have hexpsmall : Real.exp (2 * Real.pi * t) * Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (2 * Real.pi) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, ht2]
  have hmain : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
      ≤ a₀ * (Work.Kernels.scale τ) ^ N₀ + t * (a₁ * (Work.Kernels.scale τ) ^ N₁)
        + Real.exp (2 * Real.pi * t)
          * ((Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im)))
            + t * (Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im)))) := by
    rw [Work.Asymptotics.Aexp]
    refine le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _) ?_) ?_)
    · refine add_le_add hG00b ?_
      rw [norm_mul, htC]
      exact mul_le_mul_of_nonneg_left hG01b htpos.le
    · rw [norm_mul, hexp1]
      refine mul_le_mul_of_nonneg_left (le_trans (norm_add_le _ _) ?_) (Real.exp_pos _).le
      refine add_le_add hG10b ?_
      rw [norm_mul, htC]
      exact mul_le_mul_of_nonneg_left hG11b htpos.le
  refine hmain.trans ?_
  have hS0' : (0:ℝ) ≤ Work.Kernels.scale τ := hSpos.le
  have he2pi : (0:ℝ) < Real.exp (2 * Real.pi) := Real.exp_pos _
  have hCg0 : 0 ≤ Cg := hCg.le
  have hstep : t * (a₁ * (Work.Kernels.scale τ) ^ N₁) ≤ 2 * a₁ * (Work.Kernels.scale τ) ^ (N₁ + 1) := by
    have htS : t ≤ 2 * Work.Kernels.scale τ := by linarith
    calc t * (a₁ * (Work.Kernels.scale τ) ^ N₁)
        ≤ (2 * Work.Kernels.scale τ) * (a₁ * (Work.Kernels.scale τ) ^ N₁) := by
          gcongr
      _ = 2 * a₁ * (Work.Kernels.scale τ) ^ (N₁ + 1) := by
          rw [Real.rpow_add hSpos, Real.rpow_one]; ring
  have hstep2 : Real.exp (2 * Real.pi * t)
        * ((Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im)))
          + t * (Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im))))
      ≤ 3 * Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ (Ng + 1) := by
    have htS : t ≤ 2 * Work.Kernels.scale τ := by linarith
    have hb1 : Real.exp (2 * Real.pi * t) * (Cg * (Work.Kernels.scale τ) ^ Ng
        * Real.exp (-(2 * Real.pi * τ.im))) ≤ Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ Ng := by
      calc Real.exp (2 * Real.pi * t) * (Cg * (Work.Kernels.scale τ) ^ Ng
            * Real.exp (-(2 * Real.pi * τ.im)))
          = (Real.exp (2 * Real.pi * t) * Real.exp (-(2 * Real.pi * τ.im)))
              * (Cg * (Work.Kernels.scale τ) ^ Ng) := by ring
        _ ≤ Real.exp (2 * Real.pi) * (Cg * (Work.Kernels.scale τ) ^ Ng) :=
            mul_le_mul_of_nonneg_right hexpsmall (by positivity)
        _ = Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ Ng := by ring
    have hb2 : Real.exp (2 * Real.pi * t) * (t * (Cg * (Work.Kernels.scale τ) ^ Ng
        * Real.exp (-(2 * Real.pi * τ.im))))
        ≤ 2 * Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ (Ng + 1) := by
      have h1 : Real.exp (2 * Real.pi * t) * (Cg * (Work.Kernels.scale τ) ^ Ng
          * Real.exp (-(2 * Real.pi * τ.im))) ≤ Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ Ng := hb1
      calc Real.exp (2 * Real.pi * t) * (t * (Cg * (Work.Kernels.scale τ) ^ Ng
            * Real.exp (-(2 * Real.pi * τ.im))))
          = t * (Real.exp (2 * Real.pi * t) * (Cg * (Work.Kernels.scale τ) ^ Ng
              * Real.exp (-(2 * Real.pi * τ.im)))) := by ring
        _ ≤ (2 * Work.Kernels.scale τ) * (Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ Ng) :=
            mul_le_mul htS h1 (by positivity) (by positivity)
        _ = 2 * Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ (Ng + 1) := by
            rw [Real.rpow_add hSpos, Real.rpow_one]; ring
    calc Real.exp (2 * Real.pi * t)
          * ((Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im)))
            + t * (Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im))))
        = Real.exp (2 * Real.pi * t) * (Cg * (Work.Kernels.scale τ) ^ Ng
            * Real.exp (-(2 * Real.pi * τ.im)))
          + Real.exp (2 * Real.pi * t) * (t * (Cg * (Work.Kernels.scale τ) ^ Ng
            * Real.exp (-(2 * Real.pi * τ.im)))) := by ring
      _ ≤ Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ Ng
          + 2 * Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ (Ng + 1) := add_le_add hb1 hb2
      _ ≤ 3 * Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ (Ng + 1) := by
          have hSNg : (Work.Kernels.scale τ) ^ Ng ≤ (Work.Kernels.scale τ) ^ (Ng + 1) := by
            have h : (Work.Kernels.scale τ) ^ Ng * Work.Kernels.scale τ
                = (Work.Kernels.scale τ) ^ (Ng + 1) := by
              rw [Real.rpow_add hSpos, Real.rpow_one]
            rw [← h]
            nlinarith [Real.rpow_nonneg hSpos.le Ng, hS1, he2pi, hCg0]
          calc Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ Ng
              + 2 * Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ (Ng + 1)
              ≤ Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ (Ng + 1)
                + 2 * Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ (Ng + 1) := by
                gcongr
            _ = 3 * Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ (Ng + 1) := by ring
  have hsum : a₀ * (Work.Kernels.scale τ) ^ N₀ + t * (a₁ * (Work.Kernels.scale τ) ^ N₁)
        + Real.exp (2 * Real.pi * t)
          * ((Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im)))
            + t * (Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im))))
      ≤ (a₀ + 2 * a₁ + 3 * Real.exp (2 * Real.pi) * Cg) * (Work.Kernels.scale τ) ^ (max (max N₀ N₁) Ng + 1) := by
    have hSN : ∀ (c : ℝ) (n : ℝ), 0 ≤ c → n ≤ max (max N₀ N₁) Ng + 1 →
        c * (Work.Kernels.scale τ) ^ n ≤ c * (Work.Kernels.scale τ) ^ (max (max N₀ N₁) Ng + 1) := by
      intro c n hc hn
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hS1 hn) hc
    have h1 := hSN a₀ N₀ ha₀ hle₁
    have h2 := hSN (2 * a₁) (N₁ + 1) (by positivity) hle₂
    have h3 := hSN (3 * Real.exp (2 * Real.pi) * Cg) (Ng + 1) (by positivity) hle₃
    have hassoc : a₀ * (Work.Kernels.scale τ) ^ N₀ + t * (a₁ * (Work.Kernels.scale τ) ^ N₁)
          + Real.exp (2 * Real.pi * t)
            * ((Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im)))
              + t * (Cg * (Work.Kernels.scale τ) ^ Ng * Real.exp (-(2 * Real.pi * τ.im))))
        ≤ a₀ * (Work.Kernels.scale τ) ^ N₀ + 2 * a₁ * (Work.Kernels.scale τ) ^ (N₁ + 1)
          + 3 * Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ (Ng + 1) := by
      linarith [hstep, hstep2]
    have h4 : a₀ * (Work.Kernels.scale τ) ^ N₀ + 2 * a₁ * (Work.Kernels.scale τ) ^ (N₁ + 1)
          + 3 * Real.exp (2 * Real.pi) * Cg * (Work.Kernels.scale τ) ^ (Ng + 1)
        ≤ (a₀ + 2 * a₁ + 3 * Real.exp (2 * Real.pi) * Cg) * (Work.Kernels.scale τ) ^ (max (max N₀ N₁) Ng + 1) := by
      linarith [h1, h2, h3]
    linarith [hassoc, h4]
  exact hsum

/-- **The `𝒢`-correction on the middle window `[Im τ - 1, Im τ + 1]`.** -/
theorem truncAexpMidPiece (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hG1 : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (j : Fin 2),
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
      ‖Work.Asymptotics.Gcusp ℓ d 1 j τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)))
    (k l : ℕ) :
    ∃ c N : ℝ, 0 ≤ c ∧
      (∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
        ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.sinSq s *
          ∫ t in (τ.im - 1)..(τ.im + 1),
            Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
              * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))) ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), Work.Asymptotics.Funnel τ →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.sinSq s *
          ∫ t in (τ.im - 1)..(τ.im + 1),
            Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
              * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))) r‖
          ≤ c * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := aexp_mid_bound ℓ d hd hG1
  obtain ⟨c₀, hc₀, H⟩ := Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound k l
  refine ⟨c₀ * (2 * C * (2 * Real.pi) ^ l), (l : ℝ) + N, by positivity, ?_, ?_⟩
  · intro τ hτ
    have hab : τ.im - 1 ≤ τ.im + 1 := by linarith
    have hSpos : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
    have hcont : Continuous (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) := by
      unfold Work.Asymptotics.Aexp; fun_prop
    have hB0 : 0 ≤ C * (Work.Kernels.scale τ) ^ N :=
      mul_nonneg hC (Real.rpow_nonneg hSpos.le N)
    have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (τ.im - 1) (τ.im + 1))),
        ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      exact hb τ t hτ (le_of_lt ht.1) ht.2
    have hcd := laplace_interval_contDiff_omega
      (κ := fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) hab hB0
      hcont.aestronglyMeasurable hbdd
    exact Work.Asymptotics.contDiff_omega_sinSq.mul hcd
  · intro τ r hτ
    have hD : τ ∈ Work.Asymptotics.DomainD := hτ.1
    have h2 : 2 ≤ τ.im := hτ.2
    have hab : τ.im - 1 ≤ τ.im + 1 := by linarith
    have hSpos : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
    have hS1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hY2 : τ.im + 1 ≤ 2 * Work.Kernels.scale τ := by
      have := im_le_scale τ; linarith
    set A : ℝ → ℂ := fun t => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t with hAdef
    have hcont : Continuous (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) := by
      unfold Work.Asymptotics.Aexp; fun_prop
    have hmeas : AEStronglyMeasurable A (volume.restrict (Set.Ioc (τ.im - 1) (τ.im + 1))) := by
      rw [hAdef]; exact hcont.aestronglyMeasurable
    have hB0 : 0 ≤ C * (Work.Kernels.scale τ) ^ N :=
      mul_nonneg hC (Real.rpow_nonneg hSpos.le N)
    have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (τ.im - 1) (τ.im + 1))), ‖A t‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [hAdef]
      exact hb τ t hτ (le_of_lt ht.1) ht.2
    set F : ℝ → ℂ := fun x => ∫ t in (τ.im - 1)..(τ.im + 1),
      A t * (Real.exp (-(Real.pi * x * t)) : ℂ) with hFdef
    have hcdF : ContDiffOn ℝ (l : WithTop ℕ∞) F (Set.Ioi (-1)) := by
      rw [hFdef]
      exact Work.Asymptotics.contDiffOn_intervalIntegral_exp_bound A (τ.im - 1) (τ.im + 1) hab
        hmeas hB0 hbdd l
    have hderiv : ∀ m : ℕ, m ≤ l → ∀ x : ℝ, 0 ≤ x →
        ‖iteratedDeriv m F x‖
          ≤ (2 * C * (2 * Real.pi) ^ l * (Work.Kernels.scale τ) ^ ((l : ℝ) + N))
              * Real.exp (-(Real.pi * x)) := by
      intro m hm x hx
      rw [hFdef, Work.Asymptotics.iteratedDeriv_intervalIntegral_exp_bound A (τ.im - 1) (τ.im + 1)
        hab hmeas hB0 hbdd m x]
      have hpt : ∀ y ∈ Set.uIoc (τ.im - 1) (τ.im + 1),
          ‖A y * (((-(Real.pi * y) : ℝ)) : ℂ) ^ m * (Real.exp (-(Real.pi * x * y)) : ℂ)‖
            ≤ (C * (Work.Kernels.scale τ) ^ N) * (Real.pi * (τ.im + 1)) ^ m
                * Real.exp (-(Real.pi * x)) := by
        intro y hy
        have hy1 : τ.im - 1 ≤ y := by
          rw [Set.uIoc_of_le hab] at hy; exact le_of_lt hy.1
        have hy2 : y ≤ τ.im + 1 := by
          rw [Set.uIoc_of_le hab] at hy; exact hy.2
        have hy0 : 0 < y := by linarith
        have hAy : ‖A y‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
          rw [hAdef]
          exact hb τ y hτ hy1 hy2
        rw [norm_mul, norm_mul]
        have hfac : ‖((( -(Real.pi * y)) : ℝ) : ℂ) ^ m‖ = (Real.pi * y) ^ m := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
            abs_of_pos Real.pi_pos, abs_of_pos hy0]
        rw [hfac, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have hexpy : Real.exp (-(Real.pi * x * y)) ≤ Real.exp (-(Real.pi * x)) := by
          apply Real.exp_le_exp.mpr
          have hle : x ≤ x * y := le_mul_of_one_le_right hx (by linarith)
          have hle2 : Real.pi * x ≤ Real.pi * x * y := by
            have h := mul_le_mul_of_nonneg_left hle Real.pi_pos.le
            simpa [mul_assoc] using h
          linarith
        have hpowy : (Real.pi * y) ^ m ≤ (Real.pi * (τ.im + 1)) ^ m :=
          pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos, hy2]) m
        have hbase : 0 ≤ C * (Work.Kernels.scale τ) ^ N := by positivity
        have hstep : ‖A y‖ * (Real.pi * y) ^ m
            ≤ (C * (Work.Kernels.scale τ) ^ N) * (Real.pi * (τ.im + 1)) ^ m :=
          mul_le_mul hAy hpowy (by positivity) hbase
        calc ‖A y‖ * (Real.pi * y) ^ m * Real.exp (-(Real.pi * x * y))
            ≤ ((C * (Work.Kernels.scale τ) ^ N) * (Real.pi * (τ.im + 1)) ^ m)
                * Real.exp (-(Real.pi * x)) :=
              mul_le_mul hstep hexpy (Real.exp_nonneg _) (by positivity)
          _ = (C * (Work.Kernels.scale τ) ^ N) * (Real.pi * (τ.im + 1)) ^ m
                * Real.exp (-(Real.pi * x)) := by ring
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      refine hnorm.trans ?_
      have hlen : |τ.im + 1 - (τ.im - 1)| = 2 := by
        rw [abs_of_nonneg (by linarith)]; ring
      rw [hlen]
      have hq : (Real.pi * (τ.im + 1)) ^ m ≤ (2 * Real.pi) ^ l * (Work.Kernels.scale τ) ^ l := by
        have h1 : Real.pi * (τ.im + 1) ≤ 2 * Real.pi * Work.Kernels.scale τ := by
          nlinarith [Real.pi_pos, hY2]
        have h3 : (Real.pi * (τ.im + 1)) ^ m ≤ (2 * Real.pi * Work.Kernels.scale τ) ^ m :=
          pow_le_pow_left₀ (by positivity) h1 m
        calc (Real.pi * (τ.im + 1)) ^ m ≤ (2 * Real.pi * Work.Kernels.scale τ) ^ m := h3
          _ = (2 * Real.pi) ^ m * (Work.Kernels.scale τ) ^ m := by rw [mul_pow]
          _ ≤ (2 * Real.pi) ^ l * (Work.Kernels.scale τ) ^ l :=
              mul_le_mul (pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hm)
                (pow_le_pow_right₀ hS1 hm) (by positivity) (by positivity)
      calc (C * (Work.Kernels.scale τ) ^ N) * (Real.pi * (τ.im + 1)) ^ m
            * Real.exp (-(Real.pi * x)) * 2
          = 2 * C * ((Real.pi * (τ.im + 1)) ^ m * Real.exp (-(Real.pi * x)))
              * (Work.Kernels.scale τ) ^ N := by ring
        _ ≤ 2 * C * (((2 * Real.pi) ^ l * (Work.Kernels.scale τ) ^ l) * Real.exp (-(Real.pi * x)))
              * (Work.Kernels.scale τ) ^ N := by
            gcongr
        _ = (2 * C * (2 * Real.pi) ^ l * (Work.Kernels.scale τ) ^ ((l : ℝ) + N))
              * Real.exp (-(Real.pi * x)) := by
            rw [show 2 * C * ((2 * Real.pi) ^ l * (Work.Kernels.scale τ) ^ l
                    * Real.exp (-(Real.pi * x))) * (Work.Kernels.scale τ) ^ N
                  = 2 * C * (2 * Real.pi) ^ l
                    * ((Work.Kernels.scale τ) ^ l * (Work.Kernels.scale τ) ^ N)
                    * Real.exp (-(Real.pi * x)) from by ring]
            rw [show (Work.Kernels.scale τ) ^ l * (Work.Kernels.scale τ) ^ N
                  = (Work.Kernels.scale τ) ^ ((l : ℝ) + N) from by
                rw [← Real.rpow_natCast (Work.Kernels.scale τ) l,
                  ← Real.rpow_add hSpos (l : ℝ) N]]
    have hfun : (fun s : ℝ => Work.Asymptotics.sinSq s * ∫ t in (τ.im - 1)..(τ.im + 1),
          Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
            * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))
        = fun s : ℝ => (2 - 2 * ((Real.cos (Real.pi * s ^ 2)) : ℂ)) * F (s ^ 2) := by
      funext s
      rw [Work.Asymptotics.sinSq_eq, hFdef]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      simp only [hAdef, truncExp_eq]
    rw [hfun]
    have := H F (2 * C * (2 * Real.pi) ^ l * (Work.Kernels.scale τ) ^ ((l : ℝ) + N))
      (by positivity) hcdF hderiv r
    refine this.trans (le_of_eq ?_)
    ring

/-! ## The splitting of `layerTrunc` into its three contour pieces -/

/-- **The splitting of the `trunc` layer into the three pieces of the funnel decomposition.**
`∫_1^∞ = ∫_1^{Im τ - 1} + ∫_{Im τ - 1}^{Im τ + 1} + ∫_{Im τ + 1}^∞`, and on the middle window
the kernel loses its `𝒢`-part: the identity is
`∫_1^∞ (K - 𝒢)e^{-πr²t} = ∫_1^{Im τ-1}(K-𝒢)e^{-πr²t} + spikeT(r²) - ∫_{Im τ-1}^{Im τ+1}𝒢 e^{-πr²t} + tailT(r²)`.
The splitting of the (improper) integral is justified by the three bounds: `hwin` below the pole,
`spikeWindow_bound` on the spike, and the exponential decay `funnelKernelTailGcusp` above it. -/
theorem layerTruncPieces (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hwin : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
    (τ : UpperHalfPlane) (hτ : τ ∈ Work.Asymptotics.DomainD) (h2 : 2 ≤ τ.im) :
    (fun r : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
      = fun r : ℝ =>
          Work.Asymptotics.sinSq r * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
          + Work.Asymptotics.sinSq r * Work.Asymptotics.spikeT ℓ d τ (r^2)
          - Work.Asymptotics.sinSq r * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
          + Work.Asymptotics.sinSq r * Work.Asymptotics.tailT ℓ d τ (r^2) := by
  obtain ⟨Cw, Nw, Mw, hCw, hNw, hMw, hw⟩ := hwin
  obtain ⟨Bk, hBk0, hBk⟩ := Work.Asymptotics.spikeWindow_bound ℓ d hd τ ⟨hτ, h2⟩
  obtain ⟨Ct, Nt, Mt, hCt, hNt, hMt, htl⟩ := Work.Asymptotics.funnelKernelTailGcusp ℓ d hd
  have hSpos : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hY : (1:ℝ) ≤ τ.im - 1 := by linarith
  have hY1 : τ.im - 1 ≤ τ.im + 1 := by linarith
  set BA : ℝ := ‖Work.Asymptotics.Gcusp ℓ d 0 0 τ‖ + (τ.im + 1) * ‖Work.Asymptotics.Gcusp ℓ d 0 1 τ‖
      + Real.exp (2 * Real.pi * (τ.im + 1))
        * (‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖ + (τ.im + 1) * ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖)
    with hBAdef
  have hBA0 : 0 ≤ BA := by rw [hBAdef]; positivity
  have hBA : ∀ t ∈ Set.Ioc (τ.im - 1) (τ.im + 1), ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ BA := by
    intro t ht
    have ht0 : 0 < t := by have := ht.1; linarith
    have htle : t ≤ τ.im + 1 := ht.2
    have h1 : ‖((t : ℂ) * Complex.I)‖ = t := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hexp : ‖Complex.exp (2 * (Real.pi : ℂ) * (t : ℂ))‖ = Real.exp (2 * Real.pi * t) := by
      rw [show 2 * (Real.pi : ℂ) * (t : ℂ) = (((2 * Real.pi * t : ℝ)) : ℂ) from by push_cast; ring,
        Complex.norm_exp, Complex.ofReal_re]
    rw [Work.Asymptotics.Aexp]
    have h3 := norm_add_le (Work.Asymptotics.Gcusp ℓ d 0 0 τ
        + (t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 0 1 τ)
      (Complex.exp (2 * (Real.pi : ℂ) * (t : ℂ))
        * (Work.Asymptotics.Gcusp ℓ d 1 0 τ
          + (t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 1 1 τ))
    have h4 := norm_add_le (Work.Asymptotics.Gcusp ℓ d 0 0 τ)
      ((t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 0 1 τ)
    have h5 := norm_add_le (Work.Asymptotics.Gcusp ℓ d 1 0 τ)
      ((t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 1 1 τ)
    have hstep : ‖Work.Asymptotics.Gcusp ℓ d 0 0 τ
          + (t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 0 1 τ
          + Complex.exp (2 * (Real.pi : ℂ) * (t : ℂ))
            * (Work.Asymptotics.Gcusp ℓ d 1 0 τ
              + (t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 1 1 τ)‖
        ≤ ‖Work.Asymptotics.Gcusp ℓ d 0 0 τ‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 0 1 τ‖
          + Real.exp (2 * Real.pi * t)
            * (‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖) := by
      refine le_trans h3 (add_le_add (le_trans h4 ?_) ?_)
      · rw [norm_mul, h1]
      · rw [norm_mul, hexp]
        refine mul_le_mul_of_nonneg_left (le_trans h5 (add_le_add le_rfl ?_))
          (Real.exp_pos _).le
        rw [norm_mul, h1]
    refine hstep.trans ?_
    rw [hBAdef]
    have e1 : t * ‖Work.Asymptotics.Gcusp ℓ d 0 1 τ‖
        ≤ (τ.im + 1) * ‖Work.Asymptotics.Gcusp ℓ d 0 1 τ‖ :=
      mul_le_mul_of_nonneg_right htle (norm_nonneg _)
    have e2 : Real.exp (2 * Real.pi * t) ≤ Real.exp (2 * Real.pi * (τ.im + 1)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, htle])
    have e3 : ‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖
        ≤ ‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖ + (τ.im + 1) * ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right htle (norm_nonneg _))
    have e4 : (0:ℝ) ≤ ‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖
        + (τ.im + 1) * ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖ := by positivity
    have e5 : Real.exp (2 * Real.pi * t)
          * (‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖)
        ≤ Real.exp (2 * Real.pi * (τ.im + 1))
          * (‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖ + (τ.im + 1) * ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖) :=
      mul_le_mul e2 e3 (by positivity) (Real.exp_pos _).le
    linarith
  funext r
  have hen : ∀ t : ℝ, 0 < t → ‖Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))‖ ≤ 1 := by
    intro t ht
    rw [truncExp_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by
      have h : 0 ≤ Real.pi * r ^ 2 * t := by positivity
      linarith)
  have hmeasAmp : Measurable (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)) :=
    (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
      (by unfold Work.Asymptotics.Aexp; fun_prop)
  have hmeasK : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) := Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ
  have hmeasA : Measurable (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) := by unfold Work.Asymptotics.Aexp; fun_prop
  have hexpcont : Continuous (fun t : ℝ => Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) := by
    apply Complex.continuous_exp.comp
    fun_prop
  have hbwin : ∀ t ∈ Set.Ioc (1:ℝ) (τ.im - 1),
      ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)‖ ≤ Cw * (Work.Kernels.scale τ) ^ Nw * (1 + (τ.im - 1)) ^ Mw := by
    intro t ht
    have h1 : (1:ℝ) ≤ t := le_of_lt ht.1
    have h2' : t ≤ τ.im - 1 := ht.2
    have h3 := hw τ t hτ h2 h1 h2'
    refine h3.trans ?_
    have hle : 1 + t ≤ 1 + (τ.im - 1) := by linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hle hMw)
      (by positivity)
  have hbmid : ∀ t ∈ Set.Ioc (τ.im - 1) (τ.im + 1), ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)‖ ≤ Bk + BA := by
    intro t ht
    have h1 := hBk t (le_of_lt ht.1) ht.2
    have h2' := hBA t ht
    exact (norm_sub_le _ _).trans (add_le_add h1 h2')
  have hbtail : ∀ t ∈ Set.Ioi (τ.im + 1),
      ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)‖ ≤ Ct * (Work.Kernels.scale τ) ^ Nt * (1 + t) ^ Mt * Real.exp (-(Real.pi * (t - τ.im))) := by
    intro t ht
    exact htl τ t ⟨hτ, h2⟩ (le_of_lt ht)
  set B1 : ℝ := Cw * (Work.Kernels.scale τ) ^ Nw * (1 + (τ.im - 1)) ^ Mw + (Bk + BA) with hB1def
  have hB1a : Cw * (Work.Kernels.scale τ) ^ Nw * (1 + (τ.im - 1)) ^ Mw ≤ B1 := by
    rw [hB1def]; linarith
  have hB1b : Bk + BA ≤ B1 := by
    have hnn : 0 ≤ Cw * (Work.Kernels.scale τ) ^ Nw * (1 + (τ.im - 1)) ^ Mw :=
      mul_nonneg (mul_nonneg hCw.le (Real.rpow_nonneg hSpos.le Nw))
        (Real.rpow_nonneg (by linarith) Mw)
    rw [hB1def]; linarith
  have hIf1 : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) (Set.Ioc (1:ℝ) (τ.im - 1)) := by
    refine IntegrableOn.of_bound ?_ ?_ B1 ?_
    · exact lt_of_le_of_lt (measure_mono (Set.Ioc_subset_Icc_self)) isCompact_Icc.measure_lt_top
    · exact (hmeasAmp.mul hexpcont.measurable).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul]
      exact (mul_le_mul (hbwin t ht) (hen t (by linarith [ht.1])) (norm_nonneg _)
        (by positivity)).trans (by rw [mul_one]; exact hB1a)
  have hIf2 : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) (Set.Ioc (τ.im - 1) (τ.im + 1)) := by
    refine IntegrableOn.of_bound ?_ ?_ B1 ?_
    · exact lt_of_le_of_lt (measure_mono (Set.Ioc_subset_Icc_self)) isCompact_Icc.measure_lt_top
    · exact (hmeasAmp.mul hexpcont.measurable).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul]
      exact (mul_le_mul (hbmid t ht) (hen t (by linarith [ht.1])) (norm_nonneg _)
        (by positivity)).trans (by rw [mul_one]; exact hB1b)
  have hIf3 : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) (Set.Ioi (τ.im + 1)) := by
    have hmaj : Integrable (fun t : ℝ => Ct * (Work.Kernels.scale τ) ^ Nt * Real.exp (Real.pi * τ.im) * (2:ℝ) ^ Mt
        * (t ^ Mt * Real.exp (-(Real.pi * t)))) (volume.restrict (Set.Ioi (τ.im + 1))) := by
      have hbase := Work.Asymptotics.integrableOn_rpow_mul_exp_neg Mt Real.pi hMt Real.pi_pos
      have h1 : IntegrableOn (fun t : ℝ => t ^ Mt * Real.exp (-(Real.pi * t))) (Set.Ioi (τ.im + 1)) :=
        hbase.mono_set (fun t ht => by
          rw [Set.mem_Ici]; exact le_of_lt (by linarith [Set.mem_Ioi.mp ht]))
      have h2 := h1.const_mul (Ct * (Work.Kernels.scale τ) ^ Nt * Real.exp (Real.pi * τ.im) * (2:ℝ) ^ Mt)
      simpa only [mul_assoc] using h2
    refine Integrable.mono' hmaj (hmeasAmp.mul hexpcont.measurable).aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : τ.im + 1 ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
    have ht0 : 0 < t := by linarith
    have hψ := hbtail t (Set.mem_Ioi.mpr (Set.mem_Ioi.mp ht))
    rw [norm_mul]
    have hE := hen t ht0
    have hmono : (1 + t) ^ Mt ≤ (2:ℝ) ^ Mt * t ^ Mt := by
      have h1 : 1 + t ≤ 2 * t := by linarith
      have h2 := Real.rpow_le_rpow (by linarith) h1 hMt
      rwa [Real.mul_rpow (by norm_num) (le_of_lt ht0)] at h2
    have hexp2 : Real.exp (-(Real.pi * (t - τ.im)))
        = Real.exp (Real.pi * τ.im) * Real.exp (-(Real.pi * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)‖ * ‖Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))‖
        ≤ (Ct * (Work.Kernels.scale τ) ^ Nt * (1 + t) ^ Mt * Real.exp (-(Real.pi * (t - τ.im)))) * 1 :=
          mul_le_mul hψ hE (norm_nonneg _) (by positivity)
      _ = Ct * (Work.Kernels.scale τ) ^ Nt * (1 + t) ^ Mt * Real.exp (-(Real.pi * (t - τ.im))) := by rw [mul_one]
      _ ≤ Ct * (Work.Kernels.scale τ) ^ Nt * ((2:ℝ) ^ Mt * t ^ Mt) * Real.exp (-(Real.pi * (t - τ.im))) := by
          gcongr
      _ = Ct * (Work.Kernels.scale τ) ^ Nt * Real.exp (Real.pi * τ.im) * (2:ℝ) ^ Mt
            * (t ^ Mt * Real.exp (-(Real.pi * t))) := by
          rw [hexp2]; ring
  have hIfK : IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) (Set.Ioc (τ.im - 1) (τ.im + 1)) := by
    refine IntegrableOn.of_bound ?_ ?_ Bk ?_
    · exact lt_of_le_of_lt (measure_mono (Set.Ioc_subset_Icc_self)) isCompact_Icc.measure_lt_top
    · exact (hmeasK.mul hexpcont.measurable).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul]
      exact (mul_le_mul (hBk t (le_of_lt ht.1) ht.2) (hen t (by linarith [ht.1])) (norm_nonneg _)
        hBk0).trans (by rw [mul_one])
  have hIfA : IntegrableOn (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) (Set.Ioc (τ.im - 1) (τ.im + 1)) := by
    refine IntegrableOn.of_bound ?_ ?_ BA ?_
    · exact lt_of_le_of_lt (measure_mono (Set.Ioc_subset_Icc_self)) isCompact_Icc.measure_lt_top
    · exact (hmeasA.mul hexpcont.measurable).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul]
      exact (mul_le_mul (hBA t ht) (hen t (by linarith [ht.1])) (norm_nonneg _)
        hBA0).trans (by rw [mul_one])
  have hset : Set.Ioi (1:ℝ) = Set.Ioc 1 (τ.im - 1) ∪ (Set.Ioc (τ.im - 1) (τ.im + 1) ∪ Set.Ioi (τ.im + 1)) := by
    ext t
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht
      by_cases h : t ≤ τ.im - 1
      · exact Or.inl ⟨ht, h⟩
      · push Not at h
        by_cases h' : t ≤ τ.im + 1
        · exact Or.inr (Or.inl ⟨h, h'⟩)
        · push Not at h'
          exact Or.inr (Or.inr h')
    · rintro (⟨h1, -⟩ | ⟨h1', h2'⟩ | h3)
      · exact h1
      · linarith
      · linarith
  have hdisj1 : Disjoint (Set.Ioc (1:ℝ) (τ.im - 1))
      (Set.Ioc (τ.im - 1) (τ.im + 1) ∪ Set.Ioi (τ.im + 1)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases hx2 with h | h
    · exact absurd h.1 (not_lt.mpr hx1.2)
    · exact absurd h (not_lt.mpr (le_trans hx1.2 (by linarith)))
  have hdisj2 : Disjoint (Set.Ioc (τ.im - 1) (τ.im + 1)) (Set.Ioi (τ.im + 1)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact absurd hx2 (not_lt.mpr hx1.2)
  have hIf23 : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
      (Set.Ioc (τ.im - 1) (τ.im + 1) ∪ Set.Ioi (τ.im + 1)) := hIf2.union hIf3
  have hmiddle : (∫ t in (τ.im - 1)..(τ.im + 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
      = (∫ t in (τ.im - 1)..(τ.im + 1), Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
        - (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) := by
    rw [intervalIntegral.integral_of_le hY1, intervalIntegral.integral_of_le hY1,
      intervalIntegral.integral_of_le hY1]
    rw [show (∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
        = ∫ t in Set.Ioc (τ.im - 1) (τ.im + 1),
            (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))) - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) from by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t _
      ring]
    exact MeasureTheory.integral_sub hIfK hIfA
  have hspike : (∫ t in (τ.im - 1)..(τ.im + 1), Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) = Work.Asymptotics.spikeT ℓ d τ (r^2) := by
    rw [Work.Asymptotics.spikeT]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [truncExp_eq, truncWgt_eq]
  have htail : (∫ t in Set.Ioi (τ.im + 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) = Work.Asymptotics.tailT ℓ d τ (r^2) := by
    rw [Work.Asymptotics.tailT]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [truncExp_eq, truncWgt_eq]
  have key : (∫ t in Set.Ici (1:ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
      = (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
        + Work.Asymptotics.spikeT ℓ d τ (r^2)
        - (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
        + Work.Asymptotics.tailT ℓ d τ (r^2) := by
    rw [show (∫ t in Set.Ici (1:ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) = ∫ t in Set.Ioi (1:ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))) from
        integral_Ici_eq_integral_Ioi]
    rw [hset]
    rw [MeasureTheory.setIntegral_union hdisj1 (measurableSet_Ioc.union measurableSet_Ioi) hIf1 hIf23]
    rw [MeasureTheory.setIntegral_union hdisj2 measurableSet_Ioi hIf2 hIf3]
    rw [show (∫ t in Set.Ioc (1:ℝ) (τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) = ∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))) from
        (intervalIntegral.integral_of_le hY).symm]
    rw [show (∫ t in Set.Ioc (τ.im - 1) (τ.im + 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) = ∫ t in (τ.im - 1)..(τ.im + 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))) from
        (intervalIntegral.integral_of_le hY1).symm]
    rw [hmiddle, hspike, htail]
    ring
  rw [Work.Asymptotics.layerTrunc, key]
  ring


/-! ## Smoothness of the spike and tail pieces -/

/-- Integral over `[c,∞)` of the indicator of a set `s ⊆ [c,∞)`. -/
lemma setIntegral_Ici_indicator {F : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s) {c : ℝ}
    (hc : ∀ x ∈ s, c ≤ x) :
    (∫ t in Set.Ici c, s.indicator F t) = ∫ t in s, F t := by
  have h2 : (∫ t in Set.Ici c, s.indicator F t) = ∫ t, s.indicator F t :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [Set.indicator_of_notMem]
      intro hmem
      exact absurd (hc x hmem) hx)
  rw [h2, MeasureTheory.integral_indicator hs]

/-- The compactly supported amplitude of the spike piece `∫_{Im τ - 1}^{Im τ + 1} K`. -/
noncomputable def truncSpikeAmp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) : ℝ → ℂ :=
  fun t => if t ∈ Set.Ioc (τ.im - 1) (τ.im + 1) then Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
    else 0

/-- The amplitude of the tail piece, extended by zero below `Im τ + 1`. -/
noncomputable def truncTailAmp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) : ℝ → ℂ :=
  fun t => if t ∈ Set.Ioi (τ.im + 1) then
    (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
    else 0

/-- **Analyticity of the spike piece.**  The amplitude `K(τ,·)` is bounded on the compact spike
`[Im τ - 1, Im τ + 1]`, so the parametric integral is entire in `r²`. -/
theorem spikeContDiff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2)) := by
  intro τ hτ
  obtain ⟨B, hB0, hB⟩ := Work.Asymptotics.spikeWindow_bound ℓ d hd τ hτ
  have hY1 : τ.im - 1 ≤ τ.im + 1 := by linarith
  set C : ℝ := max (B * Real.exp (Real.pi * (τ.im + 1))) 1 with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hmeasAmp : Measurable (truncSpikeAmp ℓ d τ) := by
    rw [show truncSpikeAmp ℓ d τ = fun t => if t ∈ Set.Ioc (τ.im - 1) (τ.im + 1) then
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t else 0 from rfl]
    exact (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).ite measurableSet_Ioc measurable_const
  have hbd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (τ.im - 1) (τ.im + 1))),
      ‖truncSpikeAmp ℓ d τ t‖ ≤ C := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    by_cases ht : t ∈ Set.Ioc (τ.im - 1) (τ.im + 1)
    · rw [show truncSpikeAmp ℓ d τ t = Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t from by
        rw [truncSpikeAmp]; exact if_pos ht]
      have h1 := hB t (le_of_lt ht.1) ht.2
      have h2 : B ≤ C := by
        have h3 : B * Real.exp (Real.pi * (τ.im + 1)) ≤ C := le_max_left _ _
        have h4 : (1:ℝ) ≤ Real.exp (Real.pi * (τ.im + 1)) := Real.one_le_exp (by positivity)
        nlinarith [hB0, h3, h4]
      exact h1.trans h2
    · rw [show truncSpikeAmp ℓ d τ t = 0 from by rw [truncSpikeAmp]; exact if_neg ht, norm_zero]
      exact hCpos.le
  have hcd := laplace_interval_contDiff_omega (κ := truncSpikeAmp ℓ d τ) hY1 hCpos.le
    hmeasAmp.aestronglyMeasurable hbd
  have hkey : ∀ r : ℝ, Work.Asymptotics.spikeT ℓ d τ (r^2)
      = ∫ t in (τ.im - 1)..(τ.im + 1), truncSpikeAmp ℓ d τ t
          * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))) := by
    intro r
    have h1 : (∫ t in (τ.im - 1)..(τ.im + 1), truncSpikeAmp ℓ d τ t
          * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
        = ∫ t in (τ.im - 1)..(τ.im + 1), Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))) := by
      rw [intervalIntegral.integral_of_le hY1, intervalIntegral.integral_of_le hY1]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp only [truncSpikeAmp]
      rw [if_pos ht]
    rw [Work.Asymptotics.spikeT, h1]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [truncExp_eq, truncWgt_eq]
  rw [show (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))
      = fun s : ℝ => Work.Asymptotics.sinSq s
          * (∫ t in (τ.im - 1)..(τ.im + 1), truncSpikeAmp ℓ d τ t
              * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))) from by
    funext r; rw [hkey r]]
  exact Work.Asymptotics.contDiff_omega_sinSq.mul hcd

/-- **Analyticity of the tail piece.**  Above `Im τ + 1` the amplitude decays like
`e^{-π(t - Im τ)}`, which is `e^{-πt}` up to the constant `e^{π Im τ}`. -/
theorem tailContDiff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s^2)) := by
  intro τ hτ
  obtain ⟨Ct, Nt, Mt, hCt, hNt, hMt, htl⟩ := Work.Asymptotics.funnelKernelTailGcusp ℓ d hd
  have hSpos : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  set C2 : ℝ := max (Ct * (Work.Kernels.scale τ) ^ (Nt + Mt) * (2:ℝ) ^ Mt
      * Real.exp (Real.pi * τ.im)) 1 with hC2def
  have hC2pos : 0 < C2 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hmeasAmp : Measurable (truncTailAmp ℓ d τ) := by
    rw [show truncTailAmp ℓ d τ = fun t => if t ∈ Set.Ioi (τ.im + 1) then
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) else 0 from rfl]
    exact ((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
      (by unfold Work.Asymptotics.Aexp; fun_prop)).ite measurableSet_Ioi measurable_const
  have hbd : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))),
      ‖truncTailAmp ℓ d τ t‖ ≤ C2 * t ^ Mt * Real.exp (-(Real.pi * t)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t htIci
    by_cases ht : t ∈ Set.Ioi (τ.im + 1)
    · rw [show truncTailAmp ℓ d τ t
          = (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) from by
        rw [truncTailAmp]; exact if_pos ht]
      have hτ2 : (2:ℝ) ≤ τ.im := hτ.2
      have ht1 : τ.im + 1 ≤ t := le_of_lt ht
      have ht0 : 0 < t := by linarith
      have h1 := htl τ t hτ ht1
      have hbase1 : 1 + t ≤ Work.Kernels.scale τ * (2 * t) := by
        have h0t : (0:ℝ) ≤ 1 + t := by linarith
        have ha : 1 + t ≤ (1 + τ.im) * (1 + t) := by
          have h1' : 0 ≤ τ.im * (1 + t) := mul_nonneg (by linarith) h0t
          nlinarith
        have hb : (1 + τ.im) * (1 + t) ≤ Work.Kernels.scale τ * (2 * t) := by
          have hb2 : (1 + τ.im) ≤ Work.Kernels.scale τ := by
            rw [Work.Kernels.scale]
            have h1' : τ.im ≤ ‖(τ : ℂ)‖ := Work.Kernels.im_le_coe_norm τ
            have h2' : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le
            linarith
          have hc : 1 + t ≤ 2 * t := by linarith
          exact mul_le_mul hb2 hc h0t hSpos.le
        exact le_trans ha hb
      have hbase0 : 0 ≤ 1 + t := by linarith
      have hpow : (1 + t) ^ Mt ≤ (Work.Kernels.scale τ) ^ Mt * (2:ℝ) ^ Mt * t ^ Mt := by
        have h := Real.rpow_le_rpow hbase0 hbase1 hMt
        rw [Real.mul_rpow (le_of_lt hSpos) (by linarith : (0:ℝ) ≤ 2 * t),
          Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) ht0.le] at h
        calc (1 + t) ^ Mt ≤ Work.Kernels.scale τ ^ Mt * ((2:ℝ) ^ Mt * t ^ Mt) := h
          _ = Work.Kernels.scale τ ^ Mt * (2:ℝ) ^ Mt * t ^ Mt := by ring
      have hexp : Real.exp (-(Real.pi * (t - τ.im)))
          = Real.exp (Real.pi * τ.im) * Real.exp (-(Real.pi * t)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hSa : (Work.Kernels.scale τ) ^ Nt * (Work.Kernels.scale τ) ^ Mt
          = (Work.Kernels.scale τ) ^ (Nt + Mt) := by
        rw [← Real.rpow_add hSpos]
      have htM : 0 ≤ t ^ Mt := Real.rpow_nonneg ht0.le Mt
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
          ≤ Ct * (Work.Kernels.scale τ) ^ Nt * (1 + t) ^ Mt
              * Real.exp (-(Real.pi * (t - τ.im))) := h1
        _ ≤ Ct * (Work.Kernels.scale τ) ^ Nt
              * ((Work.Kernels.scale τ) ^ Mt * (2:ℝ) ^ Mt * t ^ Mt)
              * Real.exp (-(Real.pi * (t - τ.im))) := by
            have h0 : (0:ℝ) ≤ Ct * (Work.Kernels.scale τ) ^ Nt :=
              mul_nonneg hCt (Real.rpow_nonneg hSpos.le _)
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_left hpow h0
        _ = (Ct * (Work.Kernels.scale τ) ^ (Nt + Mt) * (2:ℝ) ^ Mt
              * Real.exp (Real.pi * τ.im)) * t ^ Mt
              * Real.exp (-(Real.pi * t)) := by
            rw [show Ct * (Work.Kernels.scale τ) ^ Nt
                  * ((Work.Kernels.scale τ) ^ Mt * (2:ℝ) ^ Mt * t ^ Mt)
                  * Real.exp (-(Real.pi * (t - τ.im)))
                = Ct * ((Work.Kernels.scale τ) ^ Nt * (Work.Kernels.scale τ) ^ Mt)
                  * (2:ℝ) ^ Mt * t ^ Mt
                  * Real.exp (-(Real.pi * (t - τ.im))) from by ring]
            rw [hSa, hexp]
            ring
        _ ≤ C2 * t ^ Mt * Real.exp (-(Real.pi * t)) := by
            have hle : Ct * (Work.Kernels.scale τ) ^ (Nt + Mt) * (2:ℝ) ^ Mt
                * Real.exp (Real.pi * τ.im) ≤ C2 := le_max_left _ _
            refine (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hle htM) (Real.exp_pos _).le).trans_eq ?_
            ring
    · rw [show truncTailAmp ℓ d τ t = 0 from by rw [truncTailAmp]; exact if_neg ht, norm_zero]
      have htge : (0:ℝ) ≤ t := by linarith [Set.mem_Ici.mp htIci]
      exact mul_nonneg (mul_nonneg hC2pos.le (Real.rpow_nonneg htge _)) (Real.exp_pos _).le
  have hcd := Work.Asymptotics.contDiff_omega_integral_Ici_exp
    (C := C2) (M := Mt) hC2pos hMt hmeasAmp.aestronglyMeasurable hbd
  have hkey : ∀ r : ℝ, Work.Asymptotics.tailT ℓ d τ (r^2)
      = ∫ t in Set.Ici (1:ℝ), truncTailAmp ℓ d τ t
          * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))) := by
    intro r
    have h1 : (∫ t in Set.Ici (1:ℝ), truncTailAmp ℓ d τ t
          * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
        = ∫ t in Set.Ioi (τ.im + 1),
            (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
              * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))) := by
      rw [show (fun t : ℝ => truncTailAmp ℓ d τ t
            * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ))))
          = (Set.Ioi (τ.im + 1)).indicator (fun t : ℝ =>
              (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
                - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
                * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) from by
        funext t
        rw [truncTailAmp]
        by_cases hc : t ∈ Set.Ioi (τ.im + 1)
        · rw [if_pos hc, Set.indicator_of_mem hc]
        · rw [if_neg hc, Set.indicator_of_notMem hc, zero_mul]]
      exact setIntegral_Ici_indicator measurableSet_Ioi (fun x hx => by
        have h2' : (2:ℝ) ≤ τ.im := hτ.2
        have hx' : τ.im + 1 < x := hx
        linarith)
    rw [Work.Asymptotics.tailT, h1]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [truncExp_eq, truncWgt_eq]
  rw [show (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s^2))
      = fun s : ℝ => Work.Asymptotics.sinSq s
          * (∫ t in Set.Ici (1:ℝ), truncTailAmp ℓ d τ t
              * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))) from by
    funext r; rw [hkey r]]
  exact Work.Asymptotics.contDiff_omega_sinSq.mul hcd


/-! ## The assembly -/

/-- **The `trunc` piece of the CKMRV layer on the funnel.**
`layerTrunc G ℓ d τ r = sinSq r · ∫_1^∞ (K(τ,it) - 𝒢(τ,it)) e^{-πr²t} dt` is the contribution of
the half-line `[1,∞)` of the CKMRV layer.  From the window bound `hwin` below the pole and the
exponential smallness `hG1` of the `i = 1` row of the coefficients, its `r`-seminorms on the funnel
are bounded by `c (scale τ)^N`, and it is analytic in `r`. -/
theorem funnelLayerTrunc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hwin : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
    (hG1 : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (j : Fin 2),
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
      ‖Work.Asymptotics.Gcusp ℓ d 1 j τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im))) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧
      (∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)) ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l
            (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ c * (Work.Kernels.scale τ) ^ N := by
  intro k l
  obtain ⟨cW, NW, hcW, hWcd, hWb⟩ := truncWindowPiece ℓ d hd hwin k l
  obtain ⟨cA, NA, hcA, hAcd, hAb⟩ := truncAexpMidPiece ℓ d hd hG1 k l
  obtain ⟨cS, NS, hcS, hNS, hSb⟩ := Work.Asymptotics.funnelSpikeSeminorm ℓ d hd k l
  obtain ⟨cT, NT, hcT, hNT, hTb⟩ := Work.Asymptotics.funnelTailSeminorm ℓ d hd k l
  refine ⟨cW + cS + cA + cT, max (max NW NS) (max NA NT), by positivity, ?_, ?_⟩
  · intro τ hτ h2
    have hF : Work.Asymptotics.Funnel τ := ⟨hτ, h2⟩
    have h1 : ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.sinSq s *
        (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))) := hWcd τ hτ h2
    have h2' : ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.sinSq s *
        Work.Asymptotics.spikeT ℓ d τ (s^2)) := spikeContDiff ℓ d hd τ hF
    have h3 : ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.sinSq s *
        (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))) := hAcd τ hF
    have h4 : ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.sinSq s *
        Work.Asymptotics.tailT ℓ d τ (s^2)) := tailContDiff ℓ d hd τ hF
    rw [layerTruncPieces ℓ d hd hwin τ hτ h2]
    exact ((h1.add h2').sub h3).add h4
  · intro τ r hτ h2
    have hF : Work.Asymptotics.Funnel τ := ⟨hτ, h2⟩
    have hS1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hNW : NW ≤ max (max NW NS) (max NA NT) :=
      le_trans (le_max_left NW NS) (le_max_left _ _)
    have hNS : NS ≤ max (max NW NS) (max NA NT) :=
      le_trans (le_max_right NW NS) (le_max_left _ _)
    have hNA : NA ≤ max (max NW NS) (max NA NT) :=
      le_trans (le_max_left NA NT) (le_max_right _ _)
    have hNT : NT ≤ max (max NW NS) (max NA NT) :=
      le_trans (le_max_right NA NT) (le_max_right _ _)
    have b1 := hWb τ r hτ h2
    have b2 := hSb τ r hF
    have b3 := hAb τ r hF
    have b4 := hTb τ r hF
    have e1 : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s *
        (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))) r := ((hWcd τ hτ h2).contDiffAt).of_le le_top
    have e2 : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s *
        Work.Asymptotics.spikeT ℓ d τ (s^2)) r :=
      ((spikeContDiff ℓ d hd τ hF).contDiffAt).of_le le_top
    have e3 : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s *
        (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))) r := ((hAcd τ hF).contDiffAt).of_le le_top
    have e4 : ContDiffAt ℝ (l : WithTop ℕ∞) (fun s : ℝ => Work.Asymptotics.sinSq s *
        Work.Asymptotics.tailT ℓ d τ (s^2)) r :=
      ((tailContDiff ℓ d hd τ hF).contDiffAt).of_le le_top
    have hE : (fun s : ℝ => Work.Asymptotics.sinSq s *
            (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))
          + Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2)
          - Work.Asymptotics.sinSq s * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))
          + Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s^2))
        = (((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) + ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))) - ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))))) + ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s^2))) := rfl
    rw [layerTruncPieces ℓ d hd hwin τ hτ h2, hE,
      iteratedDeriv_add (f := ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) + ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))) - ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ))))))) (g := (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s^2)))
        (by exact (e1.add e2).sub e3) e4,
      iteratedDeriv_sub (f := ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) + ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2)))) (g := (fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) (by exact e1.add e2) e3,
      iteratedDeriv_add (f := (fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) (g := (fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))) e1 e2]
    have hNW : NW ≤ max (max NW NS) (max NA NT) :=
      le_trans (le_max_left NW NS) (le_max_left _ _)
    have hNS : NS ≤ max (max NW NS) (max NA NT) :=
      le_trans (le_max_right NW NS) (le_max_left _ _)
    have hNA : NA ≤ max (max NW NS) (max NA NT) :=
      le_trans (le_max_left NA NT) (le_max_right _ _)
    have hNT : NT ≤ max (max NW NS) (max NA NT) :=
      le_trans (le_max_right NA NT) (le_max_right _ _)
    have hN1 : (Work.Kernels.scale τ) ^ NW ≤ (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT)) :=
      Real.rpow_le_rpow_of_exponent_le hS1 hNW
    have hN2 : (Work.Kernels.scale τ) ^ NS ≤ (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT)) :=
      Real.rpow_le_rpow_of_exponent_le hS1 hNS
    have hN3 : (Work.Kernels.scale τ) ^ NA ≤ (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT)) :=
      Real.rpow_le_rpow_of_exponent_le hS1 hNA
    have hN4 : (Work.Kernels.scale τ) ^ NT ≤ (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT)) :=
      Real.rpow_le_rpow_of_exponent_le hS1 hNT
    have k1 : cW * (Work.Kernels.scale τ) ^ NW ≤ cW * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT)) :=
      mul_le_mul_of_nonneg_left hN1 hcW
    have k2 : cS * (Work.Kernels.scale τ) ^ NS ≤ cS * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT)) :=
      mul_le_mul_of_nonneg_left hN2 hcS
    have k3 : cA * (Work.Kernels.scale τ) ^ NA ≤ cA * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT)) :=
      mul_le_mul_of_nonneg_left hN3 hcA
    have k4 : cT * (Work.Kernels.scale τ) ^ NT ≤ cT * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT)) :=
      mul_le_mul_of_nonneg_left hN4 hcT
    have hsum : cW * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT))
          + cS * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT))
          + cA * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT))
          + cT * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT))
        = (cW + cS + cA + cT) * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT)) := by ring
    have htri : ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r + iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))) r
          - iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r + iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s^2))) r‖
        ≤ ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r‖ + ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))) r‖
          + ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r‖ + ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s^2))) r‖ := by
      have h1 := norm_add_le (iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r + iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))) r
        - iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r) (iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s^2))) r)
      have h2 := norm_sub_le (iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r + iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))) r)
        (iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r)
      have h3 := norm_add_le (iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r) (iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))) r)
      linarith
    calc |r| ^ k * ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r + iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))) r
            - iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r + iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s^2))) r‖
        ≤ |r| ^ k * (‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r‖ + ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))) r‖
            + ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r‖ + ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s^2))) r‖) :=
          mul_le_mul_of_nonneg_left htri (by positivity)
      _ = |r| ^ k * ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (1:ℝ)..(τ.im - 1), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r‖ + |r| ^ k * ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.spikeT ℓ d τ (s^2))) r‖
            + |r| ^ k * ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * (∫ t in (τ.im - 1)..(τ.im + 1), Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (s:ℂ)^2 * (t:ℂ)))))) r‖ + |r| ^ k * ‖iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.sinSq s * Work.Asymptotics.tailT ℓ d τ (s^2))) r‖ := by ring
      _ ≤ cW * (Work.Kernels.scale τ) ^ NW + cS * (Work.Kernels.scale τ) ^ NS + cA * (Work.Kernels.scale τ) ^ NA + cT * (Work.Kernels.scale τ) ^ NT :=
          add_le_add (add_le_add (add_le_add b1 b2) b3) b4
      _ ≤ cW * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT))
            + cS * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT))
            + cA * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT))
            + cT * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT)) :=
          add_le_add (add_le_add (add_le_add k1 k2) k3) k4
      _ = (cW + cS + cA + cT) * (Work.Kernels.scale τ) ^ (max (max NW NS) (max NA NT)) := hsum

end Work.Asymptotics.HalfFunnel
