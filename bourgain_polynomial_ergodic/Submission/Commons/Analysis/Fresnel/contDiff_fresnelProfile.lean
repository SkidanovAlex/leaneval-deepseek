import Mathlib
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2

open MeasureTheory Filter
open scoped Interval Topology

namespace Commons.Analysis.Fresnel

/-- The complex-parameter version of the Fresnel profile:
`Φ(z) = ∫₀¹ e^{2πi z s²} ds`, defined for complex `z`. -/
noncomputable def fresnelProfileC (z : ℂ) : ℂ :=
  ∫ s in Set.Ioc (0 : ℝ) 1, Complex.exp (2 * Real.pi * Complex.I * (z * (s : ℂ) ^ 2))

lemma norm_two_pi : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
  rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)

lemma norm_two_pi_I : ‖((2 * Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
  rw [norm_mul, Complex.norm_I, mul_one, norm_two_pi]

lemma norm_sq_real (a : ℝ) : ‖(a : ℂ) ^ 2‖ = a ^ 2 := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma intervalIntegrable_to_integrable {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (h : IntervalIntegrable f volume 0 1) :
    Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  exact h

/-- `Φ` is complex differentiable (indeed entire). -/
lemma differentiable_fresnelProfileC : Differentiable ℂ fresnelProfileC := by
  intro x₀
  -- Pointwise bound on the derivative family, uniform on a ball around `x₀`.
  have hnorm : ∀ x ∈ Metric.ball x₀ 1, ∀ a : ℝ,
      ‖(2 * Real.pi * Complex.I * (a : ℂ) ^ 2)
          * Complex.exp (2 * Real.pi * Complex.I * (x * (a : ℂ) ^ 2))‖
        ≤ 2 * Real.pi * a ^ 2 * Real.exp (2 * Real.pi * (‖x₀‖ + 1) * a ^ 2) := by
    intro x hx a
    have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have h1 := mem_ball_iff_norm.mp hx
      calc ‖x‖ = ‖(x - x₀) + x₀‖ := by ring_nf
        _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
        _ ≤ 1 + ‖x₀‖ := by linarith
        _ = ‖x₀‖ + 1 := by ring
    have hc : ‖(2 * Real.pi * Complex.I * (a : ℂ) ^ 2 : ℂ)‖ = 2 * Real.pi * a ^ 2 := by
      rw [show (2 * Real.pi * Complex.I * (a : ℂ) ^ 2 : ℂ)
            = ((2 * Real.pi : ℂ) * Complex.I) * (a : ℂ) ^ 2 by ring]
      rw [norm_mul, norm_two_pi_I, norm_sq_real]
    have hz : ‖(2 * Real.pi * Complex.I * (x * (a : ℂ) ^ 2) : ℂ)‖
        ≤ 2 * Real.pi * (‖x₀‖ + 1) * a ^ 2 := by
      rw [show (2 * Real.pi * Complex.I * (x * (a : ℂ) ^ 2) : ℂ)
            = ((2 * Real.pi : ℂ) * Complex.I) * x * (a : ℂ) ^ 2 by ring]
      rw [norm_mul, norm_mul, norm_two_pi_I, norm_sq_real]
      gcongr
    rw [norm_mul, hc]
    calc 2 * Real.pi * a ^ 2 * ‖Complex.exp (2 * Real.pi * Complex.I * (x * (a : ℂ) ^ 2))‖
        ≤ 2 * Real.pi * a ^ 2 * Real.exp ‖2 * Real.pi * Complex.I * (x * (a : ℂ) ^ 2)‖ := by
          gcongr
          exact Complex.norm_exp_le_exp_norm _
      _ ≤ 2 * Real.pi * a ^ 2 * Real.exp (2 * Real.pi * (‖x₀‖ + 1) * a ^ 2) := by
          gcongr
  have hF_meas : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * (x * (s : ℂ) ^ 2)))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    Filter.Eventually.of_forall (fun x =>
      (by fun_prop : Continuous (fun s : ℝ =>
        Complex.exp (2 * Real.pi * Complex.I * (x * (s : ℂ) ^ 2)))).aestronglyMeasurable)
  have hF_int : Integrable (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * (x₀ * (s : ℂ) ^ 2)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    intervalIntegrable_to_integrable _
      ((by fun_prop : Continuous (fun s : ℝ =>
        Complex.exp (2 * Real.pi * Complex.I * (x₀ * (s : ℂ) ^ 2)))).intervalIntegrable 0 1)
  have hF'_meas : AEStronglyMeasurable
      (fun s : ℝ => (2 * Real.pi * Complex.I * (s : ℂ) ^ 2)
        * Complex.exp (2 * Real.pi * Complex.I * (x₀ * (s : ℂ) ^ 2)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (by fun_prop : Continuous (fun s : ℝ => (2 * Real.pi * Complex.I * (s : ℂ) ^ 2)
        * Complex.exp (2 * Real.pi * Complex.I * (x₀ * (s : ℂ) ^ 2)))).aestronglyMeasurable
  have h_bound : ∀ᵐ (a : ℝ) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ∀ x ∈ Metric.ball x₀ 1,
        ‖(fun (z : ℂ) (s : ℝ) => (2 * Real.pi * Complex.I * (s : ℂ) ^ 2)
            * Complex.exp (2 * Real.pi * Complex.I * (z * (s : ℂ) ^ 2))) x a‖
          ≤ 2 * Real.pi * a ^ 2 * Real.exp (2 * Real.pi * (‖x₀‖ + 1) * a ^ 2) :=
    Filter.Eventually.of_forall (fun a => fun x hx => hnorm x hx a)
  have hbound_int : Integrable
      (fun a : ℝ => 2 * Real.pi * a ^ 2 * Real.exp (2 * Real.pi * (‖x₀‖ + 1) * a ^ 2))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have hcont : Continuous (fun a : ℝ =>
        2 * Real.pi * a ^ 2 * Real.exp (2 * Real.pi * (‖x₀‖ + 1) * a ^ 2)) := by fun_prop
    have hii : IntervalIntegrable (fun a : ℝ =>
        2 * Real.pi * a ^ 2 * Real.exp (2 * Real.pi * (‖x₀‖ + 1) * a ^ 2)) volume 0 1 :=
      hcont.intervalIntegrable 0 1
    exact intervalIntegrable_to_integrable _ hii
  have h_diff : ∀ᵐ (a : ℝ) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ∀ x ∈ Metric.ball x₀ 1,
        HasDerivAt (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I * (z * (a : ℂ) ^ 2)))
          ((2 * Real.pi * Complex.I * (a : ℂ) ^ 2)
            * Complex.exp (2 * Real.pi * Complex.I * (x * (a : ℂ) ^ 2))) x := by
    refine Filter.Eventually.of_forall (fun a => fun x _ => ?_)
    have hlin : HasDerivAt
        (fun z : ℂ => ((2 * Real.pi : ℂ) * Complex.I * (a : ℂ) ^ 2) * z)
        ((2 * Real.pi : ℂ) * Complex.I * (a : ℂ) ^ 2) x :=
      hasDerivAt_const_mul (x := x) ((2 * Real.pi : ℂ) * Complex.I * (a : ℂ) ^ 2)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.cexp
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (F := fun (z : ℂ) (s : ℝ) => Complex.exp (2 * Real.pi * Complex.I * (z * (s : ℂ) ^ 2)))
      (F' := fun (z : ℂ) (s : ℝ) => (2 * Real.pi * Complex.I * (s : ℂ) ^ 2)
        * Complex.exp (2 * Real.pi * Complex.I * (z * (s : ℂ) ^ 2)))
      (bound := fun a : ℝ => 2 * Real.pi * a ^ 2 * Real.exp (2 * Real.pi * (‖x₀‖ + 1) * a ^ 2))
      (x₀ := x₀) (s := Metric.ball x₀ 1)
      (Metric.ball_mem_nhds x₀ one_pos) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hfun2 : fresnelProfileC = fun n : ℂ => ∫ a in Set.Ioc (0 : ℝ) 1,
      Complex.exp (2 * Real.pi * Complex.I * (n * (a : ℂ) ^ 2)) := by
    funext n
    rw [fresnelProfileC]
  rw [hfun2]
  exact hderiv.differentiableAt

lemma fresnelProfile_eq_fresnelProfileC (x : ℝ) :
    fresnelProfileC (x : ℂ) = fresnelProfile x := by
  rw [fresnelProfile, fresnelProfileC,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]

theorem contDiff_fresnelProfile :
    ContDiff ℝ (⊤ : ℕ∞) Commons.Analysis.Fresnel.fresnelProfile := by
  have hC : ContDiff ℝ (⊤ : WithTop ℕ∞) fresnelProfileC :=
    (differentiable_fresnelProfileC.contDiff).restrict_scalars ℝ
  have hC' : ContDiff ℝ (⊤ : ℕ∞) fresnelProfileC := hC.of_le le_top
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)))
  have hcomp := hC'.comp hsub
  simpa [Function.comp_def, fresnelProfile_eq_fresnelProfileC] using hcomp

end Commons.Analysis.Fresnel
