/-
# Smoothness (analyticity) of the three pieces of the CKMRV layer

The three pieces of the layer defined in `Work.Asymptotics.F2LayerDefs` are, for each `τ` in the
fundamental domain `𝒟` of `Γ(2)`, *real analytic* functions of the radial variable `r`
(the smoothness level `⊤` of `ContDiff ℝ ⊤` is `ω`, i.e. analyticity):

* `layerLow` and `layerTrunc` by differentiating under the parametric integral — the flatness
  `hflat` of the kernel at the cusp `0` dominates the integrand on `(0,1]`, the a.e. bound `htail`
  on `[1,∞)`;
* `highPart`, because it is an explicit expression in the regularising factor `psi1`, the
  exponential and the polynomials `λ = πr²`, `μ = λ - 2π` in `r`.

The two analytic engines are

* `contDiff_complex_IocExp` / `contDiff_real_IocExp` (finite interval `(0,1]`, parameter `c λ t`),
* `contDiffOn_complex_tailIntegralC` / `contDiffOn_real_tailIntegral` (tail `[1,∞)`).

Both are proved by differentiating under the integral sign with the complex parameter
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), and then using that a complex differentiable
function is analytic (`DifferentiableOn.analyticOnNhd`).  The real-analyticity follows by
restriction of scalars and composition with `r ↦ (r : ℂ)`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.ParamIntegral
import Submission.Work.Asymptotics.TailIntegral
import Submission.Work.Asymptotics.aestronglyMeasurable_contourIntegrand_clean
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth

noncomputable section

open MeasureTheory UpperHalfPlane Filter Topology
open scoped Topology

namespace Work.Asymptotics

open Work.Kernels





lemma integrableOn_const_Ioc' {E : Type*} [NormedAddCommGroup E] (K : E) :
    Integrable (fun _ : ℝ => K) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
  integrableOn_const (hs := by rw [Real.volume_Ioc]; simp)

theorem contDiff_complex_IocExp (g : ℝ → ℂ) (c : ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hbdd : ∃ C : ℝ, ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖g t‖ ≤ C) :
    ContDiff ℂ ⊤ (fun u : ℂ => ∫ t in Set.Ioc (0:ℝ) 1, g t * Complex.exp (c * u * (t:ℂ))) := by
  obtain ⟨C, hC⟩ := hbdd
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC (1/2) ⟨by norm_num, by norm_num⟩)
  set B : ℝ := ‖c‖ + 1 with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have hB0 : 0 ≤ B := le_of_lt hBpos
  have hcle : ‖c‖ ≤ B := by rw [hB]; linarith
  have key : ∀ (m : ℕ) (x : ℂ) (X t : ℝ), t ∈ Set.Ioc (0:ℝ) 1 → ‖x‖ + 1 ≤ X →
      ‖g t * (c * (t:ℂ))^m * Complex.exp (c * x * (t:ℂ))‖ ≤ C * B^m * Real.exp (B * X) := by
    intro m x X t ht hx
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hX0 : 0 ≤ X := by linarith [norm_nonneg x]
    have hgre : (c * x * (t:ℂ)).re ≤ B * X := by
      calc (c * x * (t:ℂ)).re ≤ ‖c * x * (t:ℂ)‖ := Complex.re_le_norm _
        _ = ‖c‖ * ‖x‖ * |t| := by rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ B * X := by
            have htabs : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
            have hxn : ‖x‖ ≤ X := by linarith [norm_nonneg x]
            have h1 : ‖c‖ * ‖x‖ ≤ B * X := mul_le_mul hcle hxn (norm_nonneg x) hB0
            calc ‖c‖ * ‖x‖ * |t| ≤ B * X * 1 :=
                  mul_le_mul h1 htabs (abs_nonneg t) (mul_nonneg hB0 hX0)
                _ = B * X := by ring
    have hn1 : ‖g t‖ ≤ C := hC t ht
    have hn2 : ‖(c * (t:ℂ))^m‖ ≤ B^m := by
      rw [norm_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ m
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      nlinarith [hcle, ht1, norm_nonneg c]
    have hn3 : ‖Complex.exp (c * x * (t:ℂ))‖ ≤ Real.exp (B * X) := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr hgre
    have h1 : ‖g t‖ * ‖(c * (t:ℂ))^m‖ ≤ C * B^m :=
      mul_le_mul hn1 hn2 (norm_nonneg _) hC0
    have h3 : 0 ≤ C * B^m := mul_nonneg hC0 (pow_nonneg hB0 m)
    calc ‖g t * (c * (t:ℂ))^m * Complex.exp (c * x * (t:ℂ))‖
        = ‖g t‖ * ‖(c * (t:ℂ))^m‖ * ‖Complex.exp (c * x * (t:ℂ))‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ C * B^m * Real.exp (B * X) := mul_le_mul h1 hn3 (norm_nonneg _) h3
  have hF_meas : ∀ (m : ℕ) (u : ℂ), AEStronglyMeasurable
      (fun t : ℝ => g t * (c * (t:ℂ))^m * Complex.exp (c * u * (t:ℂ)))
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    intro m u
    exact (hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
        (c * (t:ℂ))^m).aestronglyMeasurable).mul
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (c * u * (t:ℂ))).aestronglyMeasurable
  have hint : ∀ (m : ℕ) (u : ℂ), Integrable
      (fun t : ℝ => g t * (c * (t:ℂ))^m * Complex.exp (c * u * (t:ℂ)))
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    intro m u
    refine Integrable.mono' (integrableOn_const_Ioc' (C * B^m * Real.exp (B * (‖u‖ + 2))))
      (hF_meas m u) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact key m u (‖u‖ + 2) t ht (by linarith)
  rw [contDiff_omega_iff_analyticOnNhd]
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
  intro u₀ _
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), ∀ x ∈ Metric.ball u₀ 1,
      HasDerivAt (fun u : ℂ => g t * Complex.exp (c * u * (t:ℂ)))
        (g t * (c * (t:ℂ)) * Complex.exp (c * x * (t:ℂ))) x := by
    filter_upwards with t x _
    have hu : HasDerivAt (fun u : ℂ => c * u * (t:ℂ)) (c * (t:ℂ)) x := by
      have h1 : HasDerivAt (fun u : ℂ => c * u) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      simpa using h1.mul_const (t:ℂ)
    have h2 : HasDerivAt (fun u : ℂ => Complex.exp (c * u * (t:ℂ)))
        (Complex.exp (c * x * (t:ℂ)) * (c * (t:ℂ))) x :=
      (Complex.hasDerivAt_exp _).comp x hu
    exact (h2.const_mul (g t)).congr_deriv (by ring)
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), ∀ x ∈ Metric.ball u₀ 1,
      ‖g t * (c * (t:ℂ)) * Complex.exp (c * x * (t:ℂ))‖
        ≤ C * B * Real.exp (B * (‖u₀‖ + 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht x hx
    have hxd : ‖x - u₀‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hx
    have h1 : ‖x‖ ≤ ‖u₀‖ + 1 := by
      have hlt := add_lt_add_left hxd ‖u₀‖
      calc ‖x‖ = ‖(x - u₀) + u₀‖ := by ring_nf
        _ ≤ ‖x - u₀‖ + ‖u₀‖ := norm_add_le _ _
        _ ≤ 1 + ‖u₀‖ := le_of_lt hlt
        _ = ‖u₀‖ + 1 := by ring
    have hx2 : ‖x‖ + 1 ≤ ‖u₀‖ + 2 := by linarith
    simpa using key 1 x (‖u₀‖ + 2) t ht hx2
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0:ℝ) 1)) (𝕜 := ℂ) (E := ℂ)
    (F := fun u t => g t * Complex.exp (c * u * (t:ℂ)))
    (F' := fun u t => g t * (c * (t:ℂ)) * Complex.exp (c * u * (t:ℂ)))
    (x₀ := u₀) (s := Metric.ball u₀ 1)
    (bound := fun _ => C * B * Real.exp (B * (‖u₀‖ + 2)))
    (Metric.ball_mem_nhds u₀ one_pos)
    (Filter.Eventually.of_forall fun u => by simpa using hF_meas 0 u)
    (by simpa using hint 0 u₀)
    (by simpa using hF_meas 1 u₀)
    hbound (integrableOn_const_Ioc' (C * B * Real.exp (B * (‖u₀‖ + 2)))) hdiff
  exact hres.2.differentiableAt.differentiableWithinAt

theorem contDiff_real_IocExp (g : ℝ → ℂ) (c : ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hbdd : ∃ C : ℝ, ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖g t‖ ≤ C) :
    ContDiff ℝ ⊤ (fun lam : ℝ => ∫ t in Set.Ioc (0:ℝ) 1, g t * Complex.exp (c * (lam:ℂ) * (t:ℂ))) := by
  have h1 : ContDiff ℝ ⊤ (fun u : ℂ => ∫ t in Set.Ioc (0:ℝ) 1, g t * Complex.exp (c * u * (t:ℂ))) :=
    (contDiff_complex_IocExp g c hmeas hbdd).restrict_scalars ℝ
  have h2 : ContDiff ℝ ⊤ (fun lam : ℝ => (lam:ℂ)) := Complex.ofRealCLM.contDiff
  have h3 := h1.comp h2
  simpa only [Function.comp_def] using h3




def tailIntegralC (g : ℝ → ℂ) (u : ℂ) : ℂ :=
  ∫ t in Set.Ici (1:ℝ), g t * Complex.exp (-(Real.pi * u * (t:ℂ)))

lemma norm_exp_neg_pi (u : ℂ) (t : ℝ) :
    ‖Complex.exp (-(Real.pi * u * (t:ℂ)))‖ = Real.exp (-(Real.pi * u.re * t)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

theorem differentiableAt_tailIntegralC (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ici (1:ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t)))
    {u₀ : ℂ} (hu₀ : -1 < u₀.re) :
    DifferentiableAt ℂ (tailIntegralC g) u₀ := by
  set d : ℝ := (u₀.re + 1) / 2 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hdpi : 0 < Real.pi * d := mul_pos Real.pi_pos hd0
  have hmajor : Integrable (fun t : ℝ => C * Real.pi * t ^ (M + 1) * Real.exp (-(Real.pi * d * t)))
      (volume.restrict (Set.Ici (1:ℝ))) := by
    have h1 := integrableOn_rpow_mul_exp_neg (M + 1) (Real.pi * d) (by linarith) hdpi
    simpa only [mul_assoc] using h1.const_mul (C * Real.pi)
  have hmajor0 : Integrable (fun t : ℝ => C * t ^ M * Real.exp (-(Real.pi * (1 + u₀.re) * t)))
      (volume.restrict (Set.Ici (1:ℝ))) := by
    have h1 := integrableOn_rpow_mul_exp_neg M (Real.pi * (1 + u₀.re)) hM
      (mul_pos Real.pi_pos (by linarith))
    simpa only [mul_assoc] using h1.const_mul C
  have hFmeas : ∀ u : ℂ, AEStronglyMeasurable
      (fun t : ℝ => g t * Complex.exp (-(Real.pi * u * (t:ℂ))))
        (volume.restrict (Set.Ici (1:ℝ))) := fun u =>
    hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (-(Real.pi * u * (t:ℂ)))).aestronglyMeasurable
  have hF'int : ∀ u : ℂ, AEStronglyMeasurable
      (fun t : ℝ => g t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * u * (t:ℂ))))
        (volume.restrict (Set.Ici (1:ℝ))) := fun u =>
    (hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
      (-(Real.pi * (t:ℂ)))).aestronglyMeasurable).mul
      (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-(Real.pi * u * (t:ℂ)))).aestronglyMeasurable
  have hint : Integrable (fun t : ℝ => g t * Complex.exp (-(Real.pi * u₀ * (t:ℂ))))
      (volume.restrict (Set.Ici (1:ℝ))) := by
    refine Integrable.mono' hmajor0 (hFmeas u₀) ?_
    filter_upwards [hb] with t ht
    rw [norm_mul, norm_exp_neg_pi]
    have hexp : Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * u₀.re * t))
        = Real.exp (-(Real.pi * (1 + u₀.re) * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖g t‖ * Real.exp (-(Real.pi * u₀.re * t))
        ≤ (C * t ^ M * Real.exp (-(Real.pi * t))) * Real.exp (-(Real.pi * u₀.re * t)) :=
          mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
      _ = C * t ^ M * Real.exp (-(Real.pi * (1 + u₀.re) * t)) := by
          have h : (C * t ^ M * Real.exp (-(Real.pi * t))) * Real.exp (-(Real.pi * u₀.re * t))
              = C * t ^ M * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * u₀.re * t))) := by
            ring
          rw [h, hexp]
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))), ∀ u ∈ Metric.ball u₀ d,
      ‖g t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * u * (t:ℂ)))‖
        ≤ C * Real.pi * t ^ (M + 1) * Real.exp (-(Real.pi * d * t)) := by
    filter_upwards [hb, ae_restrict_mem measurableSet_Ici] with t hbt ht u hu
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp ht)
    have hud : 1 + u.re ≥ d := by
      have h1 : ‖u - u₀‖ < d := by simpa [dist_eq_norm] using Metric.mem_ball.mp hu
      have h2 : |u.re - u₀.re| ≤ ‖u - u₀‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (u - u₀)
      have h3 : u₀.re - d = d - 1 := by rw [hd]; ring
      have h4 : u.re ≥ u₀.re - d := by
        have := abs_le.mp (le_trans h2 (le_of_lt h1))
        linarith [this.1]
      rw [h3] at h4
      linarith
    have hnorm1 : ‖-(Real.pi * (t:ℂ))‖ = Real.pi * t := by
      simp only [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
        Real.norm_of_nonneg ht0.le]
    rw [norm_mul, norm_mul, hnorm1, norm_exp_neg_pi]
    have htM : t ^ (M + 1) = t ^ M * t ^ (1:ℝ) := Real.rpow_add ht0 M 1
    have ht1' : t ^ (1:ℝ) = t := Real.rpow_one t
    have hexp : Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * u.re * t))
        = Real.exp (-(Real.pi * (1 + u.re) * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp2 : Real.exp (-(Real.pi * (1 + u.re) * t)) ≤ Real.exp (-(Real.pi * d * t)) := by
      apply Real.exp_le_exp.mpr
      have h2 : Real.pi * d * t ≤ Real.pi * (1 + u.re) * t := by
        rw [show Real.pi * d * t = d * (Real.pi * t) by ring,
            show Real.pi * (1 + u.re) * t = (1 + u.re) * (Real.pi * t) by ring]
        exact mul_le_mul_of_nonneg_right hud (by positivity)
      linarith
    calc ‖g t‖ * (Real.pi * t) * Real.exp (-(Real.pi * u.re * t))
        ≤ (C * t ^ M * Real.exp (-(Real.pi * t))) * (Real.pi * t)
            * Real.exp (-(Real.pi * u.re * t)) := by
          have h1 : ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t)) := hbt
          have h2 : (0:ℝ) ≤ Real.pi * t := by positivity
          have h3 : (0:ℝ) ≤ Real.exp (-(Real.pi * u.re * t)) := (Real.exp_pos _).le
          have h4 : (0:ℝ) ≤ C * t ^ M * Real.exp (-(Real.pi * t)) := by positivity
          exact mul_le_mul (mul_le_mul h1 le_rfl h2 h4) le_rfl h3 (by positivity)
      _ = C * Real.pi * t ^ (M + 1) * Real.exp (-(Real.pi * (1 + u.re) * t)) := by
          rw [htM, ht1']
          have hsplit : C * t ^ M * Real.exp (-(Real.pi * t)) * (Real.pi * t)
              * Real.exp (-(Real.pi * u.re * t))
              = C * Real.pi * (t ^ M * t) * (Real.exp (-(Real.pi * t))
                * Real.exp (-(Real.pi * u.re * t))) := by ring
          rw [hsplit, hexp]
      _ ≤ C * Real.pi * t ^ (M + 1) * Real.exp (-(Real.pi * d * t)) := by
          have h1 : (0:ℝ) ≤ C * Real.pi * t ^ (M + 1) := by positivity
          exact mul_le_mul_of_nonneg_left hexp2 h1
  have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))), ∀ u ∈ Metric.ball u₀ d,
      HasDerivAt (fun u : ℂ => g t * Complex.exp (-(Real.pi * u * (t:ℂ))))
        (g t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * u * (t:ℂ)))) u := by
    filter_upwards with t u _
    have hu : HasDerivAt (fun u : ℂ => -(Real.pi * u * (t:ℂ))) (-(Real.pi * (t:ℂ))) u := by
      have h1 : HasDerivAt (fun u : ℂ => Real.pi * u * (t:ℂ)) (Real.pi * (t:ℂ)) u := by
        simpa using ((hasDerivAt_id u).const_mul (Real.pi : ℂ)).mul_const (t:ℂ)
      have h2 : HasDerivAt (fun u : ℂ => -(Real.pi * u * (t:ℂ))) (-(Real.pi * (t:ℂ))) u :=
        h1.neg
      simpa using h2
    have h3 : HasDerivAt (fun u : ℂ => Complex.exp (-(Real.pi * u * (t:ℂ))))
        (Complex.exp (-(Real.pi * u * (t:ℂ))) * (-(Real.pi * (t:ℂ)))) u :=
      (Complex.hasDerivAt_exp _).comp u hu
    exact (h3.const_mul (g t)).congr_deriv (by ring)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ici (1:ℝ))) (𝕜 := ℂ) (E := ℂ)
    (F := fun u t => g t * Complex.exp (-(Real.pi * u * (t:ℂ))))
    (F' := fun u t => g t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * u * (t:ℂ))))
    (x₀ := u₀) (s := Metric.ball u₀ d)
    (bound := fun t => C * Real.pi * t ^ (M + 1) * Real.exp (-(Real.pi * d * t)))
    (Metric.ball_mem_nhds u₀ hd0)
    (Filter.Eventually.of_forall fun u => hFmeas u)
    (by simpa only [tailIntegralC] using hint)
    (hF'int u₀) hbound hmajor hdiff
  exact hres.2.differentiableAt

theorem contDiffOn_complex_tailIntegralC (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ici (1:ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t))) :
    ContDiffOn ℂ ⊤ (tailIntegralC g) {u : ℂ | -1 < u.re} := by
  intro u₀ hu₀
  simp only [Set.mem_ofPred_eq] at hu₀
  have hd0 : 0 < (u₀.re + 1) / 2 := by linarith
  have hball_sub : Metric.ball u₀ ((u₀.re + 1) / 2) ⊆ {u : ℂ | -1 < u.re} := by
    intro u hu
    simp only [Set.mem_ofPred_eq]
    have h1 : ‖u - u₀‖ < (u₀.re + 1) / 2 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hu
    have h2 : |u.re - u₀.re| ≤ ‖u - u₀‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (u - u₀)
    have h3 := abs_le.mp (le_trans h2 (le_of_lt h1))
    linarith [h3.1]
  have hAn : AnalyticOnNhd ℂ (tailIntegralC g) (Metric.ball u₀ ((u₀.re + 1) / 2)) :=
    DifferentiableOn.analyticOnNhd
      (fun u hu => (differentiableAt_tailIntegralC g hmeas hC hM hb (hball_sub hu)).differentiableWithinAt)
      Metric.isOpen_ball
  exact (AnalyticAt.analyticWithinAt (hAn u₀ (Metric.mem_ball_self hd0))).contDiffWithinAt




theorem contDiffOn_real_tailIntegralC (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ici (1:ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t))) :
    ContDiffOn ℝ ⊤ (fun lam : ℝ => tailIntegralC g (lam:ℂ)) (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ ⊤ (tailIntegralC g) {u : ℂ | -1 < u.re} :=
    (contDiffOn_complex_tailIntegralC g hmeas hC hM hb).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ⊤ (fun lam : ℝ => (lam:ℂ)) (Set.Ioi (-1)) :=
    Complex.ofRealCLM.contDiff.contDiffOn
  have h3 := h1.comp h2 (fun lam hl => by
    simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; exact hl)
  simpa only [Function.comp_def] using h3

theorem contDiffOn_real_tailIntegral (g : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ici (1:ℝ))))
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hb : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))),
      ‖g t‖ ≤ C * t ^ M * Real.exp (-(Real.pi * t))) :
    ContDiffOn ℝ ⊤ (tailIntegral g) (Set.Ioi (-1)) := by
  have hfun : ∀ lam : ℝ, tailIntegralC g (lam:ℂ) = tailIntegral g lam := by
    intro lam
    simp only [tailIntegralC, tailIntegral]
    congr 1 with t
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  refine (contDiffOn_real_tailIntegralC g hmeas hC hM hb).congr ?_
  intro lam _
  exact (hfun lam).symm

lemma integrable_psi1_integrand (x : ℝ) :
    Integrable (fun s : ℝ => (((1:ℝ) - s : ℝ) : ℂ) * Complex.exp (Complex.I * (x:ℂ) * (s:ℂ)))
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  refine Integrable.mono' (integrableOn_const_Ioc' (Real.exp ‖x‖)) ?_ ?_
  · exact (by fun_prop : Continuous fun s : ℝ =>
      (((1:ℝ) - s : ℝ) : ℂ) * Complex.exp (Complex.I * (x:ℂ) * (s:ℂ))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs1 : |1 - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    have hs2 : |s| ≤ 1 := by rw [abs_of_pos hs.1]; exact hs.2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have h2 : (Complex.I * (x:ℂ) * (s:ℂ)).re ≤ ‖x‖ := by
      calc (Complex.I * (x:ℂ) * (s:ℂ)).re ≤ ‖Complex.I * (x:ℂ) * (s:ℂ)‖ := Complex.re_le_norm _
        _ = ‖x‖ * |s| := by
            simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left hs2 (norm_nonneg x)
        _ = ‖x‖ := mul_one _
    have h3 : Real.exp ((Complex.I * (x:ℂ) * (s:ℂ)).re) ≤ Real.exp ‖x‖ := Real.exp_le_exp.mpr h2
    calc |1 - s| * Real.exp ((Complex.I * (x:ℂ) * (s:ℂ)).re)
        ≤ 1 * Real.exp ‖x‖ := mul_le_mul hs1 h3 (Real.exp_pos _).le (by norm_num)
      _ = Real.exp ‖x‖ := one_mul _

theorem contDiff_psi1 : ContDiff ℝ ⊤ Work.Asymptotics.psi1 := by
  have hmeas : AEStronglyMeasurable (fun s : ℝ => (((1:ℝ) - s : ℝ) : ℂ))
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (by fun_prop : Continuous fun s : ℝ => (((1:ℝ) - s : ℝ) : ℂ)).aestronglyMeasurable
  have hbdd : ∃ C : ℝ, ∀ s ∈ Set.Ioc (0:ℝ) 1, ‖(((1:ℝ) - s : ℝ) : ℂ)‖ ≤ C :=
    ⟨1, fun s hs => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]⟩
  have hZ : ContDiff ℝ ⊤ (fun x : ℝ => ∫ s in Set.Ioc (0:ℝ) 1,
      (((1:ℝ) - s : ℝ) : ℂ) * Complex.exp (Complex.I * (x:ℂ) * (s:ℂ))) :=
    contDiff_real_IocExp _ Complex.I hmeas hbdd
  have hF : ContDiff ℝ ⊤ (fun x : ℝ => 2 * (Complex.reCLM (∫ s in Set.Ioc (0:ℝ) 1,
      (((1:ℝ) - s : ℝ) : ℂ) * Complex.exp (Complex.I * (x:ℂ) * (s:ℂ))))) :=
    contDiff_const.mul (Complex.reCLM.contDiff.comp hZ)
  have hEq : Work.Asymptotics.psi1 = fun x : ℝ => 2 * (Complex.reCLM (∫ s in Set.Ioc (0:ℝ) 1,
      (((1:ℝ) - s : ℝ) : ℂ) * Complex.exp (Complex.I * (x:ℂ) * (s:ℂ)))) := by
    funext x
    rw [psi1, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    congr 1
    rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM (integrable_psi1_integrand x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    have h1 : Complex.exp (Complex.I * (x:ℂ) * (s:ℂ))
        = ((Real.cos (x*s) : ℝ) : ℂ) + ((Real.sin (x*s) : ℝ) : ℂ) * Complex.I := by
      rw [show Complex.I * (x:ℂ) * (s:ℂ) = ((x*s : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I (x*s)
    have h2 : (((1:ℝ) - s : ℝ) : ℂ) * (((Real.cos (x*s) : ℝ) : ℂ)
        + ((Real.sin (x*s) : ℝ) : ℂ) * Complex.I)
        = ((((1:ℝ) - s) * Real.cos (x*s) : ℝ) : ℂ)
          + ((((1:ℝ) - s) * Real.sin (x*s) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    simp only []
    rw [h1, h2, Complex.reCLM_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    ring
  rw [hEq]
  exact hF


/-! ## The regularising factor `psi1` and the `sin²` prefactor -/


/-! ## Analyticity of the pieces: the `sin²` prefactor -/

lemma contDiff_complex_sin : ContDiff ℝ ⊤ Complex.sin :=
  (Complex.contDiff_sin (n := ⊤)).restrict_scalars ℝ

lemma contDiff_sinSq : ContDiff ℝ ⊤ sinSq := by
  have hsin : ContDiff ℝ ⊤ Complex.sin := contDiff_complex_sin
  have hr : ContDiff ℝ ⊤ (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
  have hin : ContDiff ℝ ⊤ (fun r : ℝ => Real.pi * (r : ℂ) ^ 2 / 2) :=
    ((contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (Real.pi : ℂ))).mul (hr.pow 2)).div_const 2
  have h2 : ContDiff ℝ ⊤ (fun r : ℝ => Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2)) := hsin.comp hin
  have h3 : ContDiff ℝ ⊤ (fun r : ℝ => Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2) := h2.pow 2
  have h4 : ContDiff ℝ ⊤ (fun r : ℝ =>
      4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2) :=
    (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (4 : ℂ))).mul h3
  change ContDiff ℝ ⊤ (fun r : ℝ => 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2)
  exact h4



open Work.Kernels

lemma measurable_E14Fun : Measurable E14Fun := by
  unfold E14Fun
  exact (measurable_E4Fun.pow_const 2).mul measurable_E6Fun

lemma measurable_jInvariantFun : Measurable jInvariantFun := by
  unfold jInvariantFun
  exact (measurable_E4Fun.pow_const 3).div measurable_DeltaFun

lemma measurable_fk_0 : Measurable (fun w : ℍ => fk 0 w) := by
  simp only [fk]; norm_num

lemma measurable_fk_2 : Measurable (fun w : ℍ => fk 2 w) := by
  simp only [fk]; norm_num
  exact measurable_E14Fun.div measurable_DeltaFun

lemma measurable_fk_4 : Measurable (fun w : ℍ => fk 4 w) := by
  simp only [fk]; norm_num
  exact measurable_E4Fun

lemma measurable_fk_14 : Measurable (fun w : ℍ => fk 14 w) := by
  simp only [fk]; norm_num
  exact measurable_E14Fun

lemma measurable_fk_neg2 : Measurable (fun w : ℍ => fk (-2) w) := by
  simp only [fk]; norm_num
  exact measurable_E10Fun.div measurable_DeltaFun

lemma measurable_fk_list_14_12_10 :
    ∀ i : Fin 3, Measurable (fun w : ℍ => fk ((![14, 12, 10] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · exact measurable_fk_14
  · exact measurable_fk12
  · exact measurable_fk10

lemma measurable_fk_list_4_2_0 :
    ∀ i : Fin 3, Measurable (fun w : ℍ => fk ((![4, 2, 0] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · exact measurable_fk_4
  · exact measurable_fk_2
  · exact measurable_fk_0

lemma measurable_fk_list_12_10_8'' :
    ∀ i : Fin 3, Measurable (fun w : ℍ => fk ((![12, 10, 8] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · exact measurable_fk12
  · exact measurable_fk10
  · exact measurable_fk8

lemma measurable_fk_list_2_0_neg2 :
    ∀ i : Fin 3, Measurable (fun w : ℍ => fk ((![2, 0, -2] : Fin 3 → ℤ) i) w) := by
  intro i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · exact measurable_fk_2
  · exact measurable_fk_0
  · exact measurable_fk_neg2

lemma measurable_UpsilonPlus_24_entry (τ : ℍ) (i j : Fin 3) :
    Measurable (fun w : ℍ => UpsilonPlus 24 τ w i j) := by
  have hPi : ∀ k l : Fin 3, Measurable (fun w : ℍ => PiMat ![4, 2, 0] w k l) :=
    fun k l => measurable_PiMat_entry _ k l measurable_fk_list_4_2_0
  have hJ : Measurable (fun w : ℍ => jInvariantFun w) := measurable_jInvariantFun
  have hΔ : Measurable (fun w : ℍ => DeltaFun w) := measurable_DeltaFun
  have h8 : ¬ ((24 : ℕ) = 8) := by norm_num
  fin_cases i <;> fin_cases j <;>
    simp only [UpsilonPlus, h8, reduceIte, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const, Fin.sum_univ_three,
      Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
    fun_prop (disch := assumption)

lemma measurable_UpsilonMinus_24_entry (τ : ℍ) (i j : Fin 3) :
    Measurable (fun w : ℍ => UpsilonMinus 24 τ w i j) := by
  have hPi : ∀ k l : Fin 3, Measurable (fun w : ℍ => PiMat ![2, 0, -2] w k l) :=
    fun k l => measurable_PiMat_entry _ k l measurable_fk_list_2_0_neg2
  have hJ : Measurable (fun w : ℍ => jInvariantFun w) := measurable_jInvariantFun
  have hΔ : Measurable (fun w : ℍ => DeltaFun w) := measurable_DeltaFun
  have h8 : ¬ ((24 : ℕ) = 8) := by norm_num
  fin_cases i <;> fin_cases j <;>
    simp only [UpsilonMinus, h8, reduceIte, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const, Fin.sum_univ_three,
      Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
    fun_prop (disch := assumption)

lemma measurable_Kfun_snd_24 (ℓ : LogLambdaData) (τ : ℍ) :
    Measurable (fun w : ℍ => Kfun ℓ 24 τ w) := by
  have hUP : ∀ i j : Fin 3, Measurable (fun w : ℍ => UpsilonPlus 24 τ w i j) :=
    fun i j => measurable_UpsilonPlus_24_entry τ i j
  have hUM : ∀ i j : Fin 3, Measurable (fun w : ℍ => UpsilonMinus 24 τ w i j) :=
    fun i j => measurable_UpsilonMinus_24_entry τ i j
  have hphit : ∀ j : Fin 3, Measurable (fun w : ℍ => phitVec w j) := measurable_phitVec
  have hpsit : ∀ j : Fin 3, Measurable (fun w : ℍ => psitVec ℓ w j) := measurable_psitVec ℓ
  unfold Kfun KPlus KMinus
  fun_prop (disch := assumption)

theorem measurable_Kaxis_Kfun (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) :
    Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) τ t) := by
  rcases hd with rfl | rfl
  · exact measurable_Kaxis_of_measurable _ _ (measurable_Kfun_snd ℓ τ)
  · exact measurable_Kaxis_of_measurable _ _ (measurable_Kfun_snd_24 ℓ τ)


/-! ## The three pieces -/

/-- The three pieces of the CKMRV layer are, for each `τ ∈ 𝒟`, smooth functions of `r`:
`layerLow` and `layerTrunc` by differentiating under the parametric integral (`hflat` dominates the
integrand on `(0,1]`, the a.e. bound `htail` on `[1,∞)`), and `highPart` because it is an explicit
expression in `sinSq`, `psi1` and `exp`. -/
theorem layerPieces_smooth (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j))
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c N' : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.DomainD → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ c * (Work.Kernels.scale τ) ^ N' * t ^ N)
    (htail : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ τ : UpperHalfPlane,
      τ ∈ Work.Asymptotics.DomainD →
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))),
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
          ≤ C * (Work.Kernels.scale τ) ^ N * t ^ M * Real.exp (-(Real.pi * t))) :
    ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD →
      ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) ∧
      ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) ∧
      ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.highPart G τ s) := by
  intro τ hτ
  have hsinSq : ContDiff ℝ ⊤ (fun r : ℝ => sinSq r) := contDiff_sinSq
  have hofR : ContDiff ℝ ⊤ (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
  have hsq : ContDiff ℝ ⊤ (fun r : ℝ => r ^ 2) := contDiff_id.pow 2
  have hKmeas : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) τ t) := measurable_Kaxis_Kfun ℓ d hd τ
  refine ⟨?_, ?_, ?_⟩
  · -- the `low` piece
    obtain ⟨c, N', hc, hb⟩ := hflat 0 le_rfl
    have hmeas : AEStronglyMeasurable (fun t : ℝ => Kaxis (Kfun ℓ d) τ t)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := hKmeas.aestronglyMeasurable
    have hbdd : ∃ C : ℝ, ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C :=
      ⟨c * (scale τ) ^ N', fun t ht => by simpa using hb τ t hτ ht.1 ht.2⟩
    have hE := contDiff_real_IocExp (fun t : ℝ => Kaxis (Kfun ℓ d) τ t) (-(Real.pi : ℂ)) hmeas hbdd
    have hcomp : ContDiff ℝ ⊤ (fun r : ℝ => ∫ t in Set.Ioc (0:ℝ) 1,
        Kaxis (Kfun ℓ d) τ t
          * Complex.exp ((-(Real.pi : ℂ)) * ((r ^ 2 : ℝ) : ℂ) * (t : ℂ))) := hE.comp hsq
    have hfun : (fun s : ℝ => layerLow ℓ d τ s) = fun r : ℝ => sinSq r *
        ∫ t in Set.Ioc (0:ℝ) 1, Kaxis (Kfun ℓ d) τ t
          * Complex.exp ((-(Real.pi : ℂ)) * ((r ^ 2 : ℝ) : ℂ) * (t : ℂ)) := by
      funext r
      rw [layerLow, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      congr 1
      congr 1
      push_cast
      ring_nf
    rw [hfun]
    exact hsinSq.mul hcomp
  · -- the `trunc` piece
    obtain ⟨C, N, M, hCpos, hN, hM, hb⟩ := htail
    set g : ℝ → ℂ := fun t => Kaxis (Kfun ℓ d) τ t - Aexp G τ t with hg
    have hAexp : AEStronglyMeasurable (fun t : ℝ => Aexp G τ t)
        (volume.restrict (Set.Ici (1:ℝ))) := by
      unfold Aexp
      fun_prop
    have hgmeas : AEStronglyMeasurable g (volume.restrict (Set.Ici (1:ℝ))) :=
      hKmeas.aestronglyMeasurable.sub hAexp
    have hbnd : ∀ᵐ t ∂(volume.restrict (Set.Ici (1:ℝ))),
        ‖g t‖ ≤ (C * (scale τ) ^ N) * t ^ M * Real.exp (-(Real.pi * t)) := hb τ hτ
    have htailC : ContDiffOn ℝ ⊤ (tailIntegral g) (Set.Ioi (-1)) :=
      contDiffOn_real_tailIntegral g hgmeas
        (mul_nonneg hCpos.le (Real.rpow_nonneg (scale_pos τ).le N)) hM hbnd
    have hcomp : ContDiffOn ℝ ⊤ (fun r : ℝ => tailIntegral g (r ^ 2)) Set.univ :=
      htailC.comp hsq.contDiffOn (fun r _ => by
        simp only [Set.mem_Ioi]
        linarith [sq_nonneg r])
    have htr : ContDiff ℝ ⊤ (fun r : ℝ => tailIntegral g (r ^ 2)) := contDiffOn_univ.mp hcomp
    have hfun : (fun s : ℝ => layerTrunc G ℓ d τ s) =
        fun r : ℝ => sinSq r * tailIntegral g (r ^ 2) := by
      funext r
      rw [layerTrunc, hg, tailIntegral]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only []
      congr 1
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hfun]
    exact hsinSq.mul htr
  · -- the `high` piece
    have hpsi : ContDiff ℝ ⊤ psi1 := contDiff_psi1
    have hlin : ContDiff ℝ ⊤ (fun r : ℝ => (Real.pi * r ^ 2 : ℝ)) :=
      contDiff_const.mul (contDiff_id.pow 2)
    have hlin2 : ContDiff ℝ ⊤ (fun r : ℝ => (Real.pi * r ^ 2 - 2 * Real.pi : ℝ)) :=
      hlin.sub contDiff_const
    have hA : ContDiff ℝ ⊤ (fun r : ℝ => ((Real.pi * r ^ 2 : ℝ) : ℂ)) := hofR.comp hlin
    have hB : ContDiff ℝ ⊤ (fun r : ℝ => ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)) :=
      hofR.comp hlin2
    have hP : ContDiff ℝ ⊤ (fun r : ℝ => ((psi1 (Real.pi * r ^ 2) : ℝ) : ℂ)) :=
      hofR.comp (hpsi.comp hlin)
    have hQ : ContDiff ℝ ⊤ (fun r : ℝ => ((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ)) :=
      hofR.comp (hpsi.comp hlin2)
    have heA : ContDiff ℝ ⊤ (fun r : ℝ => Complex.exp (-((Real.pi * r ^ 2 : ℝ) : ℂ))) :=
      (Complex.contDiff_exp (𝕜 := ℝ) (n := ⊤)).comp hA.neg
    have heB : ContDiff ℝ ⊤ (fun r : ℝ => Complex.exp (-((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ))) :=
      (Complex.contDiff_exp (𝕜 := ℝ) (n := ⊤)).comp hB.neg
    have hI : ContDiff ℝ ⊤ (fun _ : ℝ => Complex.I) := contDiff_const
    have h00 : ContDiff ℝ ⊤ (fun _ : ℝ => G 0 0 τ) := contDiff_const
    have h01 : ContDiff ℝ ⊤ (fun _ : ℝ => G 0 1 τ) := contDiff_const
    have h10 : ContDiff ℝ ⊤ (fun _ : ℝ => G 1 0 τ) := contDiff_const
    have h11 : ContDiff ℝ ⊤ (fun _ : ℝ => G 1 1 τ) := contDiff_const
    have hsum : ContDiff ℝ ⊤ (fun r : ℝ =>
        ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((psi1 (Real.pi * r ^ 2) : ℝ) : ℂ)
          * Complex.exp (-((Real.pi * r ^ 2 : ℝ) : ℂ)) * G 0 0 τ +
        Complex.I * ((psi1 (Real.pi * r ^ 2) : ℝ) : ℂ)
          * (((Real.pi * r ^ 2 : ℝ) : ℂ) + 1)
          * Complex.exp (-((Real.pi * r ^ 2 : ℝ) : ℂ)) * G 0 1 τ +
        ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)
          * ((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
          * Complex.exp (-((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)) * G 1 0 τ +
        Complex.I * ((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
          * (((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) + 1)
          * Complex.exp (-((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)) * G 1 1 τ) := by
      fun_prop (disch := assumption)
    rw [show (fun s : ℝ => highPart G τ s) = fun r : ℝ =>
        ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((psi1 (Real.pi * r ^ 2) : ℝ) : ℂ)
          * Complex.exp (-((Real.pi * r ^ 2 : ℝ) : ℂ)) * G 0 0 τ +
        Complex.I * ((psi1 (Real.pi * r ^ 2) : ℝ) : ℂ)
          * (((Real.pi * r ^ 2 : ℝ) : ℂ) + 1)
          * Complex.exp (-((Real.pi * r ^ 2 : ℝ) : ℂ)) * G 0 1 τ +
        ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)
          * ((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
          * Complex.exp (-((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)) * G 1 0 τ +
        Complex.I * ((psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℝ) : ℂ)
          * (((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) + 1)
          * Complex.exp (-((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)) * G 1 1 τ from by
      funext r
      simp only [highPart]]
    exact hsum

end Work.Asymptotics
