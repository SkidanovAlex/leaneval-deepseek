/-
# Smoothness (analyticity) and evenness of the CKMRV layer `F₂` in the radial variable

This file proves `Work.Asymptotics.paperLayer_smooth`: for `τ ∈ 𝒟` the CKMRV layer
`paperLayer G ℓ d τ` is a `C^ω` (in fact analytic) function of `r`, and it is even.

The layer is a sum of three pieces (`layerLow`, `layerTrunc`, `highPart`).  Every occurrence of `r`
in the layer is through `r²`:

* `highPart` is an explicit combination of `psi1` (which is entire, proved in
  `Submission.Work.Asymptotics.psi1_contDiff_omega`), `Complex.exp` and the constants `G i j τ`,
  evaluated at `λ = πr²` and `μ = πr² - 2π`;
* `layerLow` and `layerTrunc` are of the form `sinSq r` times a parametric integral
  `∫ κ(t) e^{-π r² t} dt` over `(0,1]` resp. `[1,∞)`.

The two analyticity inputs are isolated below: `contDiff_omega_intervalIntegral_exp` (a bounded
weight on the compact interval `(0,1]`) and `contDiff_omega_integral_Ici_exp` (a weight with an
`e^{-πt}`-type decay on `[1,∞)`).  Both are proved by extending the integrand to a holomorphic
function of the parameter and applying `analyticOnNhd_iff_differentiableOn`, differentiating under
the integral sign with `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

Evenness is then immediate because every occurrence of `r` is through `r²`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.psi1_contDiff_omega

noncomputable section

open MeasureTheory UpperHalfPlane Filter
open scoped Topology ContDiff

namespace Work.Asymptotics

/-! ## The two parametric integrals -/

/-- **Analyticity of the compact-interval parametric integral.**
If `κ` is a.e. strongly measurable on `(0,1]` and bounded there by `B`, then
`r ↦ ∫_0^1 κ t · e^{-π r² t} dt` is analytic in `r`.

The proof extends the (interval) integral to an entire function of the complex parameter `z`,
`Φ z = ∫_0^1 κ t · e^{-π z t} dt`, and restricts/composes with `r ↦ r²`. -/
theorem contDiff_omega_intervalIntegral_exp
    {κ : ℝ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hmeas : AEStronglyMeasurable κ (volume.restrict (Set.Ioc 0 1)))
    (hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 1)), ‖κ t‖ ≤ B) :
    ContDiff ℝ ω (fun r : ℝ => ∫ t in (0:ℝ)..1, κ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
  have hconv : ∀ f : ℝ → ℂ, (∫ t in (0:ℝ)..1, f t) = ∫ t, f t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    intro f; rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hcont_exp : ∀ w : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(Real.pi * w * (t:ℂ)))) (volume.restrict (Set.Ioc 0 1)) := by
    intro w
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).aestronglyMeasurable
  have hcont_lin : Continuous (fun t : ℝ => -(Real.pi * (t:ℂ))) :=
    (continuous_const.mul Complex.continuous_ofReal).neg
  have hnormpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [show ‖(Real.pi:ℂ)‖ = |Real.pi| from by
      rw [Complex.norm_def, Complex.normSq_ofReal]; simpa [sq] using Real.sqrt_sq_eq_abs Real.pi]
    exact abs_of_pos Real.pi_pos
  have hdiff : Differentiable ℂ (fun z : ℂ => ∫ t in (0:ℝ)..1, κ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) := by
    intro z
    have h_int : Integrable (fun t : ℝ => κ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) (volume.restrict (Set.Ioc 0 1)) := by
      refine Integrable.mono' (integrable_const (B * Real.exp (Real.pi * |z.re|))) ?_ ?_
      · exact hmeas.mul (hcont_exp z)
      · filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hbnd ht
        rw [norm_mul, Complex.norm_exp]
        have hexp : (-(Real.pi * z * (t:ℂ))).re = -(Real.pi * z.re * t) := by
          simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        rw [hexp]
        have h3 : - (z.re * t) ≤ |z.re| := by
          calc - (z.re * t) ≤ |z.re * t| := neg_le_abs _
            _ = |z.re| * |t| := abs_mul _ _
            _ ≤ |z.re| * 1 := mul_le_mul_of_nonneg_left (by rw [abs_of_pos ht.1]; exact ht.2) (abs_nonneg _)
            _ = |z.re| := mul_one _
        have h1 : -(Real.pi * z.re * t) ≤ Real.pi * |z.re| := by
          have : -(Real.pi * z.re * t) = Real.pi * (-(z.re * t)) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left h3 (le_of_lt Real.pi_pos)
        exact mul_le_mul hbnd (Real.exp_le_exp.mpr h1) (Real.exp_nonneg _) hB
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 1)), ∀ w ∈ Metric.ball z 1,
        ‖κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * w * (t:ℂ)))‖
          ≤ B * Real.pi * Real.exp (Real.pi * (|z.re| + 1)) := by
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
      have htle : t ≤ 1 := ht.2
      have htpos : 0 < t := ht.1
      have hnpi : ‖(Real.pi : ℂ) * (t:ℂ)‖ = Real.pi * t := by
        rw [Complex.norm_mul, hnormpi]
        congr 1
        rw [show ‖(t:ℂ)‖ = |t| from by
          rw [Complex.norm_def, Complex.normSq_ofReal]; simpa [sq] using Real.sqrt_sq_eq_abs t]
        exact abs_of_pos htpos
      rw [hnpi]
      have hexple : Real.exp (-(Real.pi * w.re * t)) ≤ Real.exp (Real.pi * (|z.re| + 1)) := by
        apply Real.exp_le_exp.mpr
        have h4 : -(w.re * t) ≤ |w.re| * t := by
          calc -(w.re * t) ≤ |w.re * t| := neg_le_abs _
            _ = |w.re| * |t| := abs_mul _ _
            _ = |w.re| * t := by rw [abs_of_pos htpos]
        have h5 : |w.re| * t ≤ |w.re| * 1 := mul_le_mul_of_nonneg_left htle (abs_nonneg _)
        nlinarith [Real.pi_pos, hre2]
      calc ‖κ t‖ * (Real.pi * t) * Real.exp (-(Real.pi * w.re * t))
          ≤ B * (Real.pi * t) * Real.exp (Real.pi * (|z.re| + 1)) := by
            apply mul_le_mul
            · exact mul_le_mul hbnd (le_refl _) (by positivity) hB
            · exact hexple
            · positivity
            · positivity
          _ ≤ B * Real.pi * Real.exp (Real.pi * (|z.re| + 1)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            have hpi : Real.pi * t ≤ Real.pi := by
              simpa using mul_le_mul_of_nonneg_left htle (le_of_lt Real.pi_pos)
            exact mul_le_mul_of_nonneg_left hpi hB
    have h_diff : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 1)), ∀ w ∈ Metric.ball z 1,
        HasDerivAt (fun w : ℂ => κ t * Complex.exp (-(Real.pi * w * (t:ℂ))))
          (κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * w * (t:ℂ)))) w := by
      filter_upwards with t
      intro w _
      have hlin : HasDerivAt (fun w : ℂ => Real.pi * w * (t:ℂ)) (Real.pi * (t:ℂ)) w := by
        have h := (hasDerivAt_id w).const_mul (Real.pi : ℂ)
        simpa using h.mul_const (t:ℂ)
      have hneg : HasDerivAt (fun w : ℂ => -(Real.pi * w * (t:ℂ))) (-(Real.pi * (t:ℂ))) w := hlin.neg
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
    have hF'_meas : AEStronglyMeasurable (fun t : ℝ => κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ)))) (volume.restrict (Set.Ioc 0 1)) := by
      apply AEStronglyMeasurable.mul ?_ (hcont_exp z)
      exact AEStronglyMeasurable.mul hmeas hcont_lin.aestronglyMeasurable
    obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
      (F := fun z t => κ t * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (F' := fun z t => κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (bound := fun _ => B * Real.pi * Real.exp (Real.pi * (|z.re| + 1)))
      (x₀ := z) (s := Metric.ball z 1)
      (Metric.ball_mem_nhds z one_pos)
      (Filter.Eventually.of_forall (fun w => hmeas.mul (hcont_exp w)))
      h_int hF'_meas h_bound (integrable_const _) h_diff
    have hfun : (fun n : ℂ => ∫ a, κ a * Complex.exp (-(Real.pi * n * (a:ℂ))) ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
        = fun n : ℂ => ∫ t in (0:ℝ)..1, κ t * Complex.exp (-(Real.pi * n * (t:ℂ))) := by
      funext n; exact (hconv _).symm
    rw [hfun] at hderiv
    exact hderiv.differentiableAt
  have hcdR : ContDiff ℝ ω (fun z : ℂ => ∫ t in (0:ℝ)..1, κ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) :=
    ((hdiff.differentiableOn.analyticOnNhd isOpen_univ).contDiff).restrict_scalars ℝ
  have hsq : ContDiff ℝ ω (fun r : ℝ => ((r:ℂ))^2) := Complex.ofRealCLM.contDiff.pow 2
  exact hcdR.comp hsq

/-- **Analyticity of the half-line parametric integral.**
If `ψ` is a.e. strongly measurable on `[1,∞)` with `‖ψ t‖ ≤ C t^M e^{-πt}` there (`C > 0`,
`M ≥ 0`), then `r ↦ ∫_1^∞ ψ t · e^{-π r² t} dt` is analytic in `r`.

The complex extension `Φ z = ∫_1^∞ ψ t · e^{-π z t} dt` is holomorphic on the half-plane
`{Re z > -1}`; the composition with `r ↦ r²` (whose image is `[0,∞) ⊂ {Re z > -1}`) yields the
claim. -/
theorem contDiff_omega_integral_Ici_exp
    {ψ : ℝ → ℂ} {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hmeas : AEStronglyMeasurable ψ (volume.restrict (Set.Ici 1)))
    (hbound : ∀ᵐ t ∂(volume.restrict (Set.Ici 1)), ‖ψ t‖ ≤ C * t^M * Real.exp (-(Real.pi * t))) :
    ContDiff ℝ ω (fun r : ℝ => ∫ t in Set.Ici 1, ψ t * Complex.exp (-(Real.pi * (r:ℂ)^2 * (t:ℂ)))) := by
  set U : Set ℂ := {z | -1 < z.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hcont : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(Real.pi * z * (t:ℂ)))) (volume.restrict (Set.Ici 1)) :=
    fun z => (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).aestronglyMeasurable
  have hcont_lin : Continuous (fun t : ℝ => -(Real.pi * (t:ℂ))) :=
    (continuous_const.mul Complex.continuous_ofReal).neg
  have hint_base : ∀ η : ℝ, 0 < η → Integrable (fun t : ℝ => C * (t^M * Real.exp (-(Real.pi * η * t)))) (volume.restrict (Set.Ici 1)) := by
    intro η hη
    have h1 : IntegrableOn (fun t : ℝ => t^M * Real.exp ((-(Real.pi * η)) * t)) (Set.Ioi 0) := by
      simpa only [Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := M) (b := Real.pi * η) (by linarith) one_pos (by positivity)
    have heq : (fun t : ℝ => t^M * Real.exp ((-(Real.pi * η)) * t)) = (fun t : ℝ => t^M * Real.exp (-(Real.pi * η * t))) := by
      funext t; rw [neg_mul]
    rw [heq] at h1
    have h2 : IntegrableOn (fun t : ℝ => t^M * Real.exp (-(Real.pi * η * t))) (Set.Ici 1) :=
      h1.mono_set (Set.Ici_subset_Ioi.mpr (by norm_num))
    exact h2.const_mul C
  have hint_deriv : ∀ η : ℝ, 0 < η → Integrable (fun t : ℝ => (C * Real.pi) * (t^(M+1) * Real.exp (-(Real.pi * η * t)))) (volume.restrict (Set.Ici 1)) := by
    intro η hη
    have h1 : IntegrableOn (fun t : ℝ => t^(M+1) * Real.exp ((-(Real.pi * η)) * t)) (Set.Ioi 0) := by
      simpa only [Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := M+1) (b := Real.pi * η) (by linarith) one_pos (by positivity)
    have heq : (fun t : ℝ => t^(M+1) * Real.exp ((-(Real.pi * η)) * t)) = (fun t : ℝ => t^(M+1) * Real.exp (-(Real.pi * η * t))) := by
      funext t; rw [neg_mul]
    rw [heq] at h1
    have h2 : IntegrableOn (fun t : ℝ => t^(M+1) * Real.exp (-(Real.pi * η * t))) (Set.Ici 1) :=
      h1.mono_set (Set.Ici_subset_Ioi.mpr (by norm_num))
    exact h2.const_mul (C * Real.pi)
  have hΦ_diff : DifferentiableOn ℂ
      (fun z : ℂ => ∫ t in Set.Ici 1, ψ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) U := by
    intro z₀ hz₀
    have hz₀' : -1 < z₀.re := hz₀
    set η : ℝ := (z₀.re + 1) / 2 with hηdef
    have hηpos : 0 < η := by rw [hηdef]; linarith
    have hz₀_eq : z₀.re = -1 + 2 * η := by rw [hηdef]; ring
    have hbase := hint_base η hηpos
    have hder := hint_deriv η hηpos
    have hbd_base : ∀ᵐ t ∂(volume.restrict (Set.Ici 1)),
        ‖ψ t * Complex.exp (-(Real.pi * z₀ * (t:ℂ)))‖ ≤ C * (t^M * Real.exp (-(Real.pi * η * t))) := by
      filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ici] with t hbnd ht
      have ht1 : 1 ≤ t := ht
      have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
      rw [norm_mul, Complex.norm_exp]
      have hexp : (-(Real.pi * z₀ * (t:ℂ))).re = -(Real.pi * z₀.re * t) := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [hexp]
      have hkey : Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * z₀.re * t))
          ≤ Real.exp (-(Real.pi * η * t)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hEq : -(Real.pi * t) + -(Real.pi * z₀.re * t) = -(Real.pi * (1 + z₀.re) * t) := by ring
        rw [hEq]
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_right _ htpos.le
        apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
        linarith
      calc ‖ψ t‖ * Real.exp (-(Real.pi * z₀.re * t))
          ≤ (C * t^M * Real.exp (-(Real.pi * t))) * Real.exp (-(Real.pi * z₀.re * t)) :=
            mul_le_mul_of_nonneg_right hbnd (Real.exp_nonneg _)
        _ = C * (t^M * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * z₀.re * t)))) := by ring
        _ ≤ C * (t^M * Real.exp (-(Real.pi * η * t))) := by
            apply mul_le_mul_of_nonneg_left _ hC.le
            exact mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg (le_of_lt htpos) _)
    have hF_int : Integrable (fun t : ℝ => ψ t * Complex.exp (-(Real.pi * z₀ * (t:ℂ)))) (volume.restrict (Set.Ici 1)) :=
      hbase.mono' (hmeas.mul (hcont z₀)) hbd_base
    have hF'_meas : AEStronglyMeasurable (fun t : ℝ => ψ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z₀ * (t:ℂ)))) (volume.restrict (Set.Ici 1)) := by
      apply AEStronglyMeasurable.mul ?_ (hcont z₀)
      exact AEStronglyMeasurable.mul hmeas hcont_lin.aestronglyMeasurable
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ici 1)), ∀ z ∈ Metric.ball z₀ η,
        ‖ψ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ)))‖
          ≤ (C * Real.pi) * (t^(M+1) * Real.exp (-(Real.pi * η * t))) := by
      filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ici] with t hbnd ht
      intro z hz
      have ht1 : 1 ≤ t := ht
      have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : z.re > -1 + η := by
        have h1 := Complex.abs_re_le_norm (z - z₀)
        rw [Complex.sub_re] at h1
        have hlt : |z.re - z₀.re| < η := lt_of_le_of_lt h1 hz
        rw [abs_lt] at hlt
        rw [hz₀_eq] at hlt
        linarith [hlt.1]
      rw [norm_mul, norm_mul, Complex.norm_exp, norm_neg]
      have hexp : (-(Real.pi * z * (t:ℂ))).re = -(Real.pi * z.re * t) := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [hexp]
      have hnpi : ‖Real.pi * (t:ℂ)‖ = Real.pi * t := by
        rw [Complex.norm_mul]
        have h1 : ‖(Real.pi:ℂ)‖ = Real.pi := by
          rw [show ‖(Real.pi:ℂ)‖ = |Real.pi| from by
            rw [Complex.norm_def, Complex.normSq_ofReal]; simpa [sq] using Real.sqrt_sq_eq_abs Real.pi]
          exact abs_of_pos Real.pi_pos
        rw [h1, show ‖(t:ℂ)‖ = |t| from by
          rw [Complex.norm_def, Complex.normSq_ofReal]; simpa [sq] using Real.sqrt_sq_eq_abs t, abs_of_pos htpos]
      rw [hnpi]
      have hkey : Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * z.re * t))
          ≤ Real.exp (-(Real.pi * η * t)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hEq : -(Real.pi * t) + -(Real.pi * z.re * t) = -(Real.pi * (1 + z.re) * t) := by ring
        rw [hEq]
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_right _ htpos.le
        apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
        linarith
      have hrpow : t^(M+1) = t^M * t := by rw [Real.rpow_add htpos, Real.rpow_one]
      calc ‖ψ t‖ * (Real.pi * t) * Real.exp (-(Real.pi * z.re * t))
          ≤ (C * t^M * Real.exp (-(Real.pi * t))) * (Real.pi * t) * Real.exp (-(Real.pi * z.re * t)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact hbnd
        _ = (C * Real.pi) * (t^(M+1) * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * z.re * t)))) := by
            rw [hrpow]; ring
        _ ≤ (C * Real.pi) * (t^(M+1) * Real.exp (-(Real.pi * η * t))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg (le_of_lt htpos) _)
    have h_diff : ∀ᵐ t ∂(volume.restrict (Set.Ici 1)), ∀ z ∈ Metric.ball z₀ η,
        HasDerivAt (fun z : ℂ => ψ t * Complex.exp (-(Real.pi * z * (t:ℂ))))
          (ψ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ)))) z := by
      filter_upwards with t
      intro z _
      have hlin : HasDerivAt (fun z : ℂ => Real.pi * z * (t:ℂ)) (Real.pi * (t:ℂ)) z := by
        have h := (hasDerivAt_id z).const_mul (Real.pi : ℂ)
        simpa using h.mul_const (t:ℂ)
      have hneg : HasDerivAt (fun z : ℂ => -(Real.pi * z * (t:ℂ))) (-(Real.pi * (t:ℂ))) z := hlin.neg
      have hexp2 : HasDerivAt (fun z : ℂ => Complex.exp (-(Real.pi * z * (t:ℂ))))
          (Complex.exp (-(Real.pi * z * (t:ℂ))) * (-(Real.pi * (t:ℂ)))) z :=
        (Complex.hasDerivAt_exp (-(Real.pi * z * (t:ℂ)))).comp z hneg
      have h3 : HasDerivAt (fun z : ℂ => ψ t * Complex.exp (-(Real.pi * z * (t:ℂ))))
          (ψ t * (Complex.exp (-(Real.pi * z * (t:ℂ))) * (-(Real.pi * (t:ℂ))))) z :=
        hexp2.const_mul (ψ t)
      have heq : ψ t * (Complex.exp (-(Real.pi * z * (t:ℂ))) * (-(Real.pi * (t:ℂ))))
          = ψ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ))) := by ring
      rw [heq] at h3
      exact h3
    obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ici (1:ℝ)))
      (F := fun z t => ψ t * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (F' := fun z t => ψ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (bound := fun t => (C * Real.pi) * (t^(M+1) * Real.exp (-(Real.pi * η * t))))
      (x₀ := z₀) (s := Metric.ball z₀ η)
      (Metric.ball_mem_nhds z₀ hηpos)
      (Filter.Eventually.of_forall (fun z => hmeas.mul (hcont z)))
      hF_int hF'_meas h_bound hder h_diff
    exact hderiv.differentiableAt.differentiableWithinAt
  have hΦ_ana : AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in Set.Ici 1, ψ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) U :=
    hΦ_diff.analyticOnNhd hUopen
  have hcd : ContDiffOn ℝ ω (fun z : ℂ => ∫ t in Set.Ici 1, ψ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) U :=
    (hΦ_ana.contDiffOn_of_completeSpace).restrict_scalars ℝ
  have hsq : ContDiff ℝ ω (fun r : ℝ => ((r:ℂ))^2) := Complex.ofRealCLM.contDiff.pow 2
  have hmaps : ∀ r : ℝ, (fun r : ℝ => ((r:ℂ))^2) r ∈ U := by
    intro r
    simp only [U, Set.mem_ofPred_eq]
    have h : (((r:ℂ))^2).re = r^2 := by
      rw [sq, Complex.mul_re]; simp [Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [h]; nlinarith [sq_nonneg r]
  exact hcd.comp_contDiff hsq hmaps

/-! ## `sinSq` is analytic -/

theorem contDiff_omega_sinSq : ContDiff ℝ ω (fun s : ℝ => sinSq s) := by
  unfold sinSq
  have hsin : ContDiff ℝ ω Complex.sin := (Complex.contDiff_sin (n := ⊤)).restrict_scalars ℝ
  apply ContDiff.mul contDiff_const
  apply ContDiff.pow
  apply hsin.comp
  apply ContDiff.div_const
  apply ContDiff.mul contDiff_const
  exact Complex.ofRealCLM.contDiff.pow 2

/-! ## `highPart` is analytic -/

theorem contDiff_omega_highPart (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    ContDiff ℝ ω (fun s : ℝ => highPart G τ s) := by
  unfold highPart
  simp only
  have hp := psi1_contDiff_omega
  have hofReal : ∀ {f : ℝ → ℝ}, ContDiff ℝ ω f → ContDiff ℝ ω (fun s : ℝ => ((f s : ℝ) : ℂ)) :=
    fun hf => Complex.ofRealCLM.contDiff.comp hf
  have hs2 : ContDiff ℝ ω (fun s : ℝ => s^2) := contDiff_id.pow 2
  have hpi2 : ContDiff ℝ ω (fun s : ℝ => Real.pi * s^2) := ContDiff.mul contDiff_const hs2
  have hl : ContDiff ℝ ω (fun s : ℝ => ((Real.pi * s^2 : ℝ):ℂ)) := hofReal hpi2
  have hm : ContDiff ℝ ω (fun s : ℝ => ((Real.pi * s^2 - 2*Real.pi : ℝ):ℂ)) :=
    hofReal (hpi2.sub contDiff_const)
  have hpsil : ContDiff ℝ ω (fun s : ℝ => ((psi1 (Real.pi * s^2):ℝ):ℂ)) := hp.comp hpi2
  have hpsim : ContDiff ℝ ω (fun s : ℝ => ((psi1 (Real.pi * s^2 - 2*Real.pi):ℝ):ℂ)) :=
    hp.comp (hpi2.sub contDiff_const)
  have hexpl : ContDiff ℝ ω (fun s : ℝ => Complex.exp (-((Real.pi * s^2 : ℝ):ℂ))) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp hl.neg
  have hexpm : ContDiff ℝ ω (fun s : ℝ => Complex.exp (-((Real.pi * s^2 - 2*Real.pi : ℝ):ℂ))) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp hm.neg
  have t1 : ContDiff ℝ ω (fun s : ℝ => ((Real.pi*s^2:ℝ):ℂ) * ((psi1 (Real.pi*s^2):ℝ):ℂ) * Complex.exp (-((Real.pi*s^2:ℝ):ℂ)) * G 0 0 τ) :=
    ((hl.mul hpsil).mul hexpl).mul contDiff_const
  have t2 : ContDiff ℝ ω (fun s : ℝ => Complex.I * ((psi1 (Real.pi*s^2):ℝ):ℂ) * (((Real.pi*s^2:ℝ):ℂ) + 1) * Complex.exp (-((Real.pi*s^2:ℝ):ℂ)) * G 0 1 τ) :=
    ((contDiff_const.mul hpsil).mul (hl.add contDiff_const)).mul hexpl |>.mul contDiff_const
  have t3 : ContDiff ℝ ω (fun s : ℝ => ((Real.pi*s^2 - 2*Real.pi:ℝ):ℂ) * ((psi1 (Real.pi*s^2 - 2*Real.pi):ℝ):ℂ) * Complex.exp (-((Real.pi*s^2 - 2*Real.pi:ℝ):ℂ)) * G 1 0 τ) :=
    ((hm.mul hpsim).mul hexpm).mul contDiff_const
  have t4 : ContDiff ℝ ω (fun s : ℝ => Complex.I * ((psi1 (Real.pi*s^2 - 2*Real.pi):ℝ):ℂ) * (((Real.pi*s^2 - 2*Real.pi:ℝ):ℂ) + 1) * Complex.exp (-((Real.pi*s^2 - 2*Real.pi:ℝ):ℂ)) * G 1 1 τ) :=
    ((contDiff_const.mul hpsim).mul (hm.add contDiff_const)).mul hexpm |>.mul contDiff_const
  exact ((t1.add t2).add t3).add t4

/-! ## The target theorem -/

/-- The CKMRV layer is, for each `τ ∈ 𝒟`, a smooth **even** function of `r`: every occurrence of
`r` in `paperLayer` is through `r²` (`sinSq r = 4 sin²(πr²/2)`, `e^{-πr²t}`, `λ = πr²`,
`μ = πr² - 2π`), and differentiating the two parametric integrals is justified by `hflat` on
`(0,1]` and the a.e. tail bound on `[1,∞)`. -/
theorem paperLayer_smooth (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
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
      ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.paperLayer G ℓ d τ s) ∧
      (∀ s : ℝ, Work.Asymptotics.paperLayer G ℓ d τ (-s)
        = Work.Asymptotics.paperLayer G ℓ d τ s) := by
  intro τ hτ
  have hscale : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  obtain ⟨c, N', hc, hflat'⟩ := hflat 0 (le_refl 0)
  obtain ⟨C, N, M, hC, hN, hM, htail'⟩ := htail
  have hmeasK : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) :=
    measurable_Kaxis_Kfun ℓ d hd τ
  have hmeasA : Measurable (fun t : ℝ => Aexp G τ t) := by
    unfold Aexp; fun_prop
  constructor
  · -- analyticity
    have hlow : ContDiff ℝ ω (fun r : ℝ => ∫ t in (0:ℝ)..1,
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t *
          Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
      refine contDiff_omega_intervalIntegral_exp (B := c * (Work.Kernels.scale τ) ^ N')
        (mul_nonneg hc (Real.rpow_nonneg hscale.le _)) hmeasK.aestronglyMeasurable ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      have := hflat' τ t hτ ht.1 ht.2
      rwa [Real.rpow_zero, mul_one] at this
    have htrunc : ContDiff ℝ ω (fun r : ℝ => ∫ t in Set.Ici 1,
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t) *
          Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
      refine contDiff_omega_integral_Ici_exp (C := C * (Work.Kernels.scale τ) ^ N) (M := M)
        (mul_pos hC (Real.rpow_pos_of_pos hscale N)) hM
        (hmeasK.sub hmeasA).aestronglyMeasurable ?_
      filter_upwards [htail' τ hτ] with t ht
      exact ht
    have hl1 : ContDiff ℝ ω (fun s : ℝ => layerLow ℓ d τ s) := by
      simp only [layerLow]
      exact contDiff_omega_sinSq.mul hlow
    have hl2 : ContDiff ℝ ω (fun s : ℝ => layerTrunc G ℓ d τ s) := by
      simp only [layerTrunc]
      exact contDiff_omega_sinSq.mul htrunc
    have h3 : ContDiff ℝ ω (fun s : ℝ => highPart G τ s) := contDiff_omega_highPart G τ
    have hsum : ContDiff ℝ ω (fun s : ℝ =>
        layerLow ℓ d τ s + layerTrunc G ℓ d τ s + highPart G τ s) := (hl1.add hl2).add h3
    simpa only [paperLayer] using hsum
  · -- evenness
    intro s
    have hsqC : ((-s : ℝ) : ℂ)^2 = ((s : ℝ) : ℂ)^2 := by
      rw [Complex.ofReal_neg, neg_sq]
    have hsqR : (-s)^2 = s^2 := neg_sq s
    simp only [paperLayer, layerLow, layerTrunc, highPart, sinSq]
    rw [hsqC, hsqR]

end Work.Asymptotics
