import Mathlib
import Submission.Work.CKFinal.LineDecay.analyticOnNhd_laplace_interval
import Submission.Work.Asymptotics.differentiableAt_integral_Ioo

namespace Work.CKFinal.LineDecay

open MeasureTheory Filter
open scoped Topology

/-- **Analyticity of an affine-exponential parametric integral over a compact interval.**

If `g : ℝ → ℂ` is continuous on `(a,b)` and bounded there, then for any constants `c d : ℂ`
the integral `z ↦ ∫_a^b g t * exp (z * (c * t + d)) dt` is entire.

This is the variant of `analyticOnNhd_laplace_interval` needed for the two horizontal segments of
the contour shift, where the exponential is `exp (I z (x + i)) = exp (z * (I * x - 1))`.

Route: at a point `z₀` the integrand `F z u = g u * exp (z * (c*u + d))` is holomorphic in `z`
and bounded on the ball of radius `1` around `z₀` by `M * exp ((‖z₀‖+1) * (‖c‖ * max |a| |b| + ‖d‖))`,
where `M` bounds `‖g‖` on `(a,b)`; a.e. strong measurability on `volume.restrict (Set.Ioo a b)`
follows from continuity of `g`.  Then `Work.Asymptotics.differentiableAt_integral_Ioo` (module
`Submission.Work.Asymptotics.differentiableAt_integral_Ioo`) gives `DifferentiableAt` of
`z ↦ ∫ u in Set.Ioo a b, F z u` at `z₀`, and the interval integral is transported as in
`analyticOnNhd_laplace_interval` (`intervalIntegral.integral_of_le` plus a.e. equality of
`Set.Ioc a b` and `Set.Ioo a b`). -/
theorem analyticOnNhd_laplace_interval_affine {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Ioo a b))
    (hbdd : ∃ M : ℝ, ∀ t ∈ Set.Ioo a b, ‖g t‖ ≤ M) (c d : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in a..b,
        g t * Complex.exp (z * (c * (t : ℂ) + d))) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  intro z₀
  -- A nonnegative bound for `g` on the open interval.
  obtain ⟨M₀, hM₀⟩ := hbdd
  set M : ℝ := max M₀ 0 with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hMb : ∀ t ∈ Set.Ioo a b, ‖g t‖ ≤ M := by
    intro t ht
    rw [hMdef]
    exact le_trans (hM₀ t ht) (le_max_left _ _)
  -- The scale of the interval.
  set P : ℝ := max |a| |b| with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; exact le_trans (abs_nonneg a) (le_max_left _ _)
  have haP : |a| ≤ P := by rw [hPdef]; exact le_max_left _ _
  have hbP : |b| ≤ P := by rw [hPdef]; exact le_max_right _ _
  -- The value bound constant.
  set C : ℝ := M * Real.exp ((‖z₀‖ + 1) * (‖c‖ * P + ‖d‖)) with hCdef
  -- Transport the interval integral to the set integral over `Ioo a b`.
  have hEq : (fun z : ℂ => ∫ t in a..b, g t * Complex.exp (z * (c * (t : ℂ) + d)))
      = fun z : ℂ => ∫ u in Set.Ioo a b, g u * Complex.exp (z * (c * (u : ℂ) + d)) := by
    funext z
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b) (μ := volume)).symm
  rw [hEq]
  refine Work.Asymptotics.differentiableAt_integral_Ioo (a := a) (b := b) (x₀ := z₀)
    (ρ := 1) (C := C) one_pos ?_ ?_ ?_
  · -- Value bound on the ball of radius `1`.
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u hu z hz
    have hz1 : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have hzd : ‖z - z₀‖ < 1 := by rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ 1 + ‖z₀‖ := by linarith
        _ = ‖z₀‖ + 1 := by ring
    have huP : |u| ≤ P := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h1 : -P ≤ -|a| := by linarith [haP]
        have h2 : -|a| ≤ a := neg_abs_le a
        linarith [hu.1]
      · have h1 : |b| ≤ P := hbP
        have h2 : b ≤ |b| := le_abs_self b
        linarith [hu.2]
    -- Norm bound on the affine part of the exponent.
    have harg : ‖c * (u : ℂ) + d‖ ≤ ‖c‖ * P + ‖d‖ := by
      calc ‖c * (u : ℂ) + d‖ ≤ ‖c * (u : ℂ)‖ + ‖d‖ := norm_add_le _ _
        _ = ‖c‖ * ‖(u : ℂ)‖ + ‖d‖ := by rw [norm_mul]
        _ = ‖c‖ * |u| + ‖d‖ := by simp
        _ ≤ ‖c‖ * P + ‖d‖ := by
            have := mul_le_mul_of_nonneg_left huP (norm_nonneg c)
            linarith
    have hzP : ‖z * (c * (u : ℂ) + d)‖ ≤ (‖z₀‖ + 1) * (‖c‖ * P + ‖d‖) := by
      rw [norm_mul]
      exact mul_le_mul hz1 harg (norm_nonneg _) (by linarith [norm_nonneg z₀])
    have hexp : Real.exp ((z * (c * (u : ℂ) + d)).re) ≤
        Real.exp ((‖z₀‖ + 1) * (‖c‖ * P + ‖d‖)) := by
      rw [Real.exp_le_exp]
      exact le_trans (Complex.re_le_norm _) hzP
    rw [norm_mul, Complex.norm_exp]
    calc ‖g u‖ * Real.exp ((z * (c * (u : ℂ) + d)).re)
        ≤ M * Real.exp ((‖z₀‖ + 1) * (‖c‖ * P + ‖d‖)) :=
          mul_le_mul (hMb u hu) hexp (Real.exp_nonneg _) hMnn
      _ = C := by rw [hCdef]
  · -- Holomorphy in the parameter for every fixed `u`.
    filter_upwards with u
    intro z _
    have h1 : DifferentiableAt ℂ (fun z' : ℂ => c * (u : ℂ) + d) z :=
      differentiableAt_const _
    have h2 : DifferentiableAt ℂ (fun z' : ℂ => z' * (c * (u : ℂ) + d)) z :=
      differentiableAt_id.mul h1
    exact (h2.cexp).const_mul (g u)
  · -- A.e. strong measurability for `z` near `z₀`.
    refine Filter.Eventually.of_forall (fun z => ?_)
    have hcont : Continuous (fun u : ℝ => Complex.exp (z * (c * (u : ℂ) + d))) :=
      Complex.continuous_exp.comp
        (continuous_const.mul ((continuous_const.mul Complex.continuous_ofReal).add continuous_const))
    exact (hg.aestronglyMeasurable measurableSet_Ioo).mul hcont.aestronglyMeasurable

end Work.CKFinal.LineDecay
