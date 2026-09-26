import Mathlib
import Submission.Work.CKFinal.LineDecay.LamDefs
import Submission.Work.Asymptotics.differentiableAt_integral_Ioo

namespace Work.CKFinal.LineDecay

open MeasureTheory Filter
open scoped Topology

/-- **Analyticity of a Laplace-type integral over a compact interval.**

If `g : ℝ → ℂ` is continuous on the open interval `(a,b)` and bounded there, then
`z ↦ ∫_a^b g t * exp (-(z * t)) dt` is entire.

Route: at a point `z₀`, the integrand `F z u = g u * exp (-(z*u))` is holomorphic in `z` and, for
`z` in the ball of radius `1` around `z₀`, bounded by `M * exp ((‖z₀‖+1) * max |a| |b|)` where `M`
bounds `‖g‖` on `(a,b)`; a.e. strong measurability on `volume.restrict (Set.Ioo a b)` follows from
`ContinuousOn g (Set.Ioo a b)`.  The workspace engine
`Work.Asymptotics.differentiableAt_integral_Ioo` (module
`Submission.Work.Asymptotics.differentiableAt_integral_Ioo`) then gives `DifferentiableAt` of
`z ↦ ∫ u in Set.Ioo a b, F z u` at `z₀`; transport back with
`intervalIntegral.integral_of_le` and a.e. equality of `Set.Ioc a b` and `Set.Ioo a b`. -/
theorem analyticOnNhd_laplace_interval {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Ioo a b))
    (hbdd : ∃ M : ℝ, ∀ t ∈ Set.Ioo a b, ‖g t‖ ≤ M) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in a..b, g t * Complex.exp (-(z * (t : ℂ)))) Set.univ := by
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
  set C : ℝ := M * Real.exp ((‖z₀‖ + 1) * P) with hCdef
  -- Transport the interval integral to the set integral over `Ioo a b`.
  have hEq : (fun z : ℂ => ∫ t in a..b, g t * Complex.exp (-(z * (t : ℂ))))
      = fun z : ℂ => ∫ u in Set.Ioo a b, g u * Complex.exp (-(z * (u : ℂ))) := by
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
    have hexp : Real.exp (-(z.re * u)) ≤ Real.exp ((‖z₀‖ + 1) * P) := by
      rw [Real.exp_le_exp]
      have h1 : -(z.re * u) ≤ |z.re * u| := neg_le_abs _
      rw [abs_mul] at h1
      have h2 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have h3 : |z.re| * |u| ≤ ‖z‖ * P :=
        mul_le_mul h2 huP (abs_nonneg u) (norm_nonneg z)
      have h4 : ‖z‖ * P ≤ (‖z₀‖ + 1) * P := mul_le_mul_of_nonneg_right hz1 hPnn
      linarith
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(z * (u : ℂ))).re = -(z.re * u) := by
      rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hre]
    calc ‖g u‖ * Real.exp (-(z.re * u))
        ≤ M * Real.exp ((‖z₀‖ + 1) * P) :=
          mul_le_mul (hMb u hu) hexp (Real.exp_nonneg _) hMnn
      _ = C := by rw [hCdef]
  · -- Holomorphy in the parameter for every fixed `u`.
    filter_upwards with u
    intro z _
    have h1 : DifferentiableAt ℂ (fun z' : ℂ => z' * (u : ℂ)) z :=
      differentiableAt_id.mul_const _
    have h2 : DifferentiableAt ℂ (fun z' : ℂ => -(z' * (u : ℂ))) z := h1.neg
    have h3 : DifferentiableAt ℂ (fun z' : ℂ => Complex.exp (-(z' * (u : ℂ)))) z := h2.cexp
    exact h3.const_mul (g u)
  · -- A.e. strong measurability for `z` near `z₀`.
    refine Filter.Eventually.of_forall (fun z => ?_)
    have hcont : Continuous (fun u : ℝ => Complex.exp (-(z * (u : ℂ)))) :=
      Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)
    exact (hg.aestronglyMeasurable measurableSet_Ioo).mul hcont.aestronglyMeasurable

end Work.CKFinal.LineDecay
