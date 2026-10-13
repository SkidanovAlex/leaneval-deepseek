import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.CoreResiduals.BiotSavart.radial_rpow_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

/-- `‖·‖ ^ s` is integrable on the complement of a ball of radius `R > 0` in `ℝ³`,
provided `s < -3` (the threshold at which `‖·‖^s` is integrable at infinity in
dimension `3`).  The proof decomposes the integral radially: by
`integrable_fun_norm_addHaar` integrability of `(Ici R).indicator (·^s) ∘ ‖·‖` is
equivalent to integrability of `y ↦ y ^ 2 * y ^ s = y ^ (s + 2)` on `(R, ∞)`, which
holds exactly when `s + 2 < -1`, i.e. `s < -3`. -/
lemma integrableOn_compl_ball_norm_rpow (s : ℝ) (hs : s < -3) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) (Metric.ball (0 : Work.LWP.R3) R)ᶜ
      volume := by
  have hdim : Module.finrank ℝ Work.LWP.R3 = 3 := by
    simp only [Work.LWP.R3]; exact finrank_euclideanSpace_fin
  rw [← MeasureTheory.integrable_indicator_iff measurableSet_ball.compl]
  -- the indicator of the complement of the ball is the radial profile `(Ici R).indicator (·^s)`
  have hpt : (Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)
      = fun x : Work.LWP.R3 => (Set.Ici R).indicator (fun t : ℝ => t ^ s) ‖x‖ := by
    funext y
    by_cases hy : y ∈ Metric.ball (0 : Work.LWP.R3) R
    · have h1 : ¬ (R ≤ ‖y‖) := by
        rw [Metric.mem_ball, dist_zero_right] at hy
        exact not_le.mpr hy
      rw [Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using h1)]
    · have h1 : R ≤ ‖y‖ := by
        rw [Metric.mem_ball, dist_zero_right] at hy
        exact not_lt.mp hy
      rw [Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using h1)]
  rw [hpt]
  rw [MeasureTheory.integrable_fun_norm_addHaar (μ := (volume : Measure Work.LWP.R3))
      (f := (Set.Ici R).indicator (fun t : ℝ => t ^ s)), hdim]
  norm_num
  -- the radial weight `y ^ 2 * y ^ s` is the indicator of `Ici R` of `y ^ (s + 2)`
  have hfun : (fun y : ℝ => y ^ (2:ℕ) * (Set.Ici R).indicator (fun t : ℝ => t ^ s) y)
      = (Set.Ici R).indicator (fun y : ℝ => y ^ (s + 2)) := by
    funext y
    by_cases hy : R ≤ y
    · have hy0 : (0:ℝ) < y := lt_of_lt_of_le hR hy
      rw [Set.indicator_of_mem (Set.mem_Ici.mpr hy), Set.indicator_of_mem (Set.mem_Ici.mpr hy)]
      rw [← Real.rpow_natCast y 2, ← Real.rpow_add hy0 ((2:ℕ):ℝ) s]
      congr 1
      ring
    · have hy' : y ∉ Set.Ici R := fun h => hy (Set.mem_Ici.mp h)
      rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy', mul_zero]
  rw [hfun]
  rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioi]
  rw [Set.indicator_indicator]
  rw [show Set.Ioi (0:ℝ) ∩ Set.Ici R = Set.Ici R from by
        rw [Set.inter_eq_right]; intro x hx; exact lt_of_lt_of_le hR hx]
  rw [MeasureTheory.integrable_indicator_iff measurableSet_Ici]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact (integrableOn_Ioi_rpow_iff hR).mpr (by linarith)

/-- The Bochner integral of the radial power over the exterior of a ball of `ℝ³`:
`∫_{‖y‖>R} ‖y‖^s dy = 4π R^{s+3}/(-(s+3))` for `s < -3` and `R > 0`.
This is the `s < -3` companion of `radial_rpow_integral` (which covers `s > -3` on a
ball); it is obtained by the polar decomposition `integral_fun_norm_addHaar` in
dimension `3` together with the one-dimensional integral `∫_R^∞ y^{s+2} dy =
-R^{s+3}/(s+3)`. -/
lemma integral_compl_ball_norm_rpow (s : ℝ) (hs : s < -3) (R : ℝ) (hR : 0 < R) :
    ∫ y in (Metric.ball (0 : Work.LWP.R3) R)ᶜ, (‖y‖ : ℝ) ^ s
      = 4 * Real.pi * R ^ (s + 3) / (-(s + 3)) := by
  have hfin : Module.finrank ℝ Work.LWP.R3 = 3 := by
    simp only [Work.LWP.R3]; exact finrank_euclideanSpace_fin
  -- volume of the unit ball of `ℝ³`
  have hvol : volume.real (Metric.ball (0 : Work.LWP.R3) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three]
    rw [show ENNReal.ofReal (1:ℝ) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)
          = ENNReal.ofReal (Real.pi * 4 / 3) by simp]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  set f : ℝ → ℝ := (Set.Ici R).indicator (fun t : ℝ => t ^ s) with hf
  -- step 1: the exterior integral is the full-space integral of the radial profile `f ∘ ‖·‖`
  have hpt : (Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)
      = fun x : Work.LWP.R3 => f ‖x‖ := by
    funext y
    rw [hf]
    by_cases hy : y ∈ Metric.ball (0 : Work.LWP.R3) R
    · have h1 : ¬ (R ≤ ‖y‖) := by
        rw [Metric.mem_ball, dist_zero_right] at hy
        exact not_le.mpr hy
      rw [Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using h1)]
    · have h1 : R ≤ ‖y‖ := by
        rw [Metric.mem_ball, dist_zero_right] at hy
        exact not_lt.mp hy
      rw [Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using h1)]
  -- step 2: the one-dimensional radial integral `∫_0^∞ y^2 * f y dy = -R^{s+3}/(s+3)`
  have hJ : ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ Work.LWP.R3 - 1) • f y
      = -(R ^ (s + 3)) / (s + 3) := by
    rw [hfin]
    simp only [hf, Nat.reduceSub]
    have key : (fun y : ℝ => y ^ (2:ℕ) • (Set.Ici R).indicator (fun t : ℝ => t ^ s) y)
        = (Set.Ici R).indicator (fun y : ℝ => y ^ (s + 2)) := by
      funext y
      by_cases hy : R ≤ y
      · have hy0 : (0:ℝ) < y := lt_of_lt_of_le hR hy
        rw [Set.indicator_of_mem (Set.mem_Ici.mpr hy)]
        rw [Set.indicator_of_mem (Set.mem_Ici.mpr hy)]
        rw [smul_eq_mul, ← Real.rpow_natCast y 2, ← Real.rpow_add hy0 ((2:ℕ):ℝ) s]
        congr 1
        ring
      · have hy' : y ∉ Set.Ici R := fun h => hy (Set.mem_Ici.mp h)
        rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy', smul_zero]
    rw [key]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    rw [Set.indicator_indicator]
    rw [MeasureTheory.integral_indicator (measurableSet_Ioi.inter measurableSet_Ici)]
    rw [show Set.Ioi (0:ℝ) ∩ Set.Ici R = Set.Ici R from by
          rw [Set.inter_eq_right]; intro x hx; exact lt_of_lt_of_le hR hx]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    rw [integral_Ioi_rpow_of_lt (by linarith : s + 2 < -1) hR]
    rw [show s + 2 + 1 = s + 3 by ring]
  -- step 3: assemble
  rw [← MeasureTheory.integral_indicator measurableSet_ball.compl]
  rw [hpt]
  rw [MeasureTheory.integral_fun_norm_addHaar volume f, hJ, hfin, hvol]
  have hsz : s + 3 ≠ 0 := by linarith
  rw [nsmul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- The `lintegral` form of the radial power integral over the exterior of a ball of `ℝ³`:
`∫⁻_{‖y‖>R} ‖y‖^s = 4π R^{s+3}/(-(s+3))` for `s < -3`.  Since the integrand is
non-negative and integrable on the exterior (`integrableOn_compl_ball_norm_rpow`), the
Lebesgue integral `∫⁻` of `ENNReal.ofReal` of it agrees with `ENNReal.ofReal` of the
Bochner integral `∫`, to which `integral_compl_ball_norm_rpow` applies. -/
theorem lintegral_exterior_norm_rpow (s : ℝ) (hs : s < -3) (R : ℝ) (hR : 0 < R) :
    ∫⁻ y in (Metric.ball (0 : Work.LWP.R3) R)ᶜ, ENNReal.ofReal (‖y‖ ^ s)
      = ENNReal.ofReal (4 * Real.pi * R ^ (s + 3) / (-(s + 3))) := by
  have hint : IntegrableOn (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)
      (Metric.ball (0 : Work.LWP.R3) R)ᶜ volume :=
    integrableOn_compl_ball_norm_rpow s hs R hR
  have hInt : Integrable ((Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
      (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)) volume :=
    (integrable_indicator_iff measurableSet_ball.compl).mpr hint
  have hnn : 0 ≤ᵐ[volume] (Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
      (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) := by
    classical
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Set.indicator_apply, Pi.zero_apply]
    split_ifs with hy
    · exact Real.rpow_nonneg (norm_nonneg y) s
    · exact le_rfl
  have hcongr :
      ∫⁻ y, (Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
          (fun y : Work.LWP.R3 => ENNReal.ofReal ((‖y‖ : ℝ) ^ s)) y
        = ∫⁻ y, ENNReal.ofReal ((Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
            (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y) := by
    classical
    refine lintegral_congr (fun y => ?_)
    by_cases hy : y ∈ (Metric.ball (0 : Work.LWP.R3) R)ᶜ
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, ENNReal.ofReal_zero]
  have hofreal : ENNReal.ofReal (∫ y, (Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
        (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y)
      = ∫⁻ y, ENNReal.ofReal ((Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
        (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y) :=
    ofReal_integral_eq_lintegral_ofReal hInt hnn
  rw [← lintegral_indicator measurableSet_ball.compl
    (fun y : Work.LWP.R3 => ENNReal.ofReal ((‖y‖ : ℝ) ^ s))]
  rw [hcongr, ← hofreal]
  rw [integral_indicator measurableSet_ball.compl]
  rw [integral_compl_ball_norm_rpow s hs R hR]

end Work.CoreResiduals.BiotSavart
