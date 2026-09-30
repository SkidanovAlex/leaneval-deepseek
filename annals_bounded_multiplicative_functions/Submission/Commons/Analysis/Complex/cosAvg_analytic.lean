import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cosine average of the real part of an analytic function

`Commons.Analysis.Complex.cosAvg_analytic` — if `F` is holomorphic on the closed disc of
radius `R > 0` centred at `a`, then

`∫₀^{2π} cos θ · Re(F(a + R e^{iθ})) dθ = π R Re(F'(a))`.

This is the Fourier-coefficient (`n = 1`) identity used in the Jensen–Carleman
computation (Heath-Brown 1992, Lemma 3.2).
-/

noncomputable section

open Complex MeasureTheory Metric Set Topology
open scoped Interval

namespace Commons.Analysis.Complex

/-! ## Pointwise complex-trigonometry -/

/-- `Re (g·e^{−iθ}) + Re (g·e^{iθ}) = 2 cos θ · Re g`. -/
private lemma re_mul_exp_sum (g : ℂ) (θ : ℝ) :
    (g * cexp (-(Complex.I * (θ : ℂ)))).re + (g * cexp (Complex.I * (θ : ℂ))).re =
      2 * Real.cos θ * g.re := by
  have hg : g = (g.re : ℂ) + (g.im : ℂ) * Complex.I := by
    rw [Complex.ext_iff]; simp
  rw [hg]
  have he1 : cexp (-(Complex.I * (θ : ℂ))) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    have hneg : -(Complex.I * (θ : ℂ)) = (-(θ : ℂ)) * Complex.I := by ring
    rw [hneg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have he2 : cexp (Complex.I * (θ : ℂ)) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    have hI : Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I := by ring
    rw [hI, Complex.exp_mul_I]
  rw [he1, he2]
  have hcosre : (Complex.cos (θ : ℂ)).re = Real.cos θ := by
    rw [← Complex.ofReal_cos, Complex.ofReal_re]
  simp [hcosre]
  ring

/-- `cos θ · Re g = (Re (g·e^{−iθ}) + Re (g·e^{iθ})) / 2`. -/
private lemma cos_mul_re_eq (g : ℂ) (θ : ℝ) :
    Real.cos θ * g.re = ((g * cexp (-(Complex.I * (θ : ℂ)))).re +
      (g * cexp (Complex.I * (θ : ℂ))).re) / 2 := by
  have h := re_mul_exp_sum g θ
  linarith

/-! ## Fourier coefficients of an analytic function on a circle -/

/-- `∫₀^{2π} F(a + R e^{iθ}) e^{−iθ} dθ = 2πR F'(a)`. -/
private lemma complexIntegral_exp_neg {a : ℂ} {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall a R)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        F (circleMap a R θ) * cexp (-(Complex.I * (θ : ℂ)))) =
      (((2 * Real.pi * R : ℝ) : ℂ) * deriv F a) := by
  have hdiffOn : DifferentiableOn ℂ F (Metric.closedBall a R) := by
    intro z hz
    exact (hF z hz).differentiableAt.differentiableWithinAt
  have hC : (∮ z in C(a, R), (1 / (z - a) ^ 2) • F z) =
      ((2 * (Real.pi : ℂ) * Complex.I) : ℂ) • deriv F a := by
    simpa using (DifferentiableOn.deriv_eq_smul_circleIntegral (c := a) (f := F) (R := R) hR hdiffOn)
  let J : ℂ := ∫ θ in (0 : ℝ)..(2 * Real.pi),
        F (circleMap a R θ) * cexp (-(Complex.I * (θ : ℂ)))
  have h_expand : (∮ z in C(a, R), (1 / (z - a) ^ 2) • F z) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (deriv (circleMap a R) θ) • ((1 / (circleMap a R θ - a) ^ 2) • F (circleMap a R θ)) := by
    rfl
  have h_simpl : (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (deriv (circleMap a R) θ) • ((1 / (circleMap a R θ - a) ^ 2) • F (circleMap a R θ))) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
          ((Complex.I : ℂ) / (R : ℂ)) * (F (circleMap a R θ) * cexp (-(Complex.I * (θ : ℂ)))) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change deriv (circleMap a R) θ • ((1 / (circleMap a R θ - a) ^ 2) • F (circleMap a R θ)) =
      ((Complex.I : ℂ) / (R : ℂ)) * (F (circleMap a R θ) * cexp (-(Complex.I * (θ : ℂ))))
    rw [deriv_circleMap, circleMap_sub_center, circleMap_zero]
    simp only [smul_eq_mul]
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
    have hexp : exp (↑θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp [hR', hexp]
    ring_nf
    have hprod : cexp (↑θ * Complex.I) * cexp (-(↑θ * Complex.I)) = 1 := by
      rw [← Complex.exp_add]
      have : ↑θ * Complex.I + -(↑θ * Complex.I) = 0 := by ring
      rw [this, Complex.exp_zero]
    symm
    calc
      cexp (↑θ * Complex.I) * F (circleMap a R θ) * cexp (-(↑θ * Complex.I))
          = F (circleMap a R θ) * (cexp (↑θ * Complex.I) * cexp (-(↑θ * Complex.I))) := by ring
      _ = F (circleMap a R θ) := by rw [hprod, mul_one]
  have hConv : (∮ z in C(a, R), (1 / (z - a) ^ 2) • F z) = ((Complex.I : ℂ) / (R : ℂ)) * J := by
    rw [h_expand, h_simpl]
    exact intervalIntegral.integral_const_mul ((Complex.I : ℂ) / (R : ℂ))
      (fun θ : ℝ => F (circleMap a R θ) * cexp (-(Complex.I * (θ : ℂ))))
  have hEq : ((Complex.I : ℂ) / (R : ℂ)) * J = ((2 * (Real.pi : ℂ) * Complex.I) : ℂ) * deriv F a := by
    rw [← hConv]
    simpa [smul_eq_mul] using hC
  have hI : (Complex.I : ℂ) ≠ 0 := by simp
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
  have hJ : J = ((2 * Real.pi * R : ℝ) : ℂ) * deriv F a := by
    calc
      J = (R : ℂ) / Complex.I * (((Complex.I : ℂ) / (R : ℂ)) * J) := by field_simp [hI, hRc]
      _ = (R : ℂ) / Complex.I * ((2 * (Real.pi : ℂ) * Complex.I) * deriv F a) := by rw [hEq]
      _ = ((2 * Real.pi * R : ℝ) : ℂ) * deriv F a := by
        have hscalar : (R : ℂ) / Complex.I * ((2 * (Real.pi : ℂ) * Complex.I) : ℂ) =
            ((2 * Real.pi * R : ℝ) : ℂ) := by
          field_simp [hI]
          norm_num
          ring
        calc
          (R : ℂ) / Complex.I * (((2 * (Real.pi : ℂ) * Complex.I) : ℂ) * deriv F a)
              = ((R : ℂ) / Complex.I * ((2 * (Real.pi : ℂ) * Complex.I) : ℂ)) * deriv F a := by
            ring
          _ = ((2 * Real.pi * R : ℝ) : ℂ) * deriv F a := by rw [hscalar]
  exact hJ

/-- `∫₀^{2π} F(a + R e^{iθ}) e^{iθ} dθ = 0`. -/
private lemma complexIntegral_exp_pos {a : ℂ} {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall a R)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        F (circleMap a R θ) * cexp (Complex.I * (θ : ℂ))) = 0 := by
  have hcF : ContinuousOn F (Metric.closedBall a R) := hF.continuousOn
  have hdiffAt : ∀ z ∈ Metric.ball a R, DifferentiableAt ℂ F z := fun z hz =>
    (hF z (Metric.ball_subset_closedBall hz)).differentiableAt
  have hG0 : (∮ z in C(a, R), (1 / ((R : ℂ) * Complex.I)) * F z) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
      (f := fun z => (1 / ((R : ℂ) * Complex.I)) * F z) (c := a) (s := ∅)
      Set.countable_empty ?_ ?_
    · intro z hz
      exact (hcF z hz).const_mul (1 / ((R : ℂ) * Complex.I))
    · intro z hz
      exact (hdiffAt z hz.1).const_mul (1 / ((R : ℂ) * Complex.I))
  have h_expand : (∮ z in C(a, R), (1 / ((R : ℂ) * Complex.I)) * F z) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (deriv (circleMap a R) θ) • ((1 / ((R : ℂ) * Complex.I)) * F (circleMap a R θ)) := by
    rfl
  have h_simpl : (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (deriv (circleMap a R) θ) • ((1 / ((R : ℂ) * Complex.I)) * F (circleMap a R θ))) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), F (circleMap a R θ) * cexp (Complex.I * (θ : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change deriv (circleMap a R) θ • ((1 / ((R : ℂ) * Complex.I)) * F (circleMap a R θ)) =
      F (circleMap a R θ) * cexp (Complex.I * (θ : ℂ))
    rw [deriv_circleMap, circleMap_zero]
    simp only [smul_eq_mul]
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
    have hI : (Complex.I : ℂ) ≠ 0 := by simp
    field_simp [hR', hI]
  have hConv : (∮ z in C(a, R), (1 / ((R : ℂ) * Complex.I)) * F z) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), F (circleMap a R θ) * cexp (Complex.I * (θ : ℂ)) := by
    rw [h_expand, h_simpl]
  rw [← hConv]
  exact hG0


/-- The real part commutes with interval integration. -/
private lemma intervalIntegral_re {a b : ℝ} (f : ℝ → ℂ) (hf : IntervalIntegrable f volume a b) :
    (∫ θ in a..b, (f θ).re) = (∫ θ in a..b, f θ).re := by
  simpa [Complex.reCLM_apply] using
    (ContinuousLinearMap.intervalIntegral_comp_comm (L := Complex.reCLM) hf)

/-! ## The cosine average identity -/

/-- If `F` is holomorphic on the closed disc of radius `R > 0` around `a`, then
`∫₀^{2π} cos θ · Re(F(a + R e^{iθ})) dθ = π R Re(F'(a))`. -/
theorem cosAvg_analytic {a : ℂ} {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall a R)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ * Complex.re (F (circleMap a R θ))) =
      Real.pi * R * Complex.re (deriv F a) := by
  let fneg : ℝ → ℂ := fun θ => F (circleMap a R θ) * cexp (-(Complex.I * (θ : ℂ)))
  let fpos : ℝ → ℂ := fun θ => F (circleMap a R θ) * cexp (Complex.I * (θ : ℂ))
  have hcontG : Continuous (fun θ : ℝ => F (circleMap a R θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact ContinuousAt.comp
      ((hF (circleMap a R θ) (circleMap_mem_closedBall a hR.le θ)).continuousAt)
      (Continuous.continuousAt (x := θ) (continuous_circleMap a R))
  have hcontEneg : Continuous (fun θ : ℝ => cexp (-(Complex.I * (θ : ℂ)))) := by fun_prop
  have hcontEpos : Continuous (fun θ : ℝ => cexp (Complex.I * (θ : ℂ))) := by fun_prop
  have hIntFneg : IntervalIntegrable fneg volume 0 (2 * Real.pi) := by
    dsimp [fneg]
    exact (Continuous.mul hcontG hcontEneg).intervalIntegrable 0 (2 * Real.pi)
  have hIntFpos : IntervalIntegrable fpos volume 0 (2 * Real.pi) := by
    dsimp [fpos]
    exact (Continuous.mul hcontG hcontEpos).intervalIntegrable 0 (2 * Real.pi)
  have hIntRNeg : IntervalIntegrable (fun θ : ℝ => (fneg θ).re) volume 0 (2 * Real.pi) := by
    exact (Complex.continuous_re.comp (by dsimp [fneg]; exact Continuous.mul hcontG hcontEneg)).intervalIntegrable 0 (2 * Real.pi)
  have hIntRPos : IntervalIntegrable (fun θ : ℝ => (fpos θ).re) volume 0 (2 * Real.pi) := by
    exact (Complex.continuous_re.comp (by dsimp [fpos]; exact Continuous.mul hcontG hcontEpos)).intervalIntegrable 0 (2 * Real.pi)
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ * Complex.re (F (circleMap a R θ)))
        = ∫ θ in (0 : ℝ)..(2 * Real.pi), (((fneg θ).re + (fpos θ).re) / 2) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      change Real.cos θ * Complex.re (F (circleMap a R θ)) = ((fneg θ).re + (fpos θ).re) / 2
      rw [show (fneg θ) = F (circleMap a R θ) * cexp (-(Complex.I * (θ : ℂ))) by rfl,
          show (fpos θ) = F (circleMap a R θ) * cexp (Complex.I * (θ : ℂ)) by rfl]
      exact cos_mul_re_eq (F (circleMap a R θ)) θ
    _ = ((∫ θ in (0 : ℝ)..(2 * Real.pi), (fneg θ).re + (fpos θ).re) / 2) := by
      rw [intervalIntegral.integral_div (2 : ℝ)]
    _ = (((∫ θ in (0 : ℝ)..(2 * Real.pi), (fneg θ).re) +
        (∫ θ in (0 : ℝ)..(2 * Real.pi), (fpos θ).re)) / 2) := by
      congr 1
      exact intervalIntegral.integral_add hIntRNeg hIntRPos
    _ = (((∫ θ in (0 : ℝ)..(2 * Real.pi), fneg θ).re +
        (∫ θ in (0 : ℝ)..(2 * Real.pi), fpos θ).re) / 2) := by
      congr 1
      rw [intervalIntegral_re fneg hIntFneg, intervalIntegral_re fpos hIntFpos]
    _ = (((((2 * Real.pi * R : ℝ) : ℂ) * deriv F a).re + (0 : ℂ).re) / 2) := by
      rw [complexIntegral_exp_neg hR hF, complexIntegral_exp_pos hR hF]
    _ = Real.pi * R * Complex.re (deriv F a) := by
      simp
      ring

end Commons.Analysis.Complex