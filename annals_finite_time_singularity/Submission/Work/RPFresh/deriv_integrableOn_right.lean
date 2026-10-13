import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.RPFresh.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.RPFresh

open MeasureTheory Set

/-- The arithmetic–geometric mean inequality `2 √(a b) ≤ a + b` for `a, b ≥ 0`. -/
private lemma two_mul_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have h1 : (0:ℝ) ≤ (Real.sqrt a - Real.sqrt b)^2 := sq_nonneg _
  have h2 : Real.sqrt a * Real.sqrt b = Real.sqrt (a*b) := (Real.sqrt_mul ha b).symm
  nlinarith [h1, Real.sq_sqrt ha, Real.sq_sqrt hb, h2]

/-- The weighted Cauchy–Schwarz/AM–GM pointwise bound: for `x > 0`, `p ∈ ℝ` and any `y`,
`|y| ≤ (x^{-p} y² + x^{p}) / 2`, i.e. `2 x^{-p/2} |y| · x^{p/2} ≤ x^{-p} y² + x^{p}`. -/
private lemma abs_le_half_rpow {x y p : ℝ} (hx : 0 < x) :
    |y| ≤ 1/2 * (x^(-p) * y^2) + 1/2 * x^p := by
  have hx0 : 0 ≤ x := le_of_lt hx
  have ha : 0 ≤ x^(-p) * y^2 := mul_nonneg (Real.rpow_nonneg hx0 _) (sq_nonneg y)
  have hb : 0 ≤ x^p := Real.rpow_nonneg hx0 _
  have hprod : x^(-p) * y^2 * x^p = y^2 := by
    have h1 : x^(-p) * x^p = 1 := by
      rw [← Real.rpow_add hx, show -p + p = 0 by ring, Real.rpow_zero]
    calc x^(-p) * y^2 * x^p = (x^(-p) * x^p) * y^2 := by ring
      _ = y^2 := by rw [h1, one_mul]
  have hAG := two_mul_sqrt_le ha hb
  have hs : Real.sqrt (x^(-p) * y^2 * x^p) = |y| := by
    rw [hprod, Real.sqrt_sq_eq_abs]
  rw [hs] at hAG
  linarith

theorem deriv_integrableOn_right (g : ℝ → ℝ) (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 (Real.pi/2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.RPFresh.sg θ * (deriv g θ)^2) (Set.Ioo 0 (Real.pi/2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    MeasureTheory.IntegrableOn (deriv g) (Set.Ioo θ (Real.pi/2)) := by
  have hsub : Set.Ioo θ (Real.pi/2) ⊆ Set.Ioo (0:ℝ) (Real.pi/2) :=
    Set.Ioo_subset_Ioo (le_of_lt hθ.1) le_rfl
  -- `deriv g` is continuous, hence a.e. strongly measurable, on `(θ, π/2)`.
  have hmeas : AEStronglyMeasurable (deriv g) (volume.restrict (Set.Ioo θ (Real.pi/2))) := by
    have h1 : ContinuousOn (derivWithin g (Set.Ioo 0 (Real.pi/2)))
        (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      hg.continuousOn_derivWithin isOpen_Ioo.uniqueDiffOn le_rfl
    have h2 : ContinuousOn (fun s => deriv g s) (Set.Ioo θ (Real.pi/2)) :=
      ContinuousOn.congr (h1.mono hsub)
        (fun x hx => (derivWithin_of_isOpen isOpen_Ioo (hsub hx)).symm)
    exact h2.aestronglyMeasurable measurableSet_Ioo
  -- The dominating function `(σ (g')² + sin(2·)^η)/2` is integrable on `(θ, π/2)`.
  have hdom : Integrable (fun s => 1/2 * (Work.FTS.EllipticEst.RPFresh.sg s * (deriv g s)^2)
        + 1/2 * (Real.sin (2*s))^Work.Spaces.eta)
      (volume.restrict (Set.Ioo θ (Real.pi/2))) := by
    have hA : Integrable (fun s => 1/2 * (Work.FTS.EllipticEst.RPFresh.sg s * (deriv g s)^2))
        (volume.restrict (Set.Ioo θ (Real.pi/2))) :=
      (hint.mono_set hsub).const_mul (1/2)
    have hB' : IntegrableOn (fun s => 1/2 * (Real.sin (2*s))^Work.Spaces.eta)
        (Set.Ioo θ (Real.pi/2)) := by
      have hc : Continuous (fun s : ℝ => 1/2 * (Real.sin (2*s))^Work.Spaces.eta) :=
        Continuous.const_mul
          ((Real.continuous_rpow_const Work.Spaces.eta_nonneg).comp (by fun_prop)) (1/2)
      refine IntegrableOn.of_bound ?_ hc.aestronglyMeasurable (1/2) ?_
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      · rw [ae_restrict_iff' measurableSet_Ioo]
        filter_upwards with s hs
        have hsin : 0 ≤ Real.sin (2*s) := le_of_lt (Real.sin_pos_of_pos_of_lt_pi
          (by linarith [hs.1, hθ.1]) (by linarith [hs.2, Real.pi_pos]))
        have h1 : Real.sin (2*s) ^ Work.Spaces.eta ≤ 1 :=
          Real.rpow_le_one hsin (Real.sin_le_one _) Work.Spaces.eta_nonneg
        have h0 : 0 ≤ Real.sin (2*s) ^ Work.Spaces.eta := Real.rpow_nonneg hsin _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2),
          abs_of_nonneg h0]
        linarith
    have hB : Integrable (fun s => 1/2 * (Real.sin (2*s))^Work.Spaces.eta)
        (volume.restrict (Set.Ioo θ (Real.pi/2))) := hB'
    exact hA.add hB
  -- `|g'| ≤ (σ (g')² + sin(2·)^η)/2` pointwise, and conclude by dominated integrability.
  refine hdom.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with s hs
  have hsin : 0 < Real.sin (2*s) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hs.1, hθ.1]) (by linarith [hs.2, Real.pi_pos])
  have hb := abs_le_half_rpow (x := Real.sin (2*s)) (y := deriv g s) (p := Work.Spaces.eta) hsin
  rw [Real.norm_eq_abs]
  calc |deriv g s| ≤ 1/2 * ((Real.sin (2*s))^(-(Work.Spaces.eta)) * (deriv g s)^2)
        + 1/2 * (Real.sin (2*s))^Work.Spaces.eta := hb
    _ = 1/2 * (Work.FTS.EllipticEst.RPFresh.sg s * (deriv g s)^2)
        + 1/2 * (Real.sin (2*s))^Work.Spaces.eta := by
          rw [Work.FTS.EllipticEst.RPFresh.sg_def]

end Work.RPFresh
