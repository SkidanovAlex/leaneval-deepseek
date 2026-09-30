import Mathlib
import Submission.Work.BMF.stepKern_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the truncated Perron step kernel in the real variable

`Commons.Analysis.Complex.stepKern σ T z` is the truncated Perron step kernel
`(1/2π) ∫_{-T}^{T} e^{(σ+it) log z} / (σ + it) dt`.  As a function of the real variable `z`
it is continuous on `(0, ∞)`: on that half line the (non-continuous) `Complex.log` agrees with
the continuous real logarithm, `σ + i t ≠ 0`, and the integrand is dominated on the compact
interval `[-T, T]`, so the parametric integral is continuous.
-/

namespace Work.BMF

open Complex MeasureTheory intervalIntegral Filter
open scoped BigOperators Topology

theorem stepKern_continuousOn (σ T : ℝ) (hσ : 0 < σ) :
    ContinuousOn (fun z : ℝ => Commons.Analysis.Complex.stepKern σ T z) (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  -- The denominator `σ + i t` never vanishes since `σ > 0`.
  have hne : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  -- Joint continuity of the integrand, with `z` ranging over the subtype `(0, ∞)` so that
  -- `Real.log (z : ℝ)` is continuous.
  have hcont : Continuous (Function.uncurry (fun (z : ↥(Set.Ioi (0 : ℝ))) (t : ℝ) =>
      Complex.exp (((σ : ℂ) + (t : ℂ) * Complex.I) * ((Real.log (z : ℝ) : ℝ) : ℂ))
        / ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
    show Continuous (fun p : ↥(Set.Ioi (0 : ℝ)) × ℝ =>
      Complex.exp (((σ : ℂ) + (p.2 : ℂ) * Complex.I) * ((Real.log (p.1 : ℝ) : ℝ) : ℂ))
        / ((σ : ℂ) + (p.2 : ℂ) * Complex.I))
    have hlog : Continuous fun p : ↥(Set.Ioi (0 : ℝ)) × ℝ => ((Real.log (p.1 : ℝ) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((Real.continuousOn_log.mono (by intro x hx; simp at hx ⊢; linarith)).comp_continuous
          (continuous_subtype_val.comp continuous_fst) (fun p => p.1.2))
    have hlin : Continuous fun p : ↥(Set.Ioi (0 : ℝ)) × ℝ => (σ : ℂ) + (p.2 : ℂ) * Complex.I := by
      continuity
    exact (Complex.continuous_exp.comp (hlin.mul hlog)).div hlin (fun p => hne p.2)
  -- Parametric integral over the compact interval `[-T, T]`.
  have hint : Continuous (fun z : ↥(Set.Ioi (0 : ℝ)) => ∫ t in (-T)..T,
      Complex.exp (((σ : ℂ) + (t : ℂ) * Complex.I) * ((Real.log (z : ℝ) : ℝ) : ℂ))
        / ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont (-T) T
  have hfinal : Continuous (fun z : ↥(Set.Ioi (0 : ℝ)) =>
      (1 / (2 * Real.pi)) * ∫ t in (-T)..T,
        Complex.exp (((σ : ℂ) + (t : ℂ) * Complex.I) * ((Real.log (z : ℝ) : ℝ) : ℂ))
          / ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    hint.const_mul (1 / (2 * Real.pi))
  -- Identify the restriction of `stepKern` with the continuous function above, using
  -- `Complex.log (z : ℂ) = (Real.log z : ℂ)` for `z > 0`.
  have hEq : (Set.Ioi (0 : ℝ)).domRestrict (fun z : ℝ => Commons.Analysis.Complex.stepKern σ T z)
      = fun z : ↥(Set.Ioi (0 : ℝ)) =>
          (1 / (2 * Real.pi)) * ∫ t in (-T)..T,
            Complex.exp (((σ : ℂ) + (t : ℂ) * Complex.I) * ((Real.log (z : ℝ) : ℝ) : ℂ))
              / ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    funext z
    rw [Set.domRestrict_apply, Commons.Analysis.Complex.stepKern]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Complex.ofReal_log (le_of_lt z.2)]
  rw [hEq]
  exact hfinal

end Work.BMF
