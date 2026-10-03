import Mathlib
import Submission.Work.FIArea2.SevenSix.one_dim_scale
import Submission.Work.FIArea2.SevenSix.inner_subst
import Submission.Work.FIArea2.SevenSix.quadrant_double_eq
import Submission.Work.FIArea2.SevenSix.quad_integrable

namespace Work.FIArea2

open scoped BigOperators

open MeasureTheory

/-- Fubini for iterated set integrals over the quadrant `Ioi 0 ×ˢ Ioi 0` (the two coordinates
carry the same measure, so swapping the order of integration is legitimate). -/
theorem setIntegral_prod_swap_Ioi {F : ℝ → ℝ → ℝ}
    (hF : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi 0)) :
    ∫ w in Set.Ioi 0, ∫ r in Set.Ioi 0, F r w = ∫ r in Set.Ioi 0, ∫ w in Set.Ioi 0, F r w := by
  have hF' : Integrable (fun p : ℝ × ℝ => F p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hF
  have hF'' : Integrable (fun p : ℝ × ℝ => F p.2 p.1)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    simpa [Function.comp_def, Prod.swap] using hF'.swap
  exact integral_integral_swap (f := fun a b => F b a) hF''

/-- `1/√x = x^{-1/2}` for `x > 0`, with the exponent written exactly as it appears in (7.6). -/
lemma one_div_sqrt_eq_rpow_neg_half (x : ℝ) (hx : 0 < x) : 1 / Real.sqrt x = x ^ (-(1:ℝ)/2) := by
  have h2 : (-(1:ℝ))/2 = -(1/2) := by ring
  rw [one_div, Real.sqrt_eq_rpow, h2, ← Real.rpow_neg (le_of_lt hx) (1/2)]

/-- The exact normalisation of the leading Fourier integral of FI §7, eq. (7.6).  For `f ≥ 0`
continuous and compactly supported in `(0,∞)` and `γ² < 1`,

  `4 ∫∫_{t₁,t₂>0} f(t₁⁴ - 2γt₁²t₂² + t₂⁴) = (1/2)·A(γ)·B`,

where `A(γ) = ∫₀^∞ (t²-2γt+1)^{-1/2}t^{-1/2}dt` and `B = ∫₀^∞ f(u)u^{-1/2}du`.  The factor `4`
reduces `∫∫_{ℝ²}` to the quadrant (the quartic is even in each variable).

Route: substituting `t₁² = r`, `t₂² = s` gives `∫∫_{r,s>0} f(r²-2γrs+s²)/(4√(rs)) dr ds`; polar
coordinates `r = ρcosθ`, `s = ρsinθ` in the quadrant give
`(1/4)∫₀^{π/2} (∫₀^∞ f(ρ²(1-γ sin2θ)) dρ) dθ/√(sinθcosθ)`; then `∫₀^∞ f(ρ²h)dρ =
(1/2)h^{-1/2}∫₀^∞ f(u)u^{-1/2}du` (substitute `u = ρ²h`), and the `θ`-integral is `A(γ)`
(substitute `t = tan θ`).  `Mathlib.Analysis.SpecialFunctions.PolarCoord` (for `ℂ`) supplies the
polar step; `MeasureTheory.integral_comp_mul_left`, `intervalIntegral.integral_comp_tan` help. -/
theorem lemma_7_6_identity (f : ℝ → ℝ) (γ : ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfc : Continuous f)
    (hfsupp : ∀ x, x ≤ 0 → f x = 0) (hcc : HasCompactSupport f) (hγ : γ ^ 2 < 1) :
    4 * (∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0,
          f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4))
      = (1 / 2) * (∫ t in Set.Ioi 0,
            (t ^ 2 - 2 * γ * t + 1) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2))
          * (∫ u in Set.Ioi 0, f u / Real.sqrt u) := by
  -- `Q w = w² - 2γw + 1` is positive because `γ² < 1`.
  have hQpos : ∀ w : ℝ, 0 < w ^ 2 - 2 * γ * w + 1 := by
    intro w
    nlinarith [sq_nonneg (w - γ), hγ]
  -- Abbreviations for the successive shapes of the integral.
  set I : ℝ := ∫ t₁ in Set.Ioi 0, ∫ t₂ in Set.Ioi 0,
      f (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4) with hI
  set D : ℝ := ∫ r in Set.Ioi 0, ∫ s in Set.Ioi 0,
      f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s) with hD
  set A : ℝ := ∫ t in Set.Ioi 0,
      (t ^ 2 - 2 * γ * t + 1) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2) with hA
  set B : ℝ := ∫ u in Set.Ioi 0, f u / Real.sqrt u with hB
  set E : ℝ := ∫ r in Set.Ioi 0, ∫ w in Set.Ioi 0,
      f (r ^ 2 * (w ^ 2 - 2 * γ * w + 1)) / Real.sqrt w with hE
  set F : ℝ := ∫ w in Set.Ioi 0, ∫ r in Set.Ioi 0,
      f (r ^ 2 * (w ^ 2 - 2 * γ * w + 1)) / Real.sqrt w with hF
  set G : ℝ := ∫ w in Set.Ioi 0,
      (1 / Real.sqrt w) * ((1 / 2) * (w ^ 2 - 2 * γ * w + 1) ^ (-(1:ℝ)/2) * B) with hG
  -- Step 1: `t₁ = √r`, `t₂ = √s`.
  have step1 : I = (1/4) * D := SevenSix.quadrant_double_eq f γ
  -- Step 2: the inner substitution `s = r*w`.
  have step2 : D = E := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    exact SevenSix.inner_subst f γ r hr
  -- Step 3: Fubini (integrability of the joint integrand).
  have step3 : E = F := (setIntegral_prod_swap_Ioi
      (F := fun r w => f (r ^ 2 * (w ^ 2 - 2 * γ * w + 1)) / Real.sqrt w)
      (SevenSix.quad_integrable f γ hf0 hfc hfsupp hcc hγ)).symm
  -- Step 4: the one-dimensional substitution `u = r²·Q(w)` evaluates the inner integral.
  have step4 : F = G := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun w hw => ?_)
    rw [integral_div, SevenSix.one_dim_scale f (hQpos w)]
    ring
  -- Steps 5 and 6: pull out the constant and identify the remaining `w`-integral with `A`.
  have step56 : G = ((1/2) * B) * A := by
    have hcongr : (∫ w in Set.Ioi 0,
          (1 / Real.sqrt w) * ((1 / 2) * (w ^ 2 - 2 * γ * w + 1) ^ (-(1:ℝ)/2) * B))
        = ∫ w in Set.Ioi 0,
          ((1 / 2) * B) * ((1 / Real.sqrt w) * (w ^ 2 - 2 * γ * w + 1) ^ (-(1:ℝ)/2)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun w hw => by ring)
    rw [hG, hcongr, integral_const_mul]
    have hA' : (∫ w in Set.Ioi 0,
          (1 / Real.sqrt w) * (w ^ 2 - 2 * γ * w + 1) ^ (-(1:ℝ)/2)) = A := by
      rw [hA]
      refine setIntegral_congr_fun measurableSet_Ioi (fun w hw => ?_)
      rw [one_div_sqrt_eq_rpow_neg_half w (Set.mem_Ioi.mp hw), mul_comm]
    rw [hA']
  rw [step1, step2, step3, step4, step56]
  ring

end Work.FIArea2
