import Mathlib
import Submission.Work.Asymptotics.rectInt_eq_residue

namespace Work.CKFinal.LineDecay

open MeasureTheory Filter Topology
open scoped Topology

/-- **The vertical-ray shift identity.**  If `f` is continuous on the half-strip
`{x₁ ≤ re ≤ x₂, y₁ ≤ im}` except at the interior point `z₀`, holomorphic on the open part of
that half-strip except at `z₀`, has simple-pole residue `c` at `z₀` (in the limit form
`(z - z₀) f z → c`), and the top-edge integrals tend to `0`, then the boundary integral of the
half-infinite rectangle equals `2 π i c`. -/
theorem vertical_ray_shift {f : ℂ → ℂ} {z₀ c : ℂ} {x₁ x₂ y₁ : ℝ}
    (hx₁ : x₁ < z₀.re) (hx₂ : z₀.re < x₂) (hy₁ : y₁ < z₀.im)
    (hcont : ContinuousOn f ({z : ℂ | x₁ ≤ z.re ∧ z.re ≤ x₂ ∧ y₁ ≤ z.im} \ {z₀}))
    (hhol : ∀ z : ℂ, x₁ < z.re → z.re < x₂ → y₁ < z.im → z ≠ z₀ → DifferentiableAt ℂ f z)
    (hres : Filter.Tendsto (fun z : ℂ => (z - z₀) * f z) (nhdsWithin z₀ {z₀}ᶜ) (nhds c))
    (htop : Filter.Tendsto (fun R : ℝ => ∫ x in x₁..x₂, f ((x : ℂ) + (R : ℂ) * Complex.I))
              Filter.atTop (nhds 0))
    (hint₁ : MeasureTheory.IntegrableOn (fun y : ℝ => f ((x₁ : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi y₁))
    (hint₂ : MeasureTheory.IntegrableOn (fun y : ℝ => f ((x₂ : ℂ) + (y : ℂ) * Complex.I)) (Set.Ioi y₁)) :
    Complex.I * (∫ y in Set.Ioi y₁, f ((x₂ : ℂ) + (y : ℂ) * Complex.I))
      - Complex.I * (∫ y in Set.Ioi y₁, f ((x₁ : ℂ) + (y : ℂ) * Complex.I))
      + (∫ x in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I))
      = 2 * (Real.pi : ℂ) * Complex.I * c := by
  -- The rectangle boundary identity for every `R > z₀.im`.
  have hrect : ∀ R : ℝ, z₀.im < R →
      (∫ x in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I))
        + Complex.I * (∫ y in y₁..R, f ((x₂ : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I * (∫ y in y₁..R, f ((x₁ : ℂ) + (y : ℂ) * Complex.I))
      = (∫ x in x₁..x₂, f ((x : ℂ) + (R : ℂ) * Complex.I)) + 2 * (Real.pi : ℂ) * Complex.I * c := by
    intro R hR
    have hcontR : ContinuousOn f
        ({z : ℂ | x₁ ≤ z.re ∧ z.re ≤ x₂ ∧ y₁ ≤ z.im ∧ z.im ≤ R} \ {z₀}) :=
      hcont.mono (Set.sdiff_subset_sdiff (fun z hz => ⟨hz.1, hz.2.1, hz.2.2.1⟩) fun x hx => hx)
    have hholR : ∀ z : ℂ, x₁ < z.re → z.re < x₂ → y₁ < z.im → z.im < R → z ≠ z₀ →
        DifferentiableAt ℂ f z := fun z h1 h2 h3 _ hne => hhol z h1 h2 h3 hne
    have key := Work.Asymptotics.rectInt_eq_residue f z₀ c x₁ x₂ y₁ R
      hx₁ hx₂ hy₁ hR hcontR hholR hres
    linear_combination key
  -- Interval-integral limits along the two vertical sides.
  have hb_lim : Tendsto (fun R : ℝ => ∫ y in y₁..R, f ((x₂ : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (∫ y in Set.Ioi y₁, f ((x₂ : ℂ) + (y : ℂ) * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := volume)
      (f := fun y : ℝ => f ((x₂ : ℂ) + (y : ℂ) * Complex.I)) y₁ hint₂ Filter.tendsto_id
  have ha_lim : Tendsto (fun R : ℝ => ∫ y in y₁..R, f ((x₁ : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (∫ y in Set.Ioi y₁, f ((x₁ : ℂ) + (y : ℂ) * Complex.I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := volume)
      (f := fun y : ℝ => f ((x₁ : ℂ) + (y : ℂ) * Complex.I)) y₁ hint₁ Filter.tendsto_id
  -- The left-hand side converges to the desired expression.
  have hL : Tendsto
      (fun R : ℝ => (∫ x in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I))
        + Complex.I * (∫ y in y₁..R, f ((x₂ : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I * (∫ y in y₁..R, f ((x₁ : ℂ) + (y : ℂ) * Complex.I)))
      atTop
      (𝓝 ((∫ x in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I))
        + Complex.I * (∫ y in Set.Ioi y₁, f ((x₂ : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I * (∫ y in Set.Ioi y₁, f ((x₁ : ℂ) + (y : ℂ) * Complex.I)))) :=
    (tendsto_const_nhds.add (hb_lim.const_mul Complex.I)).sub (ha_lim.const_mul Complex.I)
  -- Eventually the left-hand side equals the top-edge integral plus the residue term.
  have hevent : (fun R : ℝ => (∫ x in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I))
        + Complex.I * (∫ y in y₁..R, f ((x₂ : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I * (∫ y in y₁..R, f ((x₁ : ℂ) + (y : ℂ) * Complex.I)))
      =ᶠ[atTop] (fun R : ℝ => (∫ x in x₁..x₂, f ((x : ℂ) + (R : ℂ) * Complex.I))
        + 2 * (Real.pi : ℂ) * Complex.I * c) := by
    filter_upwards [eventually_gt_atTop z₀.im] with R hR
    exact hrect R hR
  have hL0 : Tendsto
      (fun R : ℝ => (∫ x in x₁..x₂, f ((x : ℂ) + (R : ℂ) * Complex.I))
        + 2 * (Real.pi : ℂ) * Complex.I * c)
      atTop (𝓝 (2 * (Real.pi : ℂ) * Complex.I * c)) := by
    simpa using htop.add tendsto_const_nhds
  have hL0' : Tendsto
      (fun R : ℝ => (∫ x in x₁..x₂, f ((x : ℂ) + (y₁ : ℂ) * Complex.I))
        + Complex.I * (∫ y in y₁..R, f ((x₂ : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I * (∫ y in y₁..R, f ((x₁ : ℂ) + (y : ℂ) * Complex.I)))
      atTop (𝓝 (2 * (Real.pi : ℂ) * Complex.I * c)) := hL0.congr' hevent.symm
  have hEq := tendsto_nhds_unique hL hL0'
  linear_combination hEq

end Work.CKFinal.LineDecay
