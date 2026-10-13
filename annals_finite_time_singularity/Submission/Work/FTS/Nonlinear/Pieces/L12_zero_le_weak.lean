import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.L12ZeroQ
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces

open scoped Real Topology
open MeasureTheory Set Filter

/-- Elementary square-root algebra: for `x ≥ 0` and `r > 0`,
`√(3 · x · ((1+r)/r)²) = √3 · √x · ((1+r)/r)`. -/
private lemma sqrt_three_mul_sq_div {x : ℝ} (hx : 0 ≤ x) {r : ℝ} (hr : 0 < r) :
    Real.sqrt (3 * (x * ((1 + r) / r) ^ 2))
      = Real.sqrt 3 * Real.sqrt x * ((1 + r) / r) := by
  have hy : 0 ≤ (1 + r) / r := div_nonneg (by linarith) (le_of_lt hr)
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (x * ((1 + r) / r) ^ 2),
    Real.sqrt_mul hx (((1 + r) / r) ^ 2), Real.sqrt_sq hy]
  ring

/-- **The "weak" `L₁₂(0)` bound.**  With only the two integrability hypotheses — the angular
slices `θ ↦ f(r,θ)²` are integrable on `Iθ` for a.e. `r > 0`, and the Hardy-weighted angular
energy `r ↦ (∫_θ f(r,θ)²)·((1+r)/r)²` is integrable on `(0,∞)` — one has
`|L₁₂(f)(0)| ≤ 3 √(∫_{r>0} (∫_θ f(r,θ)²)((1+r)/r)²)`.

This is the Cauchy–Schwarz argument of `Work.FTS.H2.L12ZeroQ` stripped of all regularity
assumptions: the slicewise bound `|L₁₂dens(f)(r)| ≤ √3 √(∫_θ f(r,θ)²)/r`
(`Work.Coercivity.L12dens_sq_slice`) holds for a.e. `r`, and the radial singularity `1/r` is
split as `((1+r)/r)·(1/(1+r))` with the tail weight `(1/(1+r))² ∈ L²(0,∞)` of `L²`-norm `≤ √2`
(`Work.FTS.H2.InvOneAddSq`).  Measurability of the angular energy is not assumed: the massaged
majorant `A(r) = √(3 (∫_θ f(r,θ)²)((1+r)/r)²)` is built from the *assumed* integrable function,
and no measurability or integrability of the density itself is used (`Work.FTS.H2.CS1D` is
unconditional). -/
theorem L12_zero_le_weak (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f r θ) ^ 2) Work.Spaces.Iθ)
    (hfin : MeasureTheory.IntegrableOn
      (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (Set.Ioi (0 : ℝ))) :
    |Work.Construction.L12 f 0| ≤ 3 * Real.sqrt
      (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) with hμdef
  set φ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2 with hφdef
  set Wt : ℝ → ℝ := fun r => ((1 + r) / r) ^ 2 with hWtdef
  set A : ℝ → ℝ := fun r => Real.sqrt (3 * (φ r * Wt r)) with hAdef
  set B : ℝ → ℝ := fun r => 1 / (1 + r) with hBdef
  set g : ℝ → ℝ := fun r => Work.FM.L12dens Work.Spaces.K f r with hgdef
  set X : ℝ := ∫ r in Set.Ioi (0 : ℝ),
      (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 with hXdef
  have hr_mem : ∀ᵐ r ∂μ, r ∈ Set.Ioi (0 : ℝ) :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioi
  -- the angular energy is everywhere nonnegative, as is the Hardy weight
  have hφ0 : ∀ r : ℝ, 0 ≤ φ r := fun r =>
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun θ => sq_nonneg (f r θ))
  have hWt0 : ∀ r : ℝ, 0 ≤ Wt r := fun r => by rw [hWtdef]; exact sq_nonneg _
  -- the majorant `A` is a.e. strongly measurable by construction
  have hA_meas : MeasureTheory.AEStronglyMeasurable A μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable (hfin.aestronglyMeasurable.const_mul 3)
  -- `A²` is the Hardy-weighted angular energy, times `3`
  have hpt : ∀ r : ℝ, A r ^ 2 = 3 * (φ r * Wt r) := by
    intro r
    rw [hAdef]
    dsimp only
    exact Real.sq_sqrt (mul_nonneg (by norm_num) (mul_nonneg (hφ0 r) (hWt0 r)))
  have hA_int : MeasureTheory.Integrable (fun r : ℝ => A r ^ 2) μ := by
    have h3 : MeasureTheory.Integrable (fun r : ℝ => 3 * (φ r * Wt r)) μ := hfin.const_mul 3
    exact h3.congr (Filter.Eventually.of_forall fun r => (hpt r).symm)
  have hmemA : MeasureTheory.MemLp A 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hA_meas).mpr hA_int
  -- the tail weight `1/(1+r)`
  have hB_meas : MeasureTheory.AEStronglyMeasurable B μ := by
    rw [hμdef, hBdef]
    exact (ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
      (fun r hr => by
        have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
        exact ne_of_gt (by show (0 : ℝ) < 1 + r; linarith))).aestronglyMeasurable
      measurableSet_Ioi
  have hB_int : MeasureTheory.Integrable (fun r : ℝ => B r ^ 2) μ := by
    rw [hμdef, hBdef]
    exact (Work.FTS.H2.InvOneAddSq).1
  have hmemB : MeasureTheory.MemLp B 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hB_meas).mpr hB_int
  -- a.e. nonnegativity of the two factors
  have hA0 : 0 ≤ᵐ[μ] A := Filter.Eventually.of_forall fun r => Real.sqrt_nonneg _
  have hB0 : 0 ≤ᵐ[μ] B := by
    filter_upwards [hr_mem] with r hr
    rw [hBdef]
    exact div_nonneg zero_le_one (by linarith [Set.mem_Ioi.mp hr])
  -- the pointwise (a.e.) slicewise bound
  have hbd : ∀ᵐ r ∂μ, |g r| ≤ A r * B r := by
    filter_upwards [hsl, hr_mem] with r hslr hr
    have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
    have hsq : (Work.FM.L12dens Work.Spaces.K f r) ^ 2 ≤ 3 * φ r / r ^ 2 :=
      Work.Coercivity.L12dens_sq_slice f Work.Coercivity.integral_Itheta_K hr' hslr
    have hb : |Work.FM.L12dens Work.Spaces.K f r|
        ≤ Real.sqrt 3 * Real.sqrt (φ r) / r :=
      Work.FTS.H2.abs_le_sqrt_three_mul_sqrt_div hr' (hφ0 r) hsq
    have hkey : A r * B r = Real.sqrt 3 * Real.sqrt (φ r) / r := by
      have hAval : A r = Real.sqrt 3 * Real.sqrt (φ r) * ((1 + r) / r) := by
        rw [hAdef, hWtdef]
        exact sqrt_three_mul_sq_div (hφ0 r) hr'
      rw [hAval, hBdef]
      have h2 : ((1 + r) / r) * (1 / (1 + r)) = 1 / r := by
        have hr0 : r ≠ 0 := ne_of_gt hr'
        have h1r : (1 : ℝ) + r ≠ 0 := by linarith
        field_simp
      calc Real.sqrt 3 * Real.sqrt (φ r) * ((1 + r) / r) * (1 / (1 + r))
          = Real.sqrt 3
              * (Real.sqrt (φ r) * (((1 + r) / r) * (1 / (1 + r)))) := by ring
        _ = Real.sqrt 3 * (Real.sqrt (φ r) * (1 / r)) := by rw [h2]
        _ = Real.sqrt 3 * Real.sqrt (φ r) / r := by ring
    rw [hgdef, hkey]
    exact hb
  -- Cauchy–Schwarz in the radial variable
  have hcs := Work.FTS.H2.CS1D (μ := μ) (g := g) (A := A) (B := B)
    hmemA hmemB hA0 hB0 hbd
  have hLHS : (∫ r, g r ∂μ) = Work.Construction.L12 f 0 := by
    rw [hμdef, hgdef]
    rfl
  have hA2 : (∫ r, A r ^ 2 ∂μ) = 3 * X := by
    rw [hμdef]
    calc ∫ r in Set.Ioi (0 : ℝ), A r ^ 2
        = ∫ r in Set.Ioi (0 : ℝ), 3 * (φ r * Wt r) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r _ => hpt r)
      _ = 3 * ∫ r in Set.Ioi (0 : ℝ), φ r * Wt r :=
          MeasureTheory.integral_const_mul 3 (fun r : ℝ => φ r * Wt r)
      _ = 3 * X := rfl
  have hB2 : (∫ r, B r ^ 2 ∂μ) ≤ 2 := by
    rw [hμdef, hBdef]
    exact (Work.FTS.H2.InvOneAddSq).2
  have hfinal : |Work.Construction.L12 f 0| ≤ Real.sqrt (3 * X) * Real.sqrt 2 := by
    rw [← hLHS]
    exact hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hA2.le) (Real.sqrt_le_sqrt hB2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt (3 * X) * Real.sqrt 2 = Real.sqrt 6 * Real.sqrt X := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) X]
    rw [show Real.sqrt 3 * Real.sqrt X * Real.sqrt 2
        = (Real.sqrt 3 * Real.sqrt 2) * Real.sqrt X from by ring]
    rw [show Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 from by
      rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (2 : ℝ)]
      norm_num]
  have h6 : Real.sqrt 6 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]
  calc |Work.Construction.L12 f 0|
      ≤ Real.sqrt (3 * X) * Real.sqrt 2 := hfinal
    _ = Real.sqrt 6 * Real.sqrt X := hsqrt
    _ ≤ 3 * Real.sqrt X := mul_le_mul_of_nonneg_right h6 (Real.sqrt_nonneg X)

end Work.FTS.Nonlinear.Pieces
