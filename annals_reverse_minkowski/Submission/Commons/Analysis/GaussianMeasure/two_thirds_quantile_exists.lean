import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import Submission.Commons.Analysis.GaussianMeasure.one_dim_tail_ten_le_sixth

open MeasureTheory Set
open scoped Real Interval

noncomputable section

namespace Commons.Analysis.GaussianMeasure

/-- There is a positive real `σ₀` at which the cumulative one-dimensional Gaussian mass
`∫_{-∞}^{σ₀} exp (-π x²) dx` equals `2/3`.

Proof sketch: with `F (t) := ∫ x in Iio t, exp (-π x²)` we have
* `F (0) = 1/2` (by reflection symmetry and `∫ exp (-πx²) = 1`),
* `5/6 ≤ F (10)` (since the upper tail `∫_{10}^{∞} exp(-πx²) ≤ 1/6`,
  see `one_dim_tail_ten_le_sixth`),
* `F` is continuous (it differs from the continuous interval-integral primitive
  `t ↦ ∫ 0..t` by the constant `F 0`, via `intervalIntegral.integral_Iio_sub_Iio'`).

The intermediate value theorem on `[0, 10]` then produces `0 < σ₀ ≤ 10` with `F σ₀ = 2/3`. -/
theorem two_thirds_quantile_exists :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧
      (∫ x in Set.Iio σ₀, Real.exp (-Real.pi * x ^ 2)) = (2 : ℝ) / 3 := by
  let f : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2)
  let F : ℝ → ℝ := fun c => ∫ x in Set.Iio c, f x
  have hf_int : Integrable f := by
    dsimp [f]
    exact integrable_exp_neg_mul_sq (b := Real.pi) Real.pi_pos
  have htot : (∫ x : ℝ, f x) = 1 := by
    dsimp [f]
    rw [integral_gaussian]
    have hsq : Real.sqrt (Real.pi / Real.pi) = 1 := by
      rw [div_self (ne_of_gt Real.pi_pos)]
      simp
    exact hsq
  -- The real line splits at any point `t`: mass left of `t` plus mass right of `t` is `1`.
  have hsplit (t : ℝ) : (∫ x in Set.Iio t, f x) + (∫ x in Set.Ioi t, f x) = 1 := by
    have hleft : (∫ x in Set.Iic t, f x) = ∫ x in Set.Iio t, f x := by
      exact MeasureTheory.integral_Iic_eq_integral_Iio (μ := (volume : Measure ℝ)) (x := t) (f := f)
    have hcomp_set : (Set.Iic t)ᶜ = Set.Ioi t := by
      ext x
      simp [Set.Ioi]
    have hcompl : (∫ x in Set.Ioi t, f x) = (∫ x : ℝ, f x) - ∫ x in Set.Iic t, f x := by
      rw [← hcomp_set]
      exact MeasureTheory.setIntegral_compl (μ := (volume : Measure ℝ)) measurableSet_Iic hf_int
    calc
      (∫ x in Set.Iio t, f x) + (∫ x in Set.Ioi t, f x)
          = (∫ x in Set.Iic t, f x) + (∫ x in Set.Ioi t, f x) := by
              rw [← hleft]
      _ = (∫ x : ℝ, f x) := by
              rw [hcompl]
              abel
      _ = 1 := htot
  -- Reflection symmetry: the negative half-line carries as much mass as the positive one.
  have hsym0 : (∫ x in Set.Iio (0 : ℝ), f x) = ∫ x in Set.Ioi (0 : ℝ), f x := by
    calc
      (∫ x in Set.Iio (0 : ℝ), f x) = ∫ x in Set.Iic (0 : ℝ), f x := by
        exact (MeasureTheory.integral_Iic_eq_integral_Iio (μ := (volume : Measure ℝ)) (x := (0 : ℝ)) (f := f)).symm
      _ = ∫ x in Set.Ioi (0 : ℝ), f (-x) := by
        rw [integral_comp_neg_Ioi]
        simp
      _ = ∫ x in Set.Ioi (0 : ℝ), f x := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        dsimp [f]
        congr 1
        ring
  -- `F (0) = 1/2 < 2/3`
  have hF0 : F (0 : ℝ) = 1 / 2 := by
    have hsplit0 := hsplit (0 : ℝ)
    have hmain : (∫ x in Set.Iio (0 : ℝ), f x) = 1 / 2 := by
      nlinarith [hsplit0, hsym0]
    simpa [F] using hmain
  -- `F (10) ≥ 5/6 > 2/3` (upper tail at 10 is at most `1/6`)
  have htail10 : (∫ x in Set.Ioi (10 : ℝ), f x) ≤ 1 / 6 := by
    simpa [f] using one_dim_tail_ten_le_sixth
  have hF10gt : (2 : ℝ) / 3 < F (10 : ℝ) := by
    have hsplit10 := hsplit (10 : ℝ)
    have hL10 : (∫ x in Set.Iio (10 : ℝ), f x) ≥ 5 / 6 := by
      nlinarith
    have hF10 : F (10 : ℝ) ≥ 5 / 6 := by
      simpa [F] using hL10
    nlinarith
  -- `F` is continuous: it is the interval-integral primitive plus a constant.
  have hFcont : Continuous F := by
    have hprim : Continuous (fun c : ℝ => ∫ x in 0..c, f x) := by
      exact hf_int.continuous_primitive (0 : ℝ)
    have hstep (c : ℝ) : F c = F (0 : ℝ) + (∫ x in 0..c, f x) := by
      have hsub : (∫ x in Set.Iio c, f x) - (∫ x in Set.Iio (0 : ℝ), f x) = ∫ x in 0..c, f x := by
        exact intervalIntegral.integral_Iio_sub_Iio' (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := c)
          (f := f) hf_int.integrableOn hf_int.integrableOn
      dsimp [F]
      linarith [hsub]
    have hdef : F = fun c : ℝ => F (0 : ℝ) + ∫ x in 0..c, f x := by
      funext c
      exact hstep c
    rw [hdef]
    exact hprim.const_add (F (0 : ℝ))
  -- Intermediate value theorem on `[0, 10]`
  have hF0lt : F (0 : ℝ) < (2 : ℝ) / 3 := by nlinarith [hF0]
  have hmid : (2 : ℝ) / 3 ∈ Set.Icc (F (0 : ℝ)) (F (10 : ℝ)) := by
    exact ⟨le_of_lt hF0lt, le_of_lt hF10gt⟩
  have himg : (2 : ℝ) / 3 ∈ (fun c : ℝ => F c) '' Set.Icc (0 : ℝ) 10 := by
    exact (intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 10) hFcont.continuousOn) hmid
  rcases himg with ⟨c, hc_mem, hc_eq⟩
  have hc_nonneg : 0 ≤ c := hc_mem.1
  have hc_pos : 0 < c := by
    refine lt_of_le_of_ne hc_nonneg ?_
    intro hc0
    have hc_eq0 : F (0 : ℝ) = (2 : ℝ) / 3 := by simpa [hc0] using hc_eq
    linarith [hF0]
  refine ⟨c, hc_pos, ?_⟩
  simpa [F, f] using hc_eq

end Commons.Analysis.GaussianMeasure
