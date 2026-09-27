import Mathlib
import Submission.Work.EKLC7.TentDef
import Submission.Work.EKLC7.tendsto_tent_formula
import Submission.Work.EKLC7.tent_formula_le_indicator
import Submission.Work.EKLC7.ext_of_Ioc_rat

/-!
# The tent functions determine a Radon measure on `ℝ`

A tent (trapezoid) function with rational parameters `a < b` and slope `n` is

`tent a b n t = max 0 (min 1 (min (n (t - a)) (1 + n (b - t))))`.

It rises linearly from `0` to `1` on `[a, a + 1/n]`, equals `1` up to `b`, decays linearly
back to `0` on `[b, b + 1/n]`, and vanishes elsewhere; in particular it is continuous with
compact support, and as `n → ∞` it converges pointwise to the indicator of the half-open
interval `(a, b]`.

Consequently, if two measures `γ, δ` on `ℝ` which are finite on compact sets give the same
value to `∫ t, tent a b n t` for every `(a, b, n)`, then they give the same mass to every
half-open interval with rational endpoints (dominated convergence: the tents are bounded by
the indicator of the compact interval `[a, b+1]`, which is integrable for a measure that is
finite on compact sets), and hence `γ = δ` because the half-open intervals with rational
endpoints form a π-system generating the Borel σ-algebra which is covered by finitely
measured sets.
-/

namespace Work.EKLC7

open MeasureTheory Filter
open scoped ENNReal Topology

/-- The tent (trapezoid) function with rational parameters `a`, `b` and slope `n`. -/
def tent (a b : ℚ) (n : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 (min ((n : ℝ) * (t - a)) (1 + (n : ℝ) * (b - t))))

/-- `tent` is literally `tentFormula` from the definition file. -/
theorem tent_eq_tentFormula : tent = tentFormula := rfl

/-- **Dominating function.** For every `n` the tent `tent a b n` is bounded by the
indicator of the compact interval `[a, b + 1]`. -/
theorem tent_le_indicator_Icc (a b : ℚ) (n : ℕ) (t : ℝ) :
    tent a b n t ≤ (Set.Icc (a : ℝ) ((b : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) t :=
  tent_formula_le_indicator a b n t

/-- **Pointwise convergence.** As `n → ∞`, `tent a b n` converges pointwise to the indicator
of the half-open interval `(a, b]`. -/
theorem tendsto_tent (a b : ℚ) (hab : a < b) (t : ℝ) :
    Filter.Tendsto (fun n : ℕ => tent a b n t) Filter.atTop
      (nhds ((Set.Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => (1 : ℝ)) t)) :=
  tendsto_tent_formula a b hab t

/-- The integrals of the tents against a measure finite on compact sets converge, as
`n → ∞`, to the (real value of the) mass of the half-open interval `(a, b]`.

Dominated convergence with dominating function the indicator of the compact interval
`[a, b + 1]` (integrable because the measure is finite on compact sets). -/
theorem tendsto_integral_tent (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (a b : ℚ) (hab : a < b) :
    Filter.Tendsto (fun n : ℕ => ∫ t, tent a b n t ∂μ) Filter.atTop
      (nhds ((μ (Set.Ioc (a : ℝ) (b : ℝ))).toReal)) := by
  -- the dominating function is integrable
  have hbint : Integrable ((Set.Icc (a : ℝ) ((b : ℝ) + 1)).indicator (fun _ => (1 : ℝ))) μ := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    refine MeasureTheory.integrableOn_const (C := (1 : ℝ)) ?_ ?_
    · exact (MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact isCompact_Icc).ne
    · simp
  -- the tents are continuous, hence a.e. strongly measurable
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun t : ℝ => tent a b n t) μ := by
    intro n
    exact ((by unfold tent; fun_prop : Continuous (fun t : ℝ => tent a b n t))).aestronglyMeasurable
  -- the domination
  have hbound : ∀ n : ℕ, ∀ᵐ t ∂μ,
      ‖tent a b n t‖ ≤ (Set.Icc (a : ℝ) ((b : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) t := by
    intro n
    refine Eventually.of_forall fun t => ?_
    unfold tent
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left (0 : ℝ) _)]
    exact tent_le_indicator_Icc a b n t
  -- the pointwise convergence
  have hlim : ∀ᵐ t ∂μ, Filter.Tendsto (fun n : ℕ => tent a b n t) Filter.atTop
      (nhds ((Set.Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => (1 : ℝ)) t)) :=
    Eventually.of_forall fun t => tendsto_tent a b hab t
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n t => tent a b n t)
    (f := fun t => (Set.Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => (1 : ℝ)) t)
    (fun t => (Set.Icc (a : ℝ) ((b : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) t)
    hmeas hbint hbound hlim
  rw [MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ) measurableSet_Ioc] at hDCT
  rw [MeasureTheory.measureReal_def] at hDCT
  simpa using hDCT

/-- **The tent functions determine a measure finite on compact sets.**  If two measures on `ℝ`
which are finite on compact sets give the same integral to every tent function with rational
parameters, then they are equal. -/
theorem TentDetermine {γ δ : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsFiniteMeasureOnCompacts γ] [MeasureTheory.IsFiniteMeasureOnCompacts δ]
    (h : ∀ (a b : ℚ) (n : ℕ), ∫ t, tent a b n t ∂γ = ∫ t, tent a b n t ∂δ) : γ = δ := by
  refine ext_of_Ioc_rat (μ := γ) (ν := δ) fun a b => ?_
  by_cases hab : a < b
  · -- the two sequences of integrals are equal, hence their limits are equal
    have hγ := tendsto_integral_tent γ a b hab
    have hδ := tendsto_integral_tent δ a b hab
    have hfun : (fun n : ℕ => ∫ t, tent a b n t ∂γ) = (fun n : ℕ => ∫ t, tent a b n t ∂δ) :=
      funext (h a b)
    have heq : (γ (Set.Ioc (a : ℝ) (b : ℝ))).toReal
        = (δ (Set.Ioc (a : ℝ) (b : ℝ))).toReal := by
      refine tendsto_nhds_unique hγ ?_
      rw [hfun]
      exact hδ
    -- both measures of the interval are finite, so `toReal` is injective on them
    have hγfin : γ (Set.Ioc (a : ℝ) (b : ℝ)) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono Set.Ioc_subset_Icc_self)
        (MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact isCompact_Icc))
    have hδfin : δ (Set.Ioc (a : ℝ) (b : ℝ)) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono Set.Ioc_subset_Icc_self)
        (MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact isCompact_Icc))
    exact (ENNReal.toReal_eq_toReal_iff' hγfin hδfin).mp heq
  · -- degenerate interval: both sides vanish
    have hab' : ¬ (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    simp [Set.Ioc_eq_empty hab']

end Work.EKLC7
