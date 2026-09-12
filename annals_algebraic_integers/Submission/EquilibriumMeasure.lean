import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The equilibrium measure of a compact interval

First layer of the potential-theoretic machinery needed to formalize Smith's
converse theorem ("Algebraic integers with conjugates in a prescribed
distribution", Ann. of Math. 200 (2024)) for the interval of Serre's example.

The unweighted equilibrium measure of `[a, b]` is the arcsine law: the
pushforward of normalized Lebesgue measure on `[0, π]` under
`t ↦ (a+b)/2 + (b-a)/2 * cos t`.  Here we record the elementary properties
needed later: it is a probability measure, its first moment is `(a+b)/2`, and
it is supported in `[a, b]`.
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal

namespace Submission.Equilibrium

/-- Lebesgue measure restricted to the open interval `(0,1)`, a probability measure. -/
def uniform01 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

lemma uniform01_univ : uniform01 Set.univ = 1 := by
  simp [uniform01, Real.volume_Ioc]

lemma uniform01_real_univ : uniform01.real Set.univ = 1 := by
  rw [Measure.real, uniform01_univ]
  norm_num

/-- The chart `u ↦ (a+b)/2 + (b-a)/2 * cos (π*u)` mapping `[0,1]` onto `[a,b]`. -/
def chart (a b : ℝ) : ℝ → ℝ :=
  fun u => (a + b) / 2 + (b - a) / 2 * Real.cos (Real.pi * u)

lemma chart_continuous (a b : ℝ) : Continuous (chart a b) := by
  unfold chart
  fun_prop

lemma chart_measurable (a b : ℝ) : Measurable (chart a b) :=
  (chart_continuous a b).measurable

/-- The (unweighted) equilibrium measure of the interval `[a,b]`. -/
def equilibrium (a b : ℝ) : Measure ℝ := Measure.map (chart a b) uniform01

lemma equilibrium_univ (a b : ℝ) : equilibrium a b Set.univ = 1 := by
  unfold equilibrium
  rw [Measure.map_apply (chart_measurable a b) MeasurableSet.univ]
  exact uniform01_univ

instance equilibrium_isProbability (a b : ℝ) : IsProbabilityMeasure (equilibrium a b) :=
  ⟨equilibrium_univ a b⟩

/-- The cosine chart integrates to zero over one half-period: `∫₀¹ cos(πu) du = 0`. -/
lemma intervalIntegral_cos_pi_mul :
    (∫ u in (0 : ℝ)..1, Real.cos (Real.pi * u)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) (c := Real.pi) (a := (0 : ℝ))
    (b := 1) (by positivity : (Real.pi : ℝ) ≠ 0)]
  simp [integral_cos]

/-- `∫₀¹ (c + d·cos(πu)) du = c`. -/
lemma intervalIntegral_affine_cos (c d : ℝ) :
    (∫ u in (0 : ℝ)..1, c + d * Real.cos (Real.pi * u)) = c := by
  have hcos : (∫ u in (0 : ℝ)..1, Real.cos (Real.pi * u)) = 0 :=
    intervalIntegral_cos_pi_mul
  calc
    (∫ u in (0 : ℝ)..1, c + d * Real.cos (Real.pi * u))
        = (∫ u in (0 : ℝ)..1, c) + (∫ u in (0 : ℝ)..1, d * Real.cos (Real.pi * u)) := by
          exact intervalIntegral.integral_add (μ := volume) (f := fun u : ℝ => c)
            (g := fun u : ℝ => d * Real.cos (Real.pi * u)) (a := (0 : ℝ)) (b := 1)
            (continuous_const.intervalIntegrable (0 : ℝ) 1)
            ((by fun_prop : Continuous (fun u : ℝ => d * Real.cos (Real.pi * u))).intervalIntegrable (0 : ℝ) 1)
    _ = (1 - (0 : ℝ)) • c + d * (∫ u in (0 : ℝ)..1, Real.cos (Real.pi * u)) := by
          rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul (r := d)]
    _ = c + d * 0 := by
          rw [hcos]
          simp
    _ = c := by ring

/-- The interval integral of the chart over `[0,1]` equals the midpoint. -/
lemma intervalIntegral_chart (a b : ℝ) :
    (∫ u in (0 : ℝ)..1, chart a b u) = (a + b) / 2 := by
  unfold chart
  exact intervalIntegral_affine_cos ((a + b) / 2) ((b - a) / 2)

/-- The integral over `uniform01` is the interval integral over `[0,1]`. -/
lemma uniform01_integral (f : ℝ → ℝ) :
    (∫ u : ℝ, f u ∂uniform01) = (∫ u in (0 : ℝ)..1, f u) := by
  rw [uniform01]
  rw [← intervalIntegral.integral_of_le (μ := volume) (f := f) (a := (0 : ℝ)) (b := 1)
    (by norm_num : (0 : ℝ) ≤ 1)]

/-- The integral of the cosine chart over the uniform measure on `[0,π]` vanishes. -/
lemma integral_cos_pi_mul : (∫ u : ℝ, Real.cos (Real.pi * u) ∂uniform01) = 0 := by
  rw [uniform01_integral]
  exact intervalIntegral_cos_pi_mul

/-- The mean of the equilibrium measure of `[a,b]` is `(a+b)/2`. -/
lemma equilibrium_mean (a b : ℝ) : (∫ x : ℝ, x ∂equilibrium a b) = (a + b) / 2 := by
  have hmap : (∫ x : ℝ, x ∂equilibrium a b) = (∫ u : ℝ, chart a b u ∂uniform01) := by
    rw [equilibrium]
    exact MeasureTheory.integral_map (φ := chart a b) (μ := uniform01) (f := fun y : ℝ => y)
      (by exact (chart_measurable a b).aemeasurable)
      (by exact continuous_id.aestronglyMeasurable (μ := Measure.map (chart a b) uniform01))
  rw [hmap]
  rw [uniform01_integral (chart a b)]
  exact intervalIntegral_chart a b



/-- For `a ≤ b`, the chart takes values in `[a,b]`. -/
lemma chart_mem_Icc {a b : ℝ} (hab : a ≤ b) (u : ℝ) : chart a b u ∈ Set.Icc a b := by
  have hhalf : 0 ≤ (b - a) / 2 := by linarith
  have hcos_ge : -1 ≤ Real.cos (Real.pi * u) := Real.neg_one_le_cos _
  have hcos_le : Real.cos (Real.pi * u) ≤ 1 := Real.cos_le_one _
  have hx : 0 ≤ chart a b u - a := by
    have : chart a b u - a = (b - a) / 2 * (1 + Real.cos (Real.pi * u)) := by
      unfold chart
      ring
    rw [this]
    exact mul_nonneg hhalf (by linarith)
  have hy : 0 ≤ b - chart a b u := by
    have : b - chart a b u = (b - a) / 2 * (1 - Real.cos (Real.pi * u)) := by
      unfold chart
      ring
    rw [this]
    exact mul_nonneg hhalf (by linarith)
  exact ⟨by linarith, by linarith⟩

/-- The complement of `[a,b]` carries no equilibrium mass (for `a ≤ b`). -/
lemma equilibrium_compl_Icc (a b : ℝ) (hab : a ≤ b) :
    equilibrium a b ((Set.Icc a b)ᶜ) = 0 := by
  unfold equilibrium
  rw [Measure.map_apply (chart_measurable a b) (MeasurableSet.compl isClosed_Icc.measurableSet)]
  -- (map (chart a b) uniform01) s = uniform01 (chart⁻¹ s); now s = chart⁻¹ ((Icc a b)ᶜ)
  rw [uniform01]
  rw [Measure.restrict_apply ((chart_measurable a b) (MeasurableSet.compl isClosed_Icc.measurableSet))]
  have hcover : ∀ u ∈ Set.Ioc (0 : ℝ) 1, u ∈ (chart a b) ⁻¹' (Set.Icc a b) := by
    intro u hu
    exact chart_mem_Icc hab u
  have hmeet : ((chart a b) ⁻¹' (Set.Icc a b))ᶜ ∩ Set.Ioc (0 : ℝ) 1 = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro u hu
    exact hu.1 (hcover u hu.2)
  simp [hmeet]

/-- The equilibrium measure of `[a,b]` has total mass one on `[a,b]` itself (for `a ≤ b`). -/
lemma equilibrium_Icc (a b : ℝ) (hab : a ≤ b) : equilibrium a b (Set.Icc a b) = 1 := by
  have hsum := MeasureTheory.measure_add_measure_compl (μ := equilibrium a b)
    (isClosed_Icc.measurableSet : MeasurableSet (Set.Icc a b))
  rw [equilibrium_compl_Icc a b hab, equilibrium_univ a b] at hsum
  simpa using hsum


/-- The equilibrium measure of `[a,b]` is supported on `[a,b]` itself (for `a ≤ b`). -/
lemma support_equilibrium_subset_Icc (a b : ℝ) (hab : a ≤ b) :
    (equilibrium a b).support ⊆ Set.Icc a b := by
  apply MeasureTheory.Measure.support_subset_of_isClosed (μ := equilibrium a b) isClosed_Icc
  rw [MeasureTheory.mem_ae_iff]
  exact equilibrium_compl_Icc a b hab


/-- The equilibrium measure of `[a,b]` (for `a ≤ b`) equals its restriction to `[a,b]`. -/
lemma equilibrium_eq_restrict_Icc (a b : ℝ) (hab : a ≤ b) :
    equilibrium a b = (equilibrium a b).restrict (Set.Icc a b) := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs]
  -- s = (s ∩ Icc) ∪ (s \ Icc); the latter has measure zero
  have hz : (equilibrium a b) (s \ Set.Icc a b) = 0 := by
    exact measure_mono_null (by intro x hx; exact hx.2) (equilibrium_compl_Icc a b hab)
  calc
    (equilibrium a b) s = (equilibrium a b) ((s ∩ Set.Icc a b) ∪ (s \ Set.Icc a b)) := by
        congr 1
        ext x
        by_cases hx : x ∈ Set.Icc a b <;> simp [hx]
    _ = (equilibrium a b) (s ∩ Set.Icc a b) + (equilibrium a b) (s \ Set.Icc a b) := by
        rw [MeasureTheory.measure_union]
        · rw [Set.disjoint_left]
          intro x hxA hxB
          exact hxB.2 hxA.2
        · exact hs.diff isClosed_Icc.measurableSet
    _ = (equilibrium a b) (s ∩ Set.Icc a b) := by rw [hz]; simp

end Submission.Equilibrium
