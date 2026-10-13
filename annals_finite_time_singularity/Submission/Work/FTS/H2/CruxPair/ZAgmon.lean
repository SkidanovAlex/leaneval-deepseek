import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open scoped RealInnerProductSpace
open MeasureTheory Set Filter

namespace Work.FTS.H2.CruxPair

set_option autoImplicit false

/-!
# The multiplicative Agmon inequality `ZAgmon`

On an interval `[z₀, 2z₀]` of length `z₀`, an absolutely continuous function `h` (here given
through the fundamental-theorem-of-calculus identity `h x - h y = ∫_y^x h'`) satisfies

  `h z ^ 2 ≤ (2 / z₀) ∫_{z₀}^{2z₀} h² + (2 z₀) ∫_{z₀}^{2z₀} (h')²`  for all `z ∈ [z₀, 2z₀]`.

The proof is the elementary Agmon argument: `h z² ≤ 2 h y² + 2 (h z - h y)²` pointwise, average
in `y` over the interval of length `z₀`, and estimate `(h z - h y)² = (∫_y^z h')²` by
Cauchy–Schwarz.
-/

/-- Cauchy–Schwarz (Bunyakovsky) inequality for the Lebesgue integral over a set, exponent `2`:
for real functions `u`, `v` that are square-integrable on `s`,
`(∫_s u v)^2 ≤ (∫_s u^2) * (∫_s v^2)`. -/
private theorem cs_int {u v : ℝ → ℝ} {s : Set ℝ}
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict s))
    (hv : MeasureTheory.MemLp v 2 (MeasureTheory.volume.restrict s)) :
    (∫ x in s, u x * v x) ^ 2 ≤ (∫ x in s, u x ^ 2) * (∫ x in s, v x ^ 2) := by
  have hB : (∫ x in s, u x * v x) = ∫ a in s, (hu.toLp u) a * (hv.toLp v) a :=
    integral_congr_ae (by
      filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
      rw [hx, hy])
  have hA : (∫ x in s, u x ^ 2) = ∫ a in s, (hu.toLp u) a * (hu.toLp u) a :=
    integral_congr_ae (by
      filter_upwards [hu.coeFn_toLp] with x hx
      rw [hx, sq])
  have hC : (∫ x in s, v x ^ 2) = ∫ a in s, (hv.toLp v) a * (hv.toLp v) a :=
    integral_congr_ae (by
      filter_upwards [hv.coeFn_toLp] with x hx
      rw [hx, sq])
  have h := real_inner_mul_inner_self_le (hu.toLp u) (hv.toLp v)
  simp only [L2.inner_def, Real.inner_apply] at h
  rw [hB, hA, hC]
  simpa [sq] using h

/-- The Cauchy–Schwarz step of the Agmon inequality: for `z₀ ≤ y ≤ z ≤ 2 z₀` and a square
integrable function on `[z₀, 2 z₀]`,
`(∫_y^z g)² ≤ z₀ * ∫_{z₀}^{2 z₀} g²`. -/
private lemma cs_sq_le {g : ℝ → ℝ} {z₀ y z : ℝ} (hz₀ : 0 < z₀)
    (hy : z₀ ≤ y) (hz : z ≤ 2 * z₀) (hyz : y ≤ z)
    (hgm : AEStronglyMeasurable g (volume.restrict (Set.Ioc y z)))
    (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume z₀ (2 * z₀)) :
    (∫ t in y..z, g t) ^ 2 ≤ z₀ * ∫ t in z₀..(2 * z₀), g t ^ 2 := by
  have hz₂ : z₀ ≤ 2 * z₀ := by linarith
  have hg2full : IntegrableOn (fun t => g t ^ 2) (Set.Ioc z₀ (2 * z₀)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz₂).mp hg2
  have hsub : Set.Ioc y z ⊆ Set.Ioc z₀ (2 * z₀) := Set.Ioc_subset_Ioc hy hz
  have hg2sub : IntegrableOn (fun t => g t ^ 2) (Set.Ioc y z) := hg2full.mono_set hsub
  have hmem : MemLp g 2 (volume.restrict (Set.Ioc y z)) :=
    (memLp_two_iff_integrable_sq hgm).2 hg2sub
  have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc y z)) :=
    memLp_const 1
  have hcs := cs_int (s := Set.Ioc y z) hmem hmem1
  have e1 : (∫ x in Set.Ioc y z, g x * 1) = ∫ t in y..z, g t := by
    rw [← intervalIntegral.integral_of_le hyz]
    simp
  have e2 : (∫ x in Set.Ioc y z, (1 : ℝ) ^ 2) = z - y := by
    rw [one_pow, ← intervalIntegral.integral_of_le hyz, intervalIntegral.integral_const,
      smul_eq_mul, mul_one]
  rw [e1, e2] at hcs
  have hleB : (∫ x in Set.Ioc y z, g x ^ 2) ≤ ∫ t in z₀..(2 * z₀), g t ^ 2 := by
    rw [← intervalIntegral.integral_of_le hyz]
    exact intervalIntegral.integral_mono_interval hy hyz hz
      (Filter.Eventually.of_forall (fun x => sq_nonneg (g x))) hg2
  have hBnn : 0 ≤ ∫ x in Set.Ioc y z, g x ^ 2 := integral_nonneg (fun x => sq_nonneg (g x))
  have hzy : z - y ≤ z₀ := by linarith
  have hkey : (∫ x in Set.Ioc y z, g x ^ 2) * (z - y) ≤ z₀ * ∫ t in z₀..(2 * z₀), g t ^ 2 := by
    calc (∫ x in Set.Ioc y z, g x ^ 2) * (z - y)
        ≤ (∫ x in Set.Ioc y z, g x ^ 2) * z₀ := mul_le_mul_of_nonneg_left hzy hBnn
      _ ≤ (∫ t in z₀..(2 * z₀), g t ^ 2) * z₀ := mul_le_mul_of_nonneg_right hleB hz₀.le
      _ = z₀ * ∫ t in z₀..(2 * z₀), g t ^ 2 := by ring
  linarith [hcs, hkey]

/-- Pointwise Agmon bound for the difference of two values of `h` on `[z₀, 2 z₀]`. -/
private lemma diff_sq_le {h : ℝ → ℝ} {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hFTC : ∀ x ∈ Set.Icc z₀ (2 * z₀), ∀ y ∈ Set.Icc z₀ (2 * z₀),
      h x - h y = ∫ t in y..x, deriv h t)
    (hint2 : IntervalIntegrable (fun t => deriv h t ^ 2) volume z₀ (2 * z₀))
    {z : ℝ} (hz : z ∈ Set.Icc z₀ (2 * z₀)) {y : ℝ} (hy : y ∈ Set.Icc z₀ (2 * z₀)) :
    (h z - h y) ^ 2 ≤ z₀ * ∫ t in z₀..(2 * z₀), deriv h t ^ 2 := by
  have hftc : h z - h y = ∫ t in y..z, deriv h t := hFTC z hz y hy
  rw [hftc]
  rcases le_total y z with hyz | hzy
  · exact cs_sq_le hz₀ hy.1 hz.2 hyz (aestronglyMeasurable_deriv h _) hint2
  · have h2 : (∫ t in y..z, deriv h t) ^ 2 = (∫ t in z..y, deriv h t) ^ 2 := by
      rw [intervalIntegral.integral_symm]
      ring
    rw [h2]
    exact cs_sq_le hz₀ hz.1 hy.2 hzy (aestronglyMeasurable_deriv h _) hint2

theorem ZAgmon (h : ℝ → ℝ) {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hcont : ContinuousOn h (Set.Icc z₀ (2 * z₀)))
    (hFTC : ∀ x ∈ Set.Icc z₀ (2 * z₀), ∀ y ∈ Set.Icc z₀ (2 * z₀),
      h x - h y = ∫ t in y..x, deriv h t)
    (hint1 : IntervalIntegrable (fun z => h z ^ 2) MeasureTheory.volume z₀ (2 * z₀))
    (hint2 : IntervalIntegrable (fun z => deriv h z ^ 2) MeasureTheory.volume z₀ (2 * z₀)) :
    ∀ z ∈ Set.Icc z₀ (2 * z₀),
      h z ^ 2 ≤ (2 / z₀) * (∫ z in z₀..(2 * z₀), h z ^ 2)
        + (2 * z₀) * (∫ z in z₀..(2 * z₀), deriv h z ^ 2) := by
  intro z hz
  have hz₂ : z₀ ≤ 2 * z₀ := by linarith
  set B : ℝ := ∫ t in z₀..(2 * z₀), deriv h t ^ 2 with hB
  -- integrability bookkeeping
  have hint_c : IntervalIntegrable (fun t : ℝ => (h z) ^ 2) volume z₀ (2 * z₀) :=
    intervalIntegrable_const
  have hint_diff : IntervalIntegrable (fun t : ℝ => (h z - h t) ^ 2) volume z₀ (2 * z₀) := by
    refine ContinuousOn.intervalIntegrable_of_Icc hz₂ ?_
    exact ((continuousOn_const : ContinuousOn (fun _ : ℝ => h z) (Set.Icc z₀ (2 * z₀))).sub
      hcont).pow 2
  -- step 1: `h z ^ 2 ≤ 2 h t ^ 2 + 2 (h z - h t) ^ 2`
  have hpt : ∀ t ∈ Set.Icc z₀ (2 * z₀), (h z) ^ 2 ≤ 2 * h t ^ 2 + 2 * (h z - h t) ^ 2 := by
    intro t _
    nlinarith [sq_nonneg (h t - (h z - h t))]
  have hint_rhs : IntervalIntegrable (fun t : ℝ => 2 * h t ^ 2 + 2 * (h z - h t) ^ 2)
      volume z₀ (2 * z₀) :=
    (hint1.const_mul 2).add (hint_diff.const_mul 2)
  have hmono1 := intervalIntegral.integral_mono_on hz₂ hint_c hint_rhs hpt
  have hconst1 : (∫ t in z₀..(2 * z₀), (h z) ^ 2) = z₀ * h z ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  -- step 2: `(h z - h t) ^ 2 ≤ z₀ * B`, then integrate in `t`
  have hpt2 : ∀ t ∈ Set.Icc z₀ (2 * z₀), (h z - h t) ^ 2 ≤ z₀ * B := by
    intro t ht
    exact diff_sq_le hz₀ hFTC hint2 hz ht
  have hmono2 := intervalIntegral.integral_mono_on hz₂ hint_diff intervalIntegrable_const hpt2
  have hconst2 : (∫ t in z₀..(2 * z₀), z₀ * B) = z₀ * (z₀ * B) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hJ : (∫ t in z₀..(2 * z₀), (h z - h t) ^ 2) ≤ z₀ * (z₀ * B) := by
    have hh := hmono2
    rwa [hconst2] at hh
  -- split the integral of the sum
  have hsplit1 : (∫ t in z₀..(2 * z₀), (2 * h t ^ 2 + 2 * (h z - h t) ^ 2))
      = (∫ t in z₀..(2 * z₀), 2 * h t ^ 2) + (∫ t in z₀..(2 * z₀), 2 * (h z - h t) ^ 2) :=
    intervalIntegral.integral_add (hint1.const_mul 2) (hint_diff.const_mul 2)
  have hsplit2 : (∫ t in z₀..(2 * z₀), 2 * h t ^ 2) = 2 * (∫ t in z₀..(2 * z₀), h t ^ 2) :=
    intervalIntegral.integral_const_mul 2 (fun t => h t ^ 2)
  have hsplit3 : (∫ t in z₀..(2 * z₀), 2 * (h z - h t) ^ 2)
      = 2 * (∫ t in z₀..(2 * z₀), (h z - h t) ^ 2) :=
    intervalIntegral.integral_const_mul 2 (fun t => (h z - h t) ^ 2)
  have hsplit : (∫ t in z₀..(2 * z₀), (2 * h t ^ 2 + 2 * (h z - h t) ^ 2))
      = 2 * (∫ t in z₀..(2 * z₀), h t ^ 2) + 2 * (∫ t in z₀..(2 * z₀), (h z - h t) ^ 2) := by
    rw [hsplit1, hsplit2, hsplit3]
  -- the chain, multiplied by `z₀`
  have hchain : z₀ * h z ^ 2 ≤ 2 * (∫ t in z₀..(2 * z₀), h t ^ 2) + 2 * (z₀ * (z₀ * B)) := by
    rw [← hconst1]
    calc (∫ t in z₀..(2 * z₀), (h z) ^ 2)
        ≤ ∫ t in z₀..(2 * z₀), (2 * h t ^ 2 + 2 * (h z - h t) ^ 2) := hmono1
      _ = 2 * (∫ t in z₀..(2 * z₀), h t ^ 2) + 2 * (∫ t in z₀..(2 * z₀), (h z - h t) ^ 2) := hsplit
      _ ≤ 2 * (∫ t in z₀..(2 * z₀), h t ^ 2) + 2 * (z₀ * (z₀ * B)) := by linarith [hJ]
  -- divide by `z₀ > 0`
  have hgoal_rhs : (2 / z₀) * (∫ t in z₀..(2 * z₀), h t ^ 2) + (2 * z₀) * B
      = (2 * (∫ t in z₀..(2 * z₀), h t ^ 2) + 2 * (z₀ * (z₀ * B))) / z₀ := by
    field_simp
  rw [hgoal_rhs, le_div_iff₀ hz₀]
  linarith [hchain]

end Work.FTS.H2.CruxPair
