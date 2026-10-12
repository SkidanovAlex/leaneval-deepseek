import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

/-- **Cauchy–Schwarz for the Bochner integral of real `L²` functions.**

For `f`, `g` in `L²(μ)` one has `(∫ f·g)² ≤ (∫ f²)·(∫ g²)`. This is the `p = q = 2`
(Hölder) case: `|∫ f g| ≤ ∫ |f| |g| ≤ (∫ f²)^{1/2} (∫ g²)^{1/2}`, squared.

It is the unweighted, unbounded counterpart of `Q0C.integral_mul_sq_le`
(`Submission/Work/BoseFixB1S/BoxQIndCore.lean`), which assumes both functions to be
a.e.-bounded; the present version only needs `MemLp _ 2`. -/
theorem integral_mul_sq_le_of_memLp {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℝ} (hf : MeasureTheory.MemLp f 2 μ) (hg : MeasureTheory.MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by simpa using hg
  -- Hölder with conjugate exponents `p = q = 2`, applied to the norms.
  have hmain := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g)
    (p := 2) (q := 2) Real.HolderConjugate.two_two hf' hg'
  -- turn the `p`-th powers of the norms into squares
  have hsqf : (fun x => ‖f x‖ ^ (2 : ℝ)) = fun x => f x ^ 2 := by
    funext x; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have hsqg : (fun x => ‖g x‖ ^ (2 : ℝ)) = fun x => g x ^ 2 := by
    funext x; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hsqf, hsqg] at hmain
  have hF : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hG : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hsqrtf : ((∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hF, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
      Real.rpow_one]
  have hsqrtg : ((∫ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 = ∫ x, g x ^ 2 ∂μ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hG, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
      Real.rpow_one]
  have hkey : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
    have hA : 0 ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ :=
      integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have h1 := pow_le_pow_left₀ hA hmain 2
    rw [mul_pow, hsqrtf, hsqrtg] at h1
    exact h1
  have habs : |∫ x, f x * g x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hle := abs_le.mp habs
  calc (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ^ 2 := sq_le_sq' hle.1 hle.2
    _ ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := hkey

/-- **`L²` bound on the integral of a function supported in a set of finite measure.**

If `f ∈ L²(μ)` vanishes outside a measurable set `s` with `μ s ≠ ⊤`, then

    (∫ f)² ≤ (∫ f²) · (μ s).toReal,

i.e. `f` is Cauchy–Schwarz dominated by the indicator of `s`. Equivalently, this is the
Hölder inequality `|∫ f| ≤ ‖f‖_{L²} · ‖1_s‖_{L²}` with `‖1_s‖_{L²}² = μ s`, squared. -/
theorem integral_sq_le_measure_mul_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s : Set α} (hs : MeasurableSet s) (hsfin : μ s ≠ ⊤)
    {f : α → ℝ} (hfm : MeasureTheory.MemLp f 2 μ) (hf : ∀ x ∉ s, f x = 0) :
    (∫ x, f x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (μ s).toReal := by
  -- the indicator of `s` is in `L²` because `μ s` is finite
  have hgm : MemLp (s.indicator (fun _ => (1 : ℝ))) 2 μ :=
    memLp_indicator_const 2 hs 1 (Or.inr hsfin)
  have hCS := integral_mul_sq_le_of_memLp hfm hgm
  -- `f · 1_s = f` pointwise, since `f` vanishes off `s`
  have hfg : (∫ x, f x * s.indicator (fun _ => (1 : ℝ)) x ∂μ) = ∫ x, f x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, mul_one]
    · rw [Set.indicator_of_notMem hx, mul_zero, hf x hx]
  -- `1_s² = 1_s`, whose integral is `(μ s).toReal`
  have hg2 : (∫ x, (s.indicator (fun _ => (1 : ℝ)) x) ^ 2 ∂μ) = (μ s).toReal := by
    have hpt : (fun x => (s.indicator (fun _ => (1 : ℝ)) x) ^ 2)
        = s.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx]; norm_num
      · rw [Set.indicator_of_notMem hx]; norm_num
    rw [hpt, integral_indicator hs, setIntegral_const]
    simp [measureReal_def]
  calc (∫ x, f x ∂μ) ^ 2 = (∫ x, f x * s.indicator (fun _ => (1 : ℝ)) x ∂μ) ^ 2 := by
        rw [hfg]
    _ ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, (s.indicator (fun _ => (1 : ℝ)) x) ^ 2 ∂μ) := hCS
    _ = (∫ x, f x ^ 2 ∂μ) * (μ s).toReal := by rw [hg2]

end Work.BoseFixB1S
