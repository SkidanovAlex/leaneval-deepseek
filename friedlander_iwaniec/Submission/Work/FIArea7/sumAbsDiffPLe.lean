import Mathlib
import Submission.Work.FIArea7.integral_le_of_support_le_K

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Work.FIArea7

/-- **Fundamental theorem of calculus, quantitative form.**  A `C¹` function is bounded in
variation by the integral of the absolute value of its derivative: for `x ≤ y`,
`|f y - f x| ≤ ∫_x^y |f'|`. -/
lemma abs_sub_le_integral_abs_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {x y : ℝ} (hxy : x ≤ y) :
    |f y - f x| ≤ ∫ t in x..y, |deriv f t| := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hcont : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hder : ∀ z ∈ Set.uIcc x y, DifferentiableAt ℝ f z := fun _ _ => hdiff.differentiableAt
  have hint : IntervalIntegrable (deriv f) volume x y := hcont.intervalIntegrable x y
  have h1 : ∫ t in x..y, deriv f t = f y - f x :=
    intervalIntegral.integral_deriv_eq_sub hder hint
  calc |f y - f x| = |∫ t in x..y, deriv f t| := by rw [h1]
    _ ≤ ∫ t in x..y, |deriv f t| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun t => deriv f t) hxy

/-- **The derivative of a function supported in `(a,b]` vanishes off `[a,b]`.**  This uses only
that `P` vanishes identically on a neighbourhood of every point outside `[a,b]` (no smoothness
needed): `P = 0` on `(-∞,a]` and on `(b,∞)`. -/
lemma deriv_eq_zero_of_support {P : ℝ → ℝ} {a b : ℝ}
    (hsupp : ∀ u, P u ≠ 0 → a < u ∧ u ≤ b) :
    ∀ u, u ∉ Set.Icc a b → deriv P u = 0 := by
  intro u hu
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  have hev : P =ᶠ[𝓝 u] 0 := by
    rcases hu with h | h
    · exact Filter.mem_of_superset (isOpen_Iio.mem_nhds h) (fun v hv => by
        by_contra hne
        exact absurd (hsupp v hne).1 (not_lt.mpr (le_of_lt hv)))
    · exact Filter.mem_of_superset (isOpen_Ioi.mem_nhds h) (fun v hv => by
        by_contra hne
        exact absurd (hsupp v hne).2 (not_le.mpr hv))
  simpa using hev.deriv_eq

/-- **Total variation of the smooth weight along an arithmetic progression.**  If `P` is `C¹`,
vanishes outside `(a,b]` and `|P'| ≤ K`, then the discrete total variation of `n ↦ P (c·n)` is at
most the total variation `K(b-a)` of `P`: each difference is bounded by `∫_{c n}^{c(n+1)} |P'|`
and the intervals with non-zero integrand lie inside `[a,b]`. -/
theorem sumAbsDiffPLe {P : ℝ → ℝ} {a b K : ℝ} (hP : ContDiff ℝ 1 P) (ha : 0 ≤ a)
    (hab : a ≤ b) (hsupp : ∀ u, P u ≠ 0 → a < u ∧ u ≤ b) (hder : ∀ u, |deriv P u| ≤ K)
    (c : ℝ) (hc : 0 < c) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, |P (c * n) - P (c * (n + 1))| ≤ K * (b - a) := by
  have hK : 0 ≤ K := by
    have h := hder 0
    have h0 : (0 : ℝ) ≤ |deriv P 0| := abs_nonneg _
    linarith
  have hcont : Continuous (deriv P) := hP.continuous_deriv (by norm_num)
  have hgi : ∀ u v : ℝ, IntervalIntegrable (fun t => |deriv P t|) volume u v :=
    fun u v => (continuous_abs.comp hcont).intervalIntegrable u v
  have hzero : ∀ u, u ∉ Set.Icc a b → |deriv P u| = 0 :=
    fun u hu => by rw [deriv_eq_zero_of_support hsupp u hu, abs_zero]
  -- The primitive `F k = ∫_a^{c k} |P'|`, whose increments telescope the variation sum.
  let F : ℕ → ℝ := fun k => ∫ t in a..(c * (k : ℝ)), |deriv P t|
  have hFsub : ∀ m n : ℕ, F n - F m = ∫ t in (c * (m : ℝ))..(c * (n : ℝ)), |deriv P t| := by
    intro m n
    exact intervalIntegral.integral_interval_sub_left (hgi a _) (hgi a _)
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp only [Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty]
    exact mul_nonneg hK (sub_nonneg.mpr hab)
  · calc ∑ n ∈ Finset.Icc 1 M, |P (c * (n : ℝ)) - P (c * ((n : ℝ) + 1))|
        ≤ ∑ n ∈ Finset.Icc 1 M, (F (n + 1) - F n) := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          have hle : c * (n : ℝ) ≤ c * ((n + 1 : ℕ) : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hc)
            push_cast
            linarith
          have h1 := abs_sub_le_integral_abs_deriv hP
            (x := c * (n : ℝ)) (y := c * ((n + 1 : ℕ) : ℝ)) hle
          rw [abs_sub_comm] at h1
          have hc2 : (c * ((n + 1 : ℕ) : ℝ)) = c * ((n : ℝ) + 1) := by push_cast; ring
          rw [hc2] at h1
          have h2 := hFsub n (n + 1)
          rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 from by push_cast; ring] at h2
          rw [h2]
          exact h1
      _ = F (M + 1) - F 1 := Finset.sum_Icc_sub hM F
      _ ≤ K * (b - a) := by
          rw [hFsub 1 (M + 1)]
          refine integral_le_of_support_le_K (continuous_abs.comp hcont) hab hK hzero
            (fun u => hder u) ?_
          simp only [Nat.cast_one]
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hc)
          push_cast
          linarith

end Work.FIArea7
