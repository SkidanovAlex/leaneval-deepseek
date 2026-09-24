import Mathlib
import Submission.Work.ChenPlan.H2.Tab

/-!
# The window sum of the linear-sieve upper envelope

`utab_table_sum_le` bounds the numerical core of Chen's `h2`:

`Σ_k Utab(s_k) · log ((σ - s_k)/(σ - s_{k+1})) ≤ 1.551`

at `σ = 5`, `s_k = 3/2 + k/20`, the `min`/`max` clamps coming from the ends of the window
`q ∈ [M, Y)`: the numerator `7/2 - k/20 = 5 - s_k` is capped by `10/3` when the cell reaches
past the top of the window, and the denominator `max 1 (7/2 - (k+1)/20)` corresponds to `q ≥ M`.

The logarithm is controlled by the trapezoid (logarithmic-mean) bound
`log (v/u) ≤ (v - u)(1/u + 1/v)/2` for `0 < u ≤ v`, which follows from the elementary
inequality `2 log x ≤ x - x⁻¹` (`x ≥ 1`) by monotonicity of `x ↦ x - x⁻¹ - 2 log x`.
The remaining estimate is a purely rational computation (`norm_num`); the resulting bound is
`≈ 1.54937 < 1.551`.
-/

namespace Work.ChenPlan.H2

open Finset

/-- Logarithmic-mean bound: `2 log x ≤ x - x⁻¹` for `x ≥ 1`.
It follows from `x ↦ x - x⁻¹ - 2 log x` being nondecreasing on `[1, ∞)`, with derivative
`(x-1)²/x² ≥ 0`, and vanishing at `x = 1`. -/
private lemma two_mul_log_le_sub_inv {x : ℝ} (hx : 1 ≤ x) : 2 * Real.log x ≤ x - x⁻¹ := by
  have hmono : MonotoneOn (fun y : ℝ => y - y⁻¹ - 2 * Real.log y) (Set.Ici 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (f' := fun y : ℝ => 1 - (-(y^2)⁻¹) - 2 * y⁻¹) ?_ ?_ ?_
    · have hid : ContinuousOn (fun y : ℝ => y) (Set.Ici 1) := continuous_id.continuousOn
      have hinv : ContinuousOn (fun y : ℝ => y⁻¹) (Set.Ici 1) :=
        continuousOn_inv₀.mono (by intro y hy; exact ne_of_gt (lt_of_lt_of_le zero_lt_one hy))
      have hlog : ContinuousOn (fun y : ℝ => Real.log y) (Set.Ici 1) :=
        Real.continuousOn_log.mono (by intro y hy; exact ne_of_gt (lt_of_lt_of_le zero_lt_one hy))
      exact (hid.sub hinv).sub (hlog.const_mul 2)
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
      have h12 : HasDerivAt (fun y : ℝ => y - y⁻¹) (1 - (-(y^2)⁻¹)) y :=
        (hasDerivAt_id y).sub (hasDerivAt_inv hy0)
      have h3 : HasDerivAt (fun y : ℝ => 2 * Real.log y) (2 * y⁻¹) y :=
        (Real.hasDerivAt_log hy0).const_mul 2
      exact (h12.sub h3).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : 0 < y := lt_trans zero_lt_one hy
      have h : 1 - (-(y^2)⁻¹) - 2 * y⁻¹ = (y - 1)^2 * (y^2)⁻¹ := by
        field_simp
        ring
      rw [h]
      exact mul_nonneg (sq_nonneg _) (by positivity)
  have h1 : (1 : ℝ) ∈ Set.Ici 1 := by simp
  have h2 := hmono h1 hx hx
  have hf1 : (fun y : ℝ => y - y⁻¹ - 2 * Real.log y) 1 = 0 := by norm_num
  rw [hf1] at h2
  linarith

/-- The trapezoid bound for the logarithm of a ratio: for `0 < u ≤ v`,
`log (v/u) ≤ (v - u)(1/u + 1/v)/2`. -/
private lemma log_div_le_trapezoid {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Real.log (v / u) ≤ (v - u) * (1 / u + 1 / v) / 2 := by
  have h1 : 1 ≤ v / u := by
    rw [le_div_iff₀ hu]
    simpa using huv
  have h2 := two_mul_log_le_sub_inv h1
  have h3 : (v - u) * (1 / u + 1 / v) / 2 * 2 = v / u - (v / u)⁻¹ := by
    have hv0 : v ≠ 0 := ne_of_gt (lt_of_lt_of_le hu huv)
    field_simp
    ring
  linarith

/-- The `max 0` version of the trapezoid bound, valid in the regime `0 ≤ v` (which covers all
window cells, since the numerator `5 - s_k` is nonnegative there). -/
private lemma max_log_div_le {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    max 0 (Real.log (v / u)) ≤ max 0 ((v - u) * (1 / u + 1 / v) / 2) := by
  rcases le_total u v with h | h
  · exact max_le_max le_rfl (log_div_le_trapezoid hu h)
  · have hvu : v / u ≤ 1 := by
      rw [div_le_one hu]
      exact h
    have h0 : 0 ≤ v / u := div_nonneg hv hu.le
    have hlog : Real.log (v / u) ≤ 0 := Real.log_nonpos h0 hvu
    calc max 0 (Real.log (v / u)) = 0 := max_eq_left hlog
      _ ≤ max 0 ((v - u) * (1 / u + 1 / v) / 2) := le_max_left _ _

/-- The numerator of the `k`-th window cell: `min (5 - s_k) (10/3)`. -/
private noncomputable def wnum (k : ℕ) : ℝ := min ((7 : ℝ) / 2 - (k : ℝ) / 20) (10 / 3)

/-- The denominator of the `k`-th window cell: `max 1 (5 - s_{k+1})`. -/
private noncomputable def wden (k : ℕ) : ℝ := max 1 ((7 : ℝ) / 2 - ((k : ℝ) + 1) / 20)

/-- The trapezoid majorant of the `k`-th summand. -/
private noncomputable def wtrap (k : ℕ) : ℝ := (wnum k - wden k) * (1 / wden k + 1 / wnum k) / 2

theorem utab_table_sum_le :
    (∑ k ∈ Finset.range 71, ((Work.ChenPlan.H2.utabQ k : ℚ) : ℝ)
        * max 0 (Real.log (min ((7 : ℝ) / 2 - (k : ℝ) / 20) (10 / 3)
            / max 1 ((7 : ℝ) / 2 - ((k : ℝ) + 1) / 20))))
      ≤ 1.551 := by
  show (∑ k ∈ Finset.range 71, ((utabQ k : ℚ) : ℝ) * max 0 (Real.log (wnum k / wden k)))
      ≤ 1.551
  have step : ∀ k ∈ Finset.range 71,
      ((utabQ k : ℚ) : ℝ) * max 0 (Real.log (wnum k / wden k))
        ≤ |((utabQ k : ℚ) : ℝ)| * max 0 (wtrap k) := by
    intro k hk
    have hk70 : k ≤ 70 := by have := Finset.mem_range.mp hk; omega
    have hu : 0 < wden k := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hv : 0 ≤ wnum k := by
      simp only [wnum]
      refine le_min ?_ (by norm_num)
      have hkR : (k : ℝ) ≤ 70 := by exact_mod_cast hk70
      linarith
    have hAB : max 0 (Real.log (wnum k / wden k)) ≤ max 0 (wtrap k) := by
      simp only [wtrap]
      exact max_log_div_le hu hv
    have hA0 : 0 ≤ max 0 (Real.log (wnum k / wden k)) := le_max_left _ _
    have hB0 : 0 ≤ max 0 (wtrap k) := le_max_left _ _
    rcases le_total 0 ((utabQ k : ℚ) : ℝ) with hw | hw
    · rw [abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left hAB hw
    · rw [abs_of_nonpos hw]
      have h1 : ((utabQ k : ℚ) : ℝ) * max 0 (Real.log (wnum k / wden k)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hw hA0
      have h2 : 0 ≤ (-((utabQ k : ℚ) : ℝ)) * max 0 (wtrap k) :=
        mul_nonneg (neg_nonneg.mpr hw) hB0
      linarith
  refine le_trans (Finset.sum_le_sum step) ?_
  simp only [wtrap, wnum, wden, utabQ, tabQ, Submission.ChenPlan.utabList,
    Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  norm_num

end Work.ChenPlan.H2
