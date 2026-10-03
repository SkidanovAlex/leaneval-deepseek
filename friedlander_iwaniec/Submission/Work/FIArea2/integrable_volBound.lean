/-
# Integrability of the dominating function `volBound` of FI Lemma 7.1

`volBound M C` is the sum of two indicator functions:

* `√6 · r` on the compact interval `[-r, r]` with `r = √(4√M)`, and
* `4√2 √M / |x|` on the annulus `(-T, -s) ∪ (s, T)` with `s = min r T`, `T = √((C + 2√M)/2)`.

The first is a bounded function supported on a compact set.  On the annulus the second is dominated
by the constant `4√2 √M / s`, which is finite because `M ≥ 1` forces `s = min r T ≥ 1` (indeed
`r ≥ 2` and `T ≥ 1`).  Hence `volBound M C` is dominated a.e. by the (integrable) function
`κ · 1_{[-A,A]}` with `A = max r T` and `κ = √6 r + 4√2 √M / s`, which is what integrability
requires (`Integrable.mono'`).
-/
import Mathlib
import Submission.Work.FIArea2.vol_bound_defs

namespace Work.FIArea2

noncomputable section

open MeasureTheory

/-- `volBound M C` is (Borel) measurable: it is a sum of two indicator functions, of a compact
interval and of an open annulus, applied to measurable functions. -/
lemma measurable_volBound (M C : ℝ) : Measurable (volBound M C) := by
  unfold volBound
  apply Measurable.add
  · exact measurable_const.indicator measurableSet_Icc
  · refine Measurable.indicator (measurable_const.div measurable_abs) ?_
    exact measurableSet_Ioo.union measurableSet_Ioo

/-- `volS M C = min (volR M) (volT M C) ≥ 1` when `1 ≤ M` and `0 ≤ C`: both `volR M = √(4√M) ≥ 2`
and `volT M C = √((C + 2√M)/2) ≥ 1`.  In particular the annulus on which the second summand of
`volBound` lives stays away from the origin. -/
lemma one_le_volS (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) : 1 ≤ volS M C := by
  rw [volS_eq, le_min_iff]
  constructor
  · rw [volR, ← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have h1 : (1 : ℝ) ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM
    linarith
  · rw [volT, ← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have h1 : (1 : ℝ) ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM
    linarith

theorem integrable_volBound (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    MeasureTheory.Integrable (volBound M C) := by
  obtain ⟨A, hRA, hTA⟩ : ∃ A, volR M ≤ A ∧ volT M C ≤ A :=
    ⟨max (volR M) (volT M C), le_max_left _ _, le_max_right _ _⟩
  have hS1 : 1 ≤ volS M C := one_le_volS M C hM hC
  have hSpos : 0 < volS M C := lt_of_lt_of_le one_pos hS1
  -- the dominating (integrable) function `κ · 1_{[-A,A]}`
  have hg : Integrable (fun x : ℝ =>
      (Real.sqrt 6 * volR M + 4 * Real.sqrt 2 * Real.sqrt M / volS M C) *
        (Set.Icc (-A) A).indicator (fun _ => (1 : ℝ)) x) := by
    have h1 : Integrable ((Set.Icc (-A) A).indicator (fun _ => (1 : ℝ))) := by
      rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (measure_Icc_lt_top.ne)
    exact h1.const_mul _
  refine Integrable.mono' hg (measurable_volBound M C).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (volBound_nonneg M C x)]
  by_cases hxA : x ∈ Set.Icc (-A) A
  · -- on `[-A,A]` the dominating function is the constant `κ`; bound each summand by its part of `κ`
    rw [Set.indicator_of_mem hxA, mul_one]
    have h1 : (Set.Icc (-(volR M)) (volR M)).indicator (fun _ => Real.sqrt 6 * volR M) x
        ≤ Real.sqrt 6 * volR M := by
      by_cases h : x ∈ Set.Icc (-(volR M)) (volR M)
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]
        exact mul_nonneg (Real.sqrt_nonneg 6) (volR_nonneg M)
    have h2 : (Set.Ioo (-(volT M C)) (-(volS M C)) ∪ Set.Ioo (volS M C) (volT M C)).indicator
          (fun x => 4 * Real.sqrt 2 * Real.sqrt M / |x|) x
        ≤ 4 * Real.sqrt 2 * Real.sqrt M / volS M C := by
      by_cases h : x ∈ Set.Ioo (-(volT M C)) (-(volS M C)) ∪ Set.Ioo (volS M C) (volT M C)
      · rw [Set.indicator_of_mem h]
        rcases h with h | h
        · -- `-T < x < -s`: then `|x| = -x > s`
          have hx0 : x < 0 := lt_of_lt_of_le h.2 (neg_nonpos.mpr (le_of_lt hSpos))
          rw [abs_of_neg hx0]
          exact div_le_div_of_nonneg_left (by positivity) hSpos (by linarith [h.2])
        · -- `s < x < T`: then `|x| = x > s`
          have hx0 : 0 < x := lt_trans hSpos h.1
          rw [abs_of_pos hx0]
          exact div_le_div_of_nonneg_left (by positivity) hSpos (by linarith [h.1])
      · rw [Set.indicator_of_notMem h]
        positivity
    simp only [volBound, Pi.add_apply]
    linarith
  · -- outside `[-A,A]` both summands vanish
    rw [Set.indicator_of_notMem hxA, mul_zero]
    have h1 : x ∉ Set.Icc (-(volR M)) (volR M) := by
      intro h; exact hxA ⟨by linarith [h.1, hRA], by linarith [h.2, hRA]⟩
    have h2 : x ∉ Set.Ioo (-(volT M C)) (-(volS M C)) ∪ Set.Ioo (volS M C) (volT M C) := by
      intro h
      apply hxA
      rcases h with h | h
      · exact ⟨by linarith [h.1, hTA], by linarith [h.2, hSpos, volR_nonneg M, hRA]⟩
      · exact ⟨by linarith [h.1, hSpos, volR_nonneg M, hRA], by linarith [h.2, hTA]⟩
    simp only [volBound, Pi.add_apply, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
      add_zero]
    exact le_refl 0

end

end Work.FIArea2
