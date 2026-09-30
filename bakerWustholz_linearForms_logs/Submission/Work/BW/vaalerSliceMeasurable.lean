import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory

/-- Vaaler slice measurability: for a closed set `C ⊆ ℝ^{n+1}` and measurable weight
functions `h i : ℝ → ℝ`, the slice integral
`s ↦ ∫ y in {x | Fin.insertNth k s x ∈ C}, ∏ i, h i (y i)`
is a measurable function of `s`.

The slice set is measured in the `k`-th coordinate; `Fin.insertNth k s x` inserts `s`
in position `k` and fills the remaining `n` coordinates with `x`, so the slice is
`{x | Fin.insertNth k s x ∈ C}`.  The integrand depends on `x` only, so it is the
indicator of a measurable set times a measurable function of `x`; uncurrying the
resulting expression in `(x, s)` gives a jointly measurable function, and the Bochner
integral over the first variable of a jointly measurable function is measurable in the
second variable (`MeasureTheory.StronglyMeasurable.integral_prod_left`). -/
theorem vaalerSliceMeasurable {n : ℕ} (C : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (hcl : IsClosed C) (h : Fin n → ℝ → ℝ)
    (hh_meas : ∀ i, Measurable (h i)) :
    Measurable (fun s : ℝ => ∫ y in {x : Fin n → ℝ | Fin.insertNth k s x ∈ C}, ∏ i, h i (y i)) := by
  classical
  -- Each slice is a closed, hence measurable, subset of `Fin n → ℝ`.
  have hS : ∀ s : ℝ, MeasurableSet {x : Fin n → ℝ | Fin.insertNth k s x ∈ C} :=
    fun s => hcl.measurableSet.preimage (by fun_prop)
  -- The weight `x ↦ ∏ i, h i (x i)` is measurable.
  have hG : Measurable (fun p : (Fin n → ℝ) × ℝ => ∏ i, h i (p.1 i)) := by
    refine Finset.measurable_prod _ (fun i _ => ?_)
    exact (hh_meas i).comp (by fun_prop)
  -- Indicator of the slice condition times the weight, as a function of `(x, s)`.
  have hjoint : Measurable (fun p : (Fin n → ℝ) × ℝ =>
      (if Fin.insertNth k p.2 p.1 ∈ C then ∏ i, h i (p.1 i) else (0:ℝ))) :=
    Measurable.ite (hcl.measurableSet.preimage (by fun_prop)) hG measurable_const
  have hkey : (fun s : ℝ => ∫ y in {x : Fin n → ℝ | Fin.insertNth k s x ∈ C}, ∏ i, h i (y i))
      = fun s : ℝ => ∫ y : Fin n → ℝ, (fun p : (Fin n → ℝ) × ℝ =>
          (if Fin.insertNth k p.2 p.1 ∈ C then ∏ i, h i (p.1 i) else (0:ℝ))) (y, s) := by
    funext s
    rw [← MeasureTheory.integral_indicator (hS s)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [Set.indicator_apply]
    by_cases hy : Fin.insertNth k s y ∈ C <;> simp [hy]
  rw [hkey]
  exact hjoint.stronglyMeasurable.integral_prod_left.measurable

end Work.BW
