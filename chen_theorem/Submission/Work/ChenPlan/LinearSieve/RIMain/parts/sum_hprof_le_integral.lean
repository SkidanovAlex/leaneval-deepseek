import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RIMain.abel_pointwise_defs
import Submission.Work.ChenPlan.LinearSieve.Abel.integral_step_bound

/-!
# The Abel step bound for the extremal profile `hprof K Z`

`hprof K Z u = (1 + K/log u)·(log Z/log u)` is the extremal profile of the linear sieve
(`RIMain.abel_pointwise_defs`).  This file proves that the Abel sum of the *drop* of `hprof`
against a non-decreasing, non-negative weight `Φ` is dominated by its logarithmic integral:

`Σ_{k<n} (hprof(P k) - hprof(P(k+1)))·Φ(P k) ≤ ∫_w^Z Φ(u)·log Z/(u log²u)·(1 + 2K/log u) du`

for every non-decreasing `P` with `w ≤ P 0` and `P n = Z`.  The density on the right is exactly
`-d/du hprof K Z u`, so the statement is the "sum ≤ integral" comparison for a decreasing
profile, term by term on the consecutive intervals `[P k, P (k+1)]` which tile `[P 0, P n] =
[P 0, Z] ⊆ [w, Z]`.

## Structure

* `step_bound_of_deriv` — the abstract comparison: for any profile `a` with `a' = -dens`
  (`dens ≥ 0`, continuous) on `[w, Z]`, the Abel sum of `a` against a globally monotone,
  non-negative weight `g` is at most `∫_w^Z g·dens`.
* `sum_hprof_le_integral` — the clamped-`Φ` transfer of that comparison to `a = hprof K Z`
  and `dens = log Z/(u log²u)·(1 + 2K/log u)`, since `Φ` is only monotone on `[w, Z]` (it need
  not even be measurable), exactly as in `Abel.integral_step_bound`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.RIMain.parts

/-- **Sum ≤ integral for a decreasing differentiable profile.**  If `dens` is non-negative and
continuous on `[w, Z]` and `a' = -dens` there, then for every non-decreasing `P` with
`w ≤ P 0` and `P n = Z` the Abel sum `Σ (a (P k) - a (P (k+1)))·g (P k)` of the drops of `a`
against a globally non-decreasing non-negative `g` is bounded by `∫_w^Z g·dens`.

The proof splits the sum over the consecutive intervals `[P k, P (k+1)]` (which tile `[P 0, Z]`):
on each of them the fundamental theorem of calculus gives
`a (P k) - a (P (k+1)) = ∫_{P k}^{P (k+1)} dens`, and since `g (u) ≥ g (P k)` and `dens ≥ 0`
on the interval, the constant `g (P k)` may be replaced by `g u` inside the integral. -/
private theorem step_bound_of_deriv {n : ℕ} {P : ℕ → ℝ} (hPmono : Monotone P)
    {w Z : ℝ} (hwP0 : w ≤ P 0) (hPn : P n = Z)
    {a dens : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Icc w Z, HasDerivAt (fun y => -a y) (dens x) x)
    (hcont : ContinuousOn dens (Set.Icc w Z))
    (hdensnn : ∀ x ∈ Set.Icc w Z, 0 ≤ dens x)
    {g : ℝ → ℝ} (hgmono : Monotone g) (hgnn : ∀ u : ℝ, 0 ≤ g u) :
    ∑ i ∈ Finset.range n, (a (P i) - a (P (i + 1))) * g (P i)
      ≤ ∫ u in w..Z, g u * dens u := by
  have hPw : ∀ i : ℕ, w ≤ P i := fun i => le_trans hwP0 (hPmono (Nat.zero_le i))
  have hPZ : ∀ i : ℕ, i ≤ n → P i ≤ Z := fun i hi => by rw [← hPn]; exact hPmono hi
  have hsubI : ∀ p q : ℝ, w ≤ p → p ≤ q → q ≤ Z → Set.Icc p q ⊆ Set.Icc w Z :=
    fun p q hp _ hq => Set.Icc_subset_Icc hp hq
  have hsubu : ∀ p q : ℝ, w ≤ p → p ≤ q → q ≤ Z → Set.uIcc p q ⊆ Set.Icc w Z :=
    fun p q hp hpq hq => by rw [Set.uIcc_of_le hpq]; exact Set.Icc_subset_Icc hp hq
  -- the term-by-term comparison on `[P i, P (i+1)]`
  have key : ∀ i : ℕ, i < n →
      (a (P i) - a (P (i + 1))) * g (P i)
        ≤ ∫ u in P i..P (i+1), g u * dens u := by
    intro i hi
    have hab : P i ≤ P (i + 1) := hPmono (Nat.le_succ i)
    have hPi : w ≤ P i := hPw i
    have hPsucc : P (i+1) ≤ Z := hPZ (i+1) (Nat.succ_le_of_lt hi)
    have hci : ContinuousOn dens (Set.uIcc (P i) (P (i+1))) :=
      hcont.mono (hsubu (P i) (P (i+1)) hPi hab hPsucc)
    have hint_d : IntervalIntegrable dens MeasureTheory.volume (P i) (P (i+1)) :=
      hci.intervalIntegrable
    -- fundamental theorem of calculus for the drop of `a`
    have hftc : ∫ u in P i..P (i+1), dens u = a (P i) - a (P (i + 1)) := by
      have hd : ∀ x ∈ Set.uIcc (P i) (P (i+1)), HasDerivAt (fun y => -a y) (dens x) x :=
        fun x hx => hderiv x (hsubu (P i) (P (i+1)) hPi hab hPsucc hx)
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint_d
      rw [h]
      ring
    have hf : IntervalIntegrable (fun u => g u * dens u) MeasureTheory.volume (P i) (P (i+1)) :=
      hgmono.intervalIntegrable.mul_continuousOn hci
    have hc : IntervalIntegrable (fun u => g (P i) * dens u) MeasureTheory.volume (P i) (P (i+1)) :=
      hint_d.const_mul (g (P i))
    have hstep : ∫ u in P i..P (i+1), g (P i) * dens u ≤ ∫ u in P i..P (i+1), g u * dens u := by
      refine intervalIntegral.integral_mono_on hab hc hf (fun u hu => ?_)
      exact mul_le_mul_of_nonneg_right (hgmono hu.1)
        (hdensnn u (hsubI (P i) (P (i+1)) hPi hab hPsucc hu))
    calc (a (P i) - a (P (i+1))) * g (P i)
        = g (P i) * (a (P i) - a (P (i+1))) := by ring
      _ = g (P i) * ∫ u in P i..P (i+1), dens u := by rw [hftc]
      _ = ∫ u in P i..P (i+1), g (P i) * dens u :=
          (intervalIntegral.integral_const_mul (g (P i)) dens).symm
      _ ≤ ∫ u in P i..P (i+1), g u * dens u := hstep
  have hsum := Finset.sum_le_sum (fun i hi => key i (Finset.mem_range.mp hi))
  have hP0n : P 0 ≤ P n := hPmono (Nat.zero_le n)
  -- the intervals tile `[P 0, P n]`
  have hint_all : ∀ k < n,
      IntervalIntegrable (fun u => g u * dens u) MeasureTheory.volume (P k) (P (k+1)) :=
    fun k hk => hgmono.intervalIntegrable.mul_continuousOn
      (hcont.mono (hsubu (P k) (P (k+1)) (hPw k) (hPmono (Nat.le_succ k))
        (hPZ (k+1) (Nat.succ_le_of_lt hk))))
  have htel : ∑ i ∈ Finset.range n, ∫ u in P i..P (i+1), g u * dens u
      = ∫ u in P 0..P n, g u * dens u :=
    intervalIntegral.sum_integral_adjacent_intervals hint_all
  -- and the integral grows from `[P 0, Z]` to `[w, Z]` (the density is non-negative)
  have hA : IntervalIntegrable (fun u => g u * dens u) MeasureTheory.volume w (P 0) :=
    hgmono.intervalIntegrable.mul_continuousOn
      (hcont.mono (hsubu w (P 0) le_rfl hwP0 (by rw [← hPn]; exact hP0n)))
  have hB : IntervalIntegrable (fun u => g u * dens u) MeasureTheory.volume (P 0) Z :=
    hgmono.intervalIntegrable.mul_continuousOn
      (hcont.mono (hsubu (P 0) Z (hPw 0) (by rw [← hPn]; exact hP0n) le_rfl))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hA hB
  have hnn_wP0 : 0 ≤ ∫ u in w..P 0, g u * dens u :=
    intervalIntegral.integral_nonneg hwP0
      (fun u hu => mul_nonneg (hgnn u)
        (hdensnn u (hsubI w (P 0) le_rfl hwP0 (by rw [← hPn]; exact hP0n) hu)))
  calc ∑ i ∈ Finset.range n, (a (P i) - a (P (i + 1))) * g (P i)
      ≤ ∑ i ∈ Finset.range n, ∫ u in P i..P (i+1), g u * dens u := hsum
    _ = ∫ u in P 0..P n, g u * dens u := htel
    _ = ∫ u in P 0..Z, g u * dens u := by rw [hPn]
    _ ≤ ∫ u in w..Z, g u * dens u := by linarith [hsplit, hnn_wP0]

theorem sum_hprof_le_integral {K w Z : ℝ} (hK : 0 ≤ K) (hw : 2 ≤ w) (hwZ : w ≤ Z)
    {n : ℕ} {P : ℕ → ℝ} (hPmono : Monotone P) (hP0 : w ≤ P 0) (hPn : P n = Z)
    {Φ : ℝ → ℝ} (hΦmono : ∀ a b : ℝ, w ≤ a → a ≤ b → b ≤ Z → Φ a ≤ Φ b)
    (hΦnn : ∀ a : ℝ, w ≤ a → a ≤ Z → 0 ≤ Φ a) :
    ∑ k ∈ Finset.range n,
        (Work.ChenPlan.LinearSieve.RIMain.hprof K Z (P k)
          - Work.ChenPlan.LinearSieve.RIMain.hprof K Z (P (k + 1))) * Φ (P k)
      ≤ ∫ u in w..Z,
          Φ u * (Real.log Z / (u * (Real.log u) ^ 2)) * (1 + 2 * K / Real.log u) := by
  classical
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  -- `Φ` is only monotone on `[w, Z]`; clamp it there to make it globally monotone
  set Ψ : ℝ → ℝ := fun u => Φ (max w (min u Z)) with hΨdef
  have hclamp_le : ∀ u : ℝ, max w (min u Z) ≤ Z := fun u => max_le hwZ (min_le_right _ _)
  have hclamp_ge : ∀ u : ℝ, w ≤ max w (min u Z) := fun u => le_max_left _ _
  have hΨmono : Monotone Ψ := by
    intro a b hab
    exact hΦmono _ _ (hclamp_ge a) (max_le_max le_rfl (min_le_min hab le_rfl)) (hclamp_le b)
  have hΨnn : ∀ u : ℝ, 0 ≤ Ψ u := fun u => hΦnn _ (hclamp_ge u) (hclamp_le u)
  have hΨeq : ∀ u : ℝ, w ≤ u → u ≤ Z → Ψ u = Φ u := by
    intro u h1 h2
    show Φ (max w (min u Z)) = Φ u
    rw [min_eq_left h2, max_eq_right h1]
  -- the antiderivative relation `d/du (-hprof K Z u) = log Z/(u log²u)·(1 + 2K/log u)`
  have hderiv : ∀ x ∈ Set.Icc w Z, HasDerivAt (fun y : ℝ => -hprof K Z y)
      ((Real.log Z / (x * (Real.log x)^2)) * (1 + 2*K/Real.log x)) x := by
    intro x hx
    have hx1 : 1 < x := by linarith [hx.1, hw]
    have hx0 : x ≠ 0 := by linarith
    have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    have hN : HasDerivAt (fun y : ℝ => -(Real.log Z) * (Real.log y + K))
        (-(Real.log Z) * x⁻¹) x :=
      ((Real.hasDerivAt_log hx0).add_const K).const_mul (-(Real.log Z))
    have hD : HasDerivAt (fun y : ℝ => (Real.log y)^2) (2 * (Real.log x)^(2-1) * x⁻¹) x :=
      (Real.hasDerivAt_log hx0).pow 2
    have hDne : (Real.log x)^2 ≠ 0 := pow_ne_zero 2 hlogx
    have hq := hN.div hD hDne
    have hfun : ((fun y : ℝ => -(Real.log Z) * (Real.log y + K)) / fun y : ℝ => (Real.log y)^2)
        = fun y : ℝ => -hprof K Z y := by
      funext y
      simp only [Work.ChenPlan.LinearSieve.RIMain.hprof, Pi.div_apply]
      by_cases h : Real.log y = 0
      · simp [h]
      · field_simp
    have hval : ((-(Real.log Z) * x⁻¹ * (Real.log x)^2
          - -(Real.log Z) * (Real.log x + K) * (2 * (Real.log x)^(2-1) * x⁻¹))
          / ((Real.log x)^2)^2)
        = (Real.log Z / (x * (Real.log x)^2)) * (1 + 2*K/Real.log x) := by
      field_simp
      ring
    rw [hfun] at hq
    rw [hval] at hq
    exact hq
  have hcont : ContinuousOn
      (fun u : ℝ => (Real.log Z / (u * (Real.log u)^2)) * (1 + 2*K/Real.log u))
      (Set.Icc w Z) := by
    intro x hx
    have hx1 : 1 < x := by linarith [hx.1, hw]
    have hx0 : x ≠ 0 := by linarith
    have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    have hl : ContinuousAt Real.log x := Real.continuousAt_log hx0
    have hden : ContinuousAt (fun u : ℝ => u * (Real.log u)^2) x :=
      continuousAt_id.mul (hl.pow 2)
    have hA : ContinuousAt (fun u : ℝ => Real.log Z / (u * (Real.log u)^2)) x :=
      continuousAt_const.div hden (mul_ne_zero hx0 (pow_ne_zero 2 hlogx))
    have hB : ContinuousAt (fun u : ℝ => 1 + 2*K/Real.log u) x :=
      continuousAt_const.add (continuousAt_const.div hl hlogx)
    exact (hA.mul hB).continuousWithinAt
  have hdensnn : ∀ x ∈ Set.Icc w Z,
      0 ≤ (Real.log Z / (x * (Real.log x)^2)) * (1 + 2*K/Real.log x) := by
    intro x hx
    have hx1 : 1 < x := by linarith [hx.1, hw]
    have hlogx : 0 < Real.log x := Real.log_pos hx1
    have h1 : 0 ≤ Real.log Z / (x * (Real.log x)^2) := by
      refine div_nonneg (le_of_lt hlogZ) ?_
      have hx0 : 0 < x := by linarith
      positivity
    have h2 : 0 ≤ 1 + 2*K/Real.log x := by
      have h3 : 0 ≤ 2*K/Real.log x := div_nonneg (by linarith) (le_of_lt hlogx)
      linarith
    exact mul_nonneg h1 h2
  have hmain := step_bound_of_deriv (a := Work.ChenPlan.LinearSieve.RIMain.hprof K Z)
    (dens := fun u : ℝ => (Real.log Z / (u * (Real.log u)^2)) * (1 + 2*K/Real.log u))
    hPmono hP0 hPn hderiv hcont hdensnn hΨmono hΨnn
  calc ∑ k ∈ Finset.range n,
        (Work.ChenPlan.LinearSieve.RIMain.hprof K Z (P k)
          - Work.ChenPlan.LinearSieve.RIMain.hprof K Z (P (k + 1))) * Φ (P k)
      = ∑ k ∈ Finset.range n,
        (Work.ChenPlan.LinearSieve.RIMain.hprof K Z (P k)
          - Work.ChenPlan.LinearSieve.RIMain.hprof K Z (P (k + 1))) * Ψ (P k) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hkn : k < n := Finset.mem_range.mp hk
        rw [hΨeq (P k) (le_trans hP0 (hPmono (Nat.zero_le k)))
          (by rw [← hPn]; exact hPmono (le_of_lt hkn))]
    _ ≤ ∫ u in w..Z, Ψ u * ((Real.log Z / (u * (Real.log u)^2)) * (1 + 2*K/Real.log u)) := hmain
    _ = ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2)) * (1 + 2 * K / Real.log u) := by
        refine intervalIntegral.integral_congr (fun u hu => ?_)
        rw [Set.uIcc_of_le hwZ] at hu
        rw [hΨeq u hu.1 hu.2]
        ring

end Work.ChenPlan.LinearSieve.RIMain.parts
