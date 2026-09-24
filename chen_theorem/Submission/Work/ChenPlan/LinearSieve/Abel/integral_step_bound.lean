import Mathlib

/-!
# The Abel (Stieltjes) step bound for the linear sieve

This file proves the "sum ≤ integral" comparison used to convert the Abel-summation sum over
primes of the linear sieve into an integral.  Writing `g(u) = log Z / log u` (which is decreasing
on `[w, Z]`, `w ≥ 2`), the drop `g(P i) - g(P (i+1))` of the sieve weight at the prime `P i` is
dominated, term by term, by the integral of `-g'` over the corresponding interval:

`∫_a^b du/(u (log u)^2) = -1/log b + 1/log a`, i.e. `∫_a^b log Z/(u (log u)^2) du = g a - g b`.

Since `Φ` is non-decreasing and non-negative on `[w, Z]`, on `[P i, P (i+1)]` the integrand
`Φ(u)·log Z/(u (log u)^2)` is pointwise at least `Φ(P i)·log Z/(u (log u)^2)`; summing over the
consecutive intervals `[P i, P (i+1)]` (which tile `[P 0, P n] = [P 0, Z]`) and using that the
integrand is non-negative on `[w, P 0]` gives the claim.

The main technical point is that `Φ` is only monotone on `[w, Z]`, so it need not be measurable.
We replace it by the clamped function `u ↦ Φ(max w (min u Z))`, which is globally monotone (hence
measurable and interval integrable) and agrees with `Φ` on `[w, Z]`.
-/

namespace Work.ChenPlan.LinearSieve.Abel

/-- Telescoping the interval integrals over the consecutive intervals `[Q i, Q (i+1)]` for
`i < n` recovers the integral over `[Q 0, Q n]`, when `Q` is monotone. -/
private theorem integral_range_sum {f : ℝ → ℝ} {Q : ℕ → ℝ} (hQ : Monotone Q) (n : ℕ)
    (hint : IntervalIntegrable f MeasureTheory.volume (Q 0) (Q n)) :
    ∑ i ∈ Finset.range n, ∫ u in Q i..Q (i+1), f u = ∫ u in Q 0..Q n, f u := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hQm : Q m ≤ Q (m+1) := hQ (Nat.le_succ m)
    have hQ0m : Q 0 ≤ Q m := hQ (Nat.zero_le m)
    have hsub : Set.uIcc (Q 0) (Q m) ⊆ Set.uIcc (Q 0) (Q (m+1)) := by
      rw [Set.uIcc_of_le hQ0m, Set.uIcc_of_le (le_trans hQ0m hQm)]
      exact Set.Icc_subset_Icc le_rfl hQm
    have hintm : IntervalIntegrable f MeasureTheory.volume (Q 0) (Q m) := hint.mono_set hsub
    have hsub2 : Set.uIcc (Q m) (Q (m+1)) ⊆ Set.uIcc (Q 0) (Q (m+1)) := by
      rw [Set.uIcc_of_le hQm, Set.uIcc_of_le (le_trans hQ0m hQm)]
      exact Set.Icc_subset_Icc hQ0m le_rfl
    have hintlast : IntervalIntegrable f MeasureTheory.volume (Q m) (Q (m+1)) :=
      hint.mono_set hsub2
    rw [Finset.sum_range_succ, ih hintm]
    exact intervalIntegral.integral_add_adjacent_intervals hintm hintlast

/-- The step bound for a globally monotone, non-negative weight `g`:
`Σ_i (g (P i) - g (P (i+1))) · g (P i) ≤ ∫_w^Z g u · log Z / (u (log u)²)`. -/
private theorem step_bound_of_monotone {n : ℕ} {P : ℕ → ℝ} (hPmono : Monotone P)
    {w Z : ℝ} (hw : 2 ≤ w) (hwZ : w ≤ Z) (hwP0 : w ≤ P 0) (hPn : P n = Z)
    {g : ℝ → ℝ} (hgmono : Monotone g) (hgnn : ∀ u : ℝ, w ≤ u → 0 ≤ g u) :
    ∑ i ∈ Finset.range n,
        (Real.log Z / Real.log (P i) - Real.log Z / Real.log (P (i + 1))) * g (P i)
      ≤ ∫ u in w..Z, g u * (Real.log Z / (u * (Real.log u) ^ 2)) := by
  have hPw : ∀ i : ℕ, w ≤ P i := fun i => le_trans hwP0 (hPmono (Nat.zero_le i))
  have hPZ : ∀ i : ℕ, i ≤ n → P i ≤ Z := fun i hi => by rw [← hPn]; exact hPmono hi
  -- the density `u ↦ log Z / (u (log u)²)` is continuous on `[w, Z]` (as `w ≥ 2`) ...
  have hfun_cont : ContinuousOn (fun u : ℝ => Real.log Z / (u * (Real.log u)^2))
      (Set.Icc w Z) := by
    intro x hx
    have hx1 : 1 < x := by linarith [hx.1, hw]
    have hx0 : x ≠ 0 := by linarith
    have hl : ContinuousAt Real.log x := Real.continuousAt_log hx0
    have hden : ContinuousAt (fun u : ℝ => u * (Real.log u)^2) x :=
      continuousAt_id.mul (hl.pow 2)
    exact (continuousAt_const.div hden
      (mul_ne_zero hx0 (pow_ne_zero 2 (ne_of_gt (Real.log_pos hx1))))).continuousWithinAt
  -- ... hence on every subinterval `[a, b] ⊆ [w, Z]`.
  have hcont_of : ∀ a b : ℝ, w ≤ a → a ≤ b → b ≤ Z →
      ContinuousOn (fun u : ℝ => Real.log Z / (u * (Real.log u)^2)) (Set.uIcc a b) := by
    intro a b ha hab hb
    rw [Set.uIcc_of_le hab]
    exact hfun_cont.mono (Set.Icc_subset_Icc ha hb)
  -- the term-by-term comparison
  have key : ∀ i : ℕ, i < n →
      (Real.log Z / Real.log (P i) - Real.log Z / Real.log (P (i + 1))) * g (P i)
        ≤ ∫ u in P i..P (i+1), g u * (Real.log Z / (u * (Real.log u)^2)) := by
    intro i hi
    have hab : P i ≤ P (i+1) := hPmono (Nat.le_succ i)
    have hci := hcont_of (P i) (P (i+1)) (hPw i) hab (hPZ (i+1) (Nat.succ_le_of_lt hi))
    have hint : IntervalIntegrable (fun u : ℝ => Real.log Z / (u * (Real.log u)^2))
        MeasureTheory.volume (P i) (P (i+1)) := hci.intervalIntegrable
    have hf : IntervalIntegrable (fun u : ℝ => g u * (Real.log Z / (u * (Real.log u)^2)))
        MeasureTheory.volume (P i) (P (i+1)) := hgmono.intervalIntegrable.mul_continuousOn hci
    have hc : IntervalIntegrable (fun u : ℝ => g (P i) * (Real.log Z / (u * (Real.log u)^2)))
        MeasureTheory.volume (P i) (P (i+1)) := hint.const_mul (g (P i))
    have hstep : ∫ u in P i..P (i+1), g (P i) * (Real.log Z / (u * (Real.log u)^2))
        ≤ ∫ u in P i..P (i+1), g u * (Real.log Z / (u * (Real.log u)^2)) := by
      refine intervalIntegral.integral_mono_on hab hc hf (fun u hu => ?_)
      have hu2 : w ≤ u := le_trans (hPw i) hu.1
      have hhu : 0 ≤ Real.log Z / (u * (Real.log u)^2) := by
        have hZ : 0 < Real.log Z := Real.log_pos (by linarith [hw, hwZ])
        have hu1' : 1 < u := by linarith [hw, hu2]
        have hden : 0 ≤ u * (Real.log u)^2 := by
          have hlu : 0 < Real.log u := Real.log_pos hu1'
          positivity
        exact div_nonneg (le_of_lt hZ) hden
      exact mul_le_mul_of_nonneg_right (hgmono hu.1) hhu
    -- the constant multiple and the fundamental theorem of calculus
    have hconst : ∫ u in P i..P (i+1), g (P i) * (Real.log Z / (u * (Real.log u)^2))
        = g (P i) * ∫ u in P i..P (i+1), (Real.log Z / (u * (Real.log u)^2)) :=
      intervalIntegral.integral_const_mul _ _
    have hftc : ∫ u in P i..P (i+1), (Real.log Z / (u * (Real.log u)^2))
        = Real.log Z / Real.log (P i) - Real.log Z / Real.log (P (i+1)) := by
      have hderiv : ∀ x ∈ Set.uIcc (P i) (P (i+1)),
          HasDerivAt (fun u : ℝ => (-Real.log Z) / Real.log u)
          (Real.log Z / (x * (Real.log x)^2)) x := by
        intro x hx
        rw [Set.uIcc_of_le hab] at hx
        have hx0 : x ≠ 0 := by linarith [hx.1, hPw i, hw]
        have hxl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith [hx.1, hPw i, hw]))
        have hd := (hasDerivAt_const (x := x) (-Real.log Z)).div (Real.hasDerivAt_log hx0) hxl
        have hval : (0 * Real.log x - -Real.log Z * x⁻¹) / Real.log x ^ 2
            = Real.log Z / (x * (Real.log x)^2) := by
          field_simp
          ring
        rw [hval] at hd
        exact hd
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hci.intervalIntegrable]
      ring
    calc (Real.log Z / Real.log (P i) - Real.log Z / Real.log (P (i + 1))) * g (P i)
        = g (P i) * (Real.log Z / Real.log (P i) - Real.log Z / Real.log (P (i + 1))) := by
          ring
      _ = g (P i) * ∫ u in P i..P (i+1), (Real.log Z / (u * (Real.log u)^2)) := by rw [hftc]
      _ = ∫ u in P i..P (i+1), g (P i) * (Real.log Z / (u * (Real.log u)^2)) := hconst.symm
      _ ≤ ∫ u in P i..P (i+1), g u * (Real.log Z / (u * (Real.log u)^2)) := hstep
  have hsum := Finset.sum_le_sum (fun i hi => key i (Finset.mem_range.mp hi))
  -- telescoping over the consecutive intervals
  have hP0n : P 0 ≤ P n := hPmono (Nat.zero_le n)
  have hint0n : IntervalIntegrable (fun u : ℝ => g u * (Real.log Z / (u * (Real.log u)^2)))
      MeasureTheory.volume (P 0) (P n) :=
    hgmono.intervalIntegrable.mul_continuousOn
      (hcont_of (P 0) (P n) (hPw 0) hP0n (by rw [hPn]))
  have htel := integral_range_sum hPmono n hint0n
  -- `∫_w^Z ≥ ∫_{P 0}^Z`
  have hcont_wP0 : ContinuousOn (fun u : ℝ => Real.log Z / (u * (Real.log u)^2))
      (Set.uIcc w (P 0)) :=
    hcont_of w (P 0) le_rfl hwP0 (by rw [← hPn]; exact hP0n)
  have hcont_P0Z : ContinuousOn (fun u : ℝ => Real.log Z / (u * (Real.log u)^2))
      (Set.uIcc (P 0) Z) :=
    hcont_of (P 0) Z (hPw 0) (by rw [← hPn]; exact hP0n) le_rfl
  have hA : IntervalIntegrable (fun u : ℝ => g u * (Real.log Z / (u * (Real.log u)^2)))
      MeasureTheory.volume w (P 0) := hgmono.intervalIntegrable.mul_continuousOn hcont_wP0
  have hB : IntervalIntegrable (fun u : ℝ => g u * (Real.log Z / (u * (Real.log u)^2)))
      MeasureTheory.volume (P 0) Z := hgmono.intervalIntegrable.mul_continuousOn hcont_P0Z
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hA hB
  have hnn_wP0 : 0 ≤ ∫ u in w..P 0, g u * (Real.log Z / (u * (Real.log u)^2)) := by
    refine intervalIntegral.integral_nonneg hwP0 (fun u hu => ?_)
    refine mul_nonneg (hgnn u hu.1) ?_
    have hu1 : 1 < u := by linarith [hu.1, hw]
    have hZ : 0 < Real.log Z := Real.log_pos (by linarith [hw, hwZ])
    have hden : 0 ≤ u * (Real.log u)^2 := by
      have hlu : 0 < Real.log u := Real.log_pos hu1
      positivity
    exact div_nonneg (le_of_lt hZ) hden
  calc ∑ i ∈ Finset.range n,
        (Real.log Z / Real.log (P i) - Real.log Z / Real.log (P (i + 1))) * g (P i)
      ≤ ∑ i ∈ Finset.range n,
          ∫ u in P i..P (i+1), g u * (Real.log Z / (u * (Real.log u)^2)) := hsum
    _ = ∫ u in P 0..P n, g u * (Real.log Z / (u * (Real.log u)^2)) := htel
    _ = ∫ u in P 0..Z, g u * (Real.log Z / (u * (Real.log u)^2)) := by rw [hPn]
    _ ≤ ∫ u in w..Z, g u * (Real.log Z / (u * (Real.log u)^2)) := by linarith [hsplit, hnn_wP0]

theorem integral_step_bound {n : ℕ} {P : ℕ → ℝ} (hPmono : Monotone P)
    {w Z : ℝ} (hw : 2 ≤ w) (hwZ : w ≤ Z) (hwP0 : w ≤ P 0) (hPn : P n = Z)
    {Φ : ℝ → ℝ} (hΦmono : ∀ a b : ℝ, w ≤ a → a ≤ b → b ≤ Z → Φ a ≤ Φ b)
    (hΦnn : ∀ a : ℝ, w ≤ a → a ≤ Z → 0 ≤ Φ a) :
    ∑ i ∈ Finset.range n,
        (Real.log Z / Real.log (P i) - Real.log Z / Real.log (P (i + 1))) * Φ (P i)
      ≤ ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2)) := by
  have hPw : ∀ i : ℕ, w ≤ P i := fun i => le_trans hwP0 (hPmono (Nat.zero_le i))
  have hPZ : ∀ i : ℕ, i ≤ n → P i ≤ Z := fun i hi => by rw [← hPn]; exact hPmono hi
  -- clamp `Φ` to `[w, Z]`, where it is monotone, to make it globally monotone
  have hclamp_le : ∀ u : ℝ, max w (min u Z) ≤ Z := fun u => max_le hwZ (min_le_right _ _)
  have hclamp_ge : ∀ u : ℝ, w ≤ max w (min u Z) := fun u => le_max_left _ _
  have hGmono : Monotone (fun u : ℝ => Φ (max w (min u Z))) := by
    intro a b hab
    exact hΦmono _ _ (hclamp_ge a) (max_le_max le_rfl (min_le_min hab le_rfl)) (hclamp_le b)
  have hGnn : ∀ u : ℝ, w ≤ u → 0 ≤ Φ (max w (min u Z)) :=
    fun u _ => hΦnn _ (hclamp_ge u) (hclamp_le u)
  have hGeq : ∀ u : ℝ, w ≤ u → u ≤ Z → Φ (max w (min u Z)) = Φ u := by
    intro u h1 h2
    rw [min_eq_left h2, max_eq_right h1]
  have hmain := step_bound_of_monotone hPmono hw hwZ hwP0 hPn hGmono hGnn
  have h1 : ∑ i ∈ Finset.range n,
        (Real.log Z / Real.log (P i) - Real.log Z / Real.log (P (i + 1))) * Φ (P i)
      = ∑ i ∈ Finset.range n,
        (Real.log Z / Real.log (P i) - Real.log Z / Real.log (P (i + 1)))
          * Φ (max w (min (P i) Z)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hGeq (P i) (hPw i) (hPZ i (le_of_lt (Finset.mem_range.mp hi)))]
  have h2 : (∫ u in w..Z, Φ (max w (min u Z)) * (Real.log Z / (u * (Real.log u)^2)))
      = ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u)^2)) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le hwZ] at hu
    rw [hGeq u hu.1 hu.2]
  rw [h1, ← h2]
  exact hmain

end Work.ChenPlan.LinearSieve.Abel
