import Mathlib
import Submission.Work.ZeroDensity.Montgomery.gallagherPointwise
import Submission.Work.ZeroDensity.Montgomery.sumIntervalIntegralLe
import Submission.Work.ZeroDensity.Montgomery.integralMulLeSqrtMulSqrt

namespace Work.ZeroDensity.Montgomery

open scoped Classical BigOperators
open MeasureTheory

/-- **Gallagher's sampling bound (separated points versus the integral mean square).**  Let `g : ℝ → ℂ`
be differentiable everywhere with derivative `g'`, let `g'` be continuous, let `h > 0`, let `A ≤ B`,
and let `S : Finset ℝ` be a set of points whose `h`-neighbourhoods `[s-h, s+h]` lie in `[A,B]` and are
pairwise disjoint (`2h ≤ |s - s'|` for `s ≠ s'` in `S`).  Then
`∑_{s∈S} ‖g s‖² ≤ (1/(2h)) ∫_A^B ‖g‖² + 2 (∫_A^B ‖g‖²)^{1/2} (∫_A^B ‖g'‖²)^{1/2}`.
Proof sketch: on each interval `[s-h,s+h]` one has `‖g s‖² ≤ (1/(2h))∫ ‖g‖² + 2 ∫ ‖g‖ ‖g'‖` (average
the identity `‖g s‖² = ‖g x‖² + (‖g s‖² - ‖g x‖²)` over `x ∈ [s-h,s+h]` and bound the difference by
`2 ∫ ‖g‖ ‖g'‖` using the Newton--Leibniz formula); the intervals are disjoint and lie in `[A,B]`, so
the first terms sum to at most `(1/(2h)) ∫_A^B ‖g‖²`, and Cauchy--Schwarz bounds the second.
(`Continuous g'` is needed so that `‖g'‖²` is interval integrable, Mathlib's integral being
junk-zero on non-integrable functions.) -/
theorem gallagherSeparated {g g' : ℝ → ℂ} (hderiv : ∀ x, HasDerivAt g (g' x) x)
    (hcont : Continuous g')
    {h A B : ℝ} (hh : 0 < h) (hAB : A ≤ B)
    {S : Finset ℝ} (hsub : ∀ s ∈ S, A ≤ s - h ∧ s + h ≤ B)
    (hsep : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → 2 * h ≤ |s - s'|) :
    ∑ s ∈ S, ‖g s‖ ^ 2
      ≤ (1 / (2 * h)) * (∫ x in A..B, ‖g x‖ ^ 2)
        + 2 * Real.sqrt (∫ x in A..B, ‖g x‖ ^ 2) * Real.sqrt (∫ x in A..B, ‖g' x‖ ^ 2) := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hderiv x).continuousAt
  have hnn : (0 : ℝ) ≤ 1 / (2 * h) := by
    have h2h : (0 : ℝ) < 2 * h := by linarith
    exact div_nonneg (by norm_num) h2h.le
  -- Averaging step: the local (per point of `S`) Gallagher inequality.
  have hlocal : ∀ s ∈ S, ‖g s‖ ^ 2 ≤
      (1 / (2 * h)) * (∫ x in (s - h)..(s + h), ‖g x‖ ^ 2)
        + 2 * ∫ x in (s - h)..(s + h), ‖g x‖ * ‖g' x‖ := by
    intro s hs
    have hle : s - h ≤ s + h := by linarith
    set C : ℝ := ∫ x in (s - h)..(s + h), ‖g x‖ * ‖g' x‖ with hC
    have hpt : ∀ x ∈ Set.Icc (s - h) (s + h), ‖g s‖ ^ 2 ≤ ‖g x‖ ^ 2 + 2 * C := by
      intro x hx
      have h := gallagherPointwise hderiv hcont hh hx
      rw [hC]; exact h
    have hcont2 : Continuous fun x : ℝ => ‖g x‖ ^ 2 + 2 * C :=
      (((hgc.norm).pow 2).add continuous_const)
    have hmono : (∫ x in (s - h)..(s + h), ‖g s‖ ^ 2)
        ≤ ∫ x in (s - h)..(s + h), (‖g x‖ ^ 2 + 2 * C) :=
      intervalIntegral.integral_mono_on hle
        (Continuous.intervalIntegrable continuous_const _ _)
        (Continuous.intervalIntegrable hcont2 _ _) hpt
    have e1 : ∫ x in (s - h)..(s + h), ‖g s‖ ^ 2 = (2 * h) * ‖g s‖ ^ 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have e2 : ∫ x in (s - h)..(s + h), (‖g x‖ ^ 2 + 2 * C)
        = (∫ x in (s - h)..(s + h), ‖g x‖ ^ 2) + (2 * h) * (2 * C) := by
      have hadd := intervalIntegral.integral_add (μ := volume) (a := s - h) (b := s + h)
          (f := fun x : ℝ => ‖g x‖ ^ 2) (g := fun _ : ℝ => 2 * C)
          (Continuous.intervalIntegrable ((hgc.norm).pow 2) _ _)
          (Continuous.intervalIntegrable continuous_const _ _)
      rw [hadd, intervalIntegral.integral_const, smul_eq_mul]; ring
    have h2h' : (2 * h) * ‖g s‖ ^ 2
        ≤ (∫ x in (s - h)..(s + h), ‖g x‖ ^ 2) + (2 * h) * (2 * C) :=
      calc (2 * h) * ‖g s‖ ^ 2 = ∫ x in (s - h)..(s + h), ‖g s‖ ^ 2 := e1.symm
        _ ≤ ∫ x in (s - h)..(s + h), (‖g x‖ ^ 2 + 2 * C) := hmono
        _ = (∫ x in (s - h)..(s + h), ‖g x‖ ^ 2) + (2 * h) * (2 * C) := e2
    have hmul := mul_le_mul_of_nonneg_left h2h' hnn
    have e3 : (1 / (2 * h)) * ((2 * h) * ‖g s‖ ^ 2) = ‖g s‖ ^ 2 := by field_simp
    have e4 : (1 / (2 * h)) * ((∫ x in (s - h)..(s + h), ‖g x‖ ^ 2) + (2 * h) * (2 * C))
        = (1 / (2 * h)) * (∫ x in (s - h)..(s + h), ‖g x‖ ^ 2) + 2 * C := by field_simp
    rw [e3, e4] at hmul
    rw [hC] at hmul
    exact hmul
  -- Summing the local inequalities.
  have hsum : ∑ s ∈ S, ‖g s‖ ^ 2 ≤
      (1 / (2 * h)) * (∑ s ∈ S, ∫ x in (s - h)..(s + h), ‖g x‖ ^ 2)
        + 2 * (∑ s ∈ S, ∫ x in (s - h)..(s + h), ‖g x‖ * ‖g' x‖) := by
    calc ∑ s ∈ S, ‖g s‖ ^ 2
      ≤ ∑ s ∈ S, ((1 / (2 * h)) * (∫ x in (s - h)..(s + h), ‖g x‖ ^ 2)
            + 2 * ∫ x in (s - h)..(s + h), ‖g x‖ * ‖g' x‖) := Finset.sum_le_sum hlocal
      _ = (1 / (2 * h)) * (∑ s ∈ S, ∫ x in (s - h)..(s + h), ‖g x‖ ^ 2)
            + 2 * (∑ s ∈ S, ∫ x in (s - h)..(s + h), ‖g x‖ * ‖g' x‖) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- Disjointness: the neighbourhood integrals are dominated by the full integral.
  have hQ1 : (∑ s ∈ S, ∫ x in (s - h)..(s + h), ‖g x‖ ^ 2) ≤ ∫ x in A..B, ‖g x‖ ^ 2 :=
    sumIntervalIntegralLe hh hAB ((hgc.norm).pow 2) (fun x => sq_nonneg _) hsub hsep
  have hQ2 : (∑ s ∈ S, ∫ x in (s - h)..(s + h), ‖g x‖ * ‖g' x‖)
      ≤ ∫ x in A..B, ‖g x‖ * ‖g' x‖ :=
    sumIntervalIntegralLe hh hAB (hgc.norm.mul hcont.norm)
      (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsub hsep
  -- Cauchy--Schwarz on `[A,B]`.
  have hJ : (∫ x in A..B, ‖g x‖ * ‖g' x‖) ≤
      Real.sqrt (∫ x in A..B, ‖g x‖ ^ 2) * Real.sqrt (∫ x in A..B, ‖g' x‖ ^ 2) :=
    integralMulLeSqrtMulSqrt hgc.norm hcont.norm (fun x => norm_nonneg _)
      (fun x => norm_nonneg _) hAB
  have h1 : (1 / (2 * h)) * (∑ s ∈ S, ∫ x in (s - h)..(s + h), ‖g x‖ ^ 2)
      + 2 * (∑ s ∈ S, ∫ x in (s - h)..(s + h), ‖g x‖ * ‖g' x‖)
      ≤ (1 / (2 * h)) * (∫ x in A..B, ‖g x‖ ^ 2) + 2 * (∫ x in A..B, ‖g x‖ * ‖g' x‖) :=
    add_le_add (mul_le_mul_of_nonneg_left hQ1 hnn) (mul_le_mul_of_nonneg_left hQ2 (by norm_num))
  have h2 : (1 / (2 * h)) * (∫ x in A..B, ‖g x‖ ^ 2) + 2 * (∫ x in A..B, ‖g x‖ * ‖g' x‖)
      ≤ (1 / (2 * h)) * (∫ x in A..B, ‖g x‖ ^ 2)
        + 2 * (Real.sqrt (∫ x in A..B, ‖g x‖ ^ 2) * Real.sqrt (∫ x in A..B, ‖g' x‖ ^ 2)) :=
    add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hJ (by norm_num))
  calc ∑ s ∈ S, ‖g s‖ ^ 2
      ≤ (1 / (2 * h)) * (∫ x in A..B, ‖g x‖ ^ 2) + 2 * (∫ x in A..B, ‖g x‖ * ‖g' x‖) :=
        hsum.trans h1
    _ ≤ (1 / (2 * h)) * (∫ x in A..B, ‖g x‖ ^ 2)
        + 2 * (Real.sqrt (∫ x in A..B, ‖g x‖ ^ 2) * Real.sqrt (∫ x in A..B, ‖g' x‖ ^ 2)) := h2
    _ = (1 / (2 * h)) * (∫ x in A..B, ‖g x‖ ^ 2)
        + 2 * Real.sqrt (∫ x in A..B, ‖g x‖ ^ 2) * Real.sqrt (∫ x in A..B, ‖g' x‖ ^ 2) := by ring

end Work.ZeroDensity.Montgomery
