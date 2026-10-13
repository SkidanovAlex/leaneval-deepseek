import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.PhiStar.Honesty.sq_integral_sqrt_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sq_tail_le`: the weighted Cauchy–Schwarz bound on the far tail

For `s < -1`, `z ≥ 1` and `c` with `(c t)²` integrable on `(1,∞)`,

  `(∫_z^∞ c t · t^s)² ≤ (∫_z^∞ (c t)²) · z^{2s+1}/(-(2s+1))`.

This is the Cauchy–Schwarz (Bunyakovsky) inequality applied to the two `L²(Ioi z)`
functions `t ↦ c t` and `t ↦ t^s`, together with the elementary evaluation
`∫_z^∞ t^{2s} dt = z^{2s+1}/(-(2s+1))` of the weight (legitimate because `2s < -2`), i.e. the
`L²`-norm of the weight `t^s` on the tail.  It is the estimate that bounds the decaying radial
Green integral `∫_z^∞ c t · t^{-(2m/α) - 1}` of `Work.FTS.PhiStar.Radial.radGreen` by the
`L²`-mass `∫_z^∞ c²`.

The formalisation goes through the "square roots" form of Cauchy–Schwarz
(`Work.PhiStar.Honesty.sq_integral_sqrt_mul_le`, which is stated for two nonnegative integrable
functions `A`, `B`), with `A t = (c t)²` and `B t = t^{2s}`: on `(z,∞)` one has `t > 0`, so
`√((c t)²) · √(t^{2s}) = |c t| · t^s`.  This avoids ever having to *prove* that `c · t^s` is
integrable: all that is used is `|∫ f| ≤ ∫ |f|`, which is unconditional.
-/

noncomputable section

open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty.CSTools

/-- **Weighted Cauchy–Schwarz on the far tail.**  If `s < -1`, `z ≥ 1` and `c² ∈ L¹(1,∞)`, then
`(∫_z^∞ c t · t^s)² ≤ (∫_z^∞ c²) · z^{2s+1}/(-(2s+1))`.

The constant is the `L²`-norm squared of the weight `t^s` on `(z,∞)`, namely
`∫_z^∞ t^{2s} = z^{2s+1}/(-(2s+1))`, which is finite precisely because `2s < -2 < -1`. -/
theorem sq_tail_le {c : ℝ → ℝ} {s : ℝ} (hs : s < -1) {z : ℝ} (hz : 1 ≤ z)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    (∫ t in Set.Ioi z, c t * t ^ s) ^ 2
      ≤ (∫ t in Set.Ioi z, (c t) ^ 2) * (z ^ (2 * s + 1) / (-(2 * s + 1))) := by
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have h2s : 2 * s < -1 := by linarith
  -- The two `L²(Ioi z)` factors: `(c t)²` and the weight `t^{2s}`.
  have hA : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi z) :=
    hfar.mono_set (Set.Ioi_subset_Ioi hz)
  have hB : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (2 * s)) (Set.Ioi z) :=
    integrableOn_Ioi_rpow_of_lt h2s hz0
  have hAnn : ∀ t ∈ Set.Ioi z, 0 ≤ (c t) ^ 2 := fun t _ => sq_nonneg _
  have hBnn : ∀ t ∈ Set.Ioi z, 0 ≤ t ^ (2 * s) := fun t ht =>
    Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hz0 (le_of_lt ht))) _
  -- Cauchy–Schwarz in the "square roots" form.
  have hcs :=
    Work.PhiStar.Honesty.sq_integral_sqrt_mul_le measurableSet_Ioi hA hB hAnn hBnn
  -- On `(z,∞)` we have `t > 0`, so `√((c t)²) · √(t^{2s}) = |c t| · t^s`.
  have hpoint : ∀ t ∈ Set.Ioi z,
      Real.sqrt ((c t) ^ 2) * Real.sqrt (t ^ (2 * s)) = |c t| * t ^ s := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hz0 (le_of_lt ht)
    have hsq : Real.sqrt (t ^ (2 * s)) = t ^ s := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]
      congr 1
      ring
    rw [Real.sqrt_sq_eq_abs, hsq]
  have hL : (∫ t in Set.Ioi z, Real.sqrt ((c t) ^ 2) * Real.sqrt (t ^ (2 * s)))
      = ∫ t in Set.Ioi z, |c t| * t ^ s :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpoint
  -- The weight integral.
  have hval : (∫ t in Set.Ioi z, t ^ (2 * s)) = z ^ (2 * s + 1) / (-(2 * s + 1)) := by
    rw [integral_Ioi_rpow_of_lt h2s hz0, div_neg, neg_div]
  rw [hL, hval] at hcs
  -- `|∫ c t · t^s| ≤ ∫ |c t| · t^s`, unconditionally.
  have habs : |∫ t in Set.Ioi z, c t * t ^ s| ≤ ∫ t in Set.Ioi z, |c t| * t ^ s := by
    have h1 := MeasureTheory.abs_integral_le_integral_abs
      (μ := MeasureTheory.volume.restrict (Set.Ioi z)) (f := fun t : ℝ => c t * t ^ s)
    have h2 : (∫ t in Set.Ioi z, |c t * t ^ s|) = ∫ t in Set.Ioi z, |c t| * t ^ s :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
        rw [abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hz0 (le_of_lt ht))) s)])
    rw [h2] at h1
    exact h1
  have hsq : (∫ t in Set.Ioi z, c t * t ^ s) ^ 2
      ≤ (∫ t in Set.Ioi z, |c t| * t ^ s) ^ 2 := by
    rw [← sq_abs (∫ t in Set.Ioi z, c t * t ^ s)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  exact le_trans hsq hcs

end Work.FTS.PhiStar.Honesty.CSTools
