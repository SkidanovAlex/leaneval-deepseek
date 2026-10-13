import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux

/-- Pointwise total-variation bound: if `U` has derivative `U'` at every point of `[a,b]` and `U'`
is interval integrable on `[a,b]`, then for every `x ∈ [a,b]` the difference `U θ - U x` is
dominated, in absolute value, by the total variation `∫ y in a..b, |U' y|`.

This is the fundamental-theorem-of-calculus step behind `tvAverageLe`: restrict the FTC to the
subinterval between `x` and `θ` and use monotonicity of the integral of the nonnegative function
`|U'|`. -/
lemma abs_sub_le_intervalIntegral_abs_deriv {a b θ : ℝ} (haθ : a ≤ θ)
    (hθb : θ ≤ b) {U U' : ℝ → ℝ} (hU : ∀ x ∈ Set.Icc a b, HasDerivAt U (U' x) x)
    (hInt : IntervalIntegrable U' MeasureTheory.volume a b) :
    ∀ x ∈ Set.Icc a b, |U θ - U x| ≤ ∫ y in a..b, |U' y| := by
  intro x hx
  rcases le_total x θ with hxθ | hθx
  · have hsubI : Set.uIcc x θ ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le hxθ]
      exact Set.Icc_subset_Icc hx.1 hθb
    have hsub : Set.uIcc x θ ⊆ Set.uIcc a b := hsubI.trans Set.Icc_subset_uIcc
    have hFTC : ∫ y in x..θ, U' y = U θ - U x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y hy => hU y (hsubI hy)) (hInt.mono_set hsub)
    calc |U θ - U x| = |∫ y in x..θ, U' y| := by rw [hFTC]
      _ ≤ ∫ y in x..θ, |U' y| := intervalIntegral.abs_integral_le_integral_abs hxθ
      _ ≤ ∫ y in a..b, |U' y| :=
          intervalIntegral.integral_mono_interval hx.1 hxθ hθb
            (ae_of_all _ (fun y => abs_nonneg (U' y))) hInt.abs
  · have hsubI : Set.uIcc θ x ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le hθx]
      exact Set.Icc_subset_Icc haθ hx.2
    have hsub : Set.uIcc θ x ⊆ Set.uIcc a b := hsubI.trans Set.Icc_subset_uIcc
    have hFTC : ∫ y in θ..x, U' y = U x - U θ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y hy => hU y (hsubI hy)) (hInt.mono_set hsub)
    calc |U θ - U x| = |∫ y in θ..x, U' y| := by rw [hFTC, abs_sub_comm]
      _ ≤ ∫ y in θ..x, |U' y| := intervalIntegral.abs_integral_le_integral_abs hθx
      _ ≤ ∫ y in a..b, |U' y| :=
          intervalIntegral.integral_mono_interval haθ hθx hx.2
            (ae_of_all _ (fun y => abs_nonneg (U' y))) hInt.abs

/-- The value of a function at a point is bounded by its mean value over `[a,b]` plus its total
variation on `[a,b]`: if `U` has derivative `U'` at each point of `[a,b]` with `U'` interval
integrable, and `U` is interval integrable, then for `θ ∈ [a,b]`
`U θ ≤ (1/(b-a)) ∫_a^b U + ∫_a^b |U'|`.

Proof: by `abs_sub_le_intervalIntegral_abs_deriv`, `U θ - U x ≤ ∫_a^b |U'|` for every `x ∈ [a,b]`;
integrating this inequality over `[a,b]` gives `(b-a) U θ - ∫_a^b U ≤ (b-a) ∫_a^b |U'|`, and
division by `b - a > 0` yields the claim. -/
theorem tvAverageLe {a b θ : ℝ} (hab : a < b) (haθ : a ≤ θ) (hθb : θ ≤ b)
    {U U' : ℝ → ℝ} (hU : ∀ x ∈ Set.Icc a b, HasDerivAt U (U' x) x)
    (hInt : IntervalIntegrable U' MeasureTheory.volume a b)
    (hIntU : IntervalIntegrable U MeasureTheory.volume a b) :
    U θ ≤ (1 / (b - a)) * (∫ x in a..b, U x) + ∫ x in a..b, |U' x| := by
  have hab_le : a ≤ b := hab.le
  have hbda : (0 : ℝ) < b - a := sub_pos.mpr hab
  -- pointwise bound
  have hpt : ∀ x ∈ Set.Icc a b, U θ - U x ≤ ∫ y in a..b, |U' y| := fun x hx =>
    (le_abs_self (U θ - U x)).trans
      (abs_sub_le_intervalIntegral_abs_deriv haθ hθb hU hInt x hx)
  -- integrate the pointwise bound
  have hnonneg : 0 ≤ ∫ x in a..b, (U x + ((∫ y in a..b, |U' y|) - U θ)) :=
    intervalIntegral.integral_nonneg hab_le (fun u hu => by linarith [hpt u hu])
  have hval : ∫ x in a..b, (U x + ((∫ y in a..b, |U' y|) - U θ))
      = (∫ x in a..b, U x) + (b - a) * ((∫ y in a..b, |U' y|) - U θ) := by
    rw [intervalIntegral.integral_add hIntU intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  have hmain : (b - a) * U θ ≤ (∫ x in a..b, U x) + (b - a) * (∫ x in a..b, |U' x|) := by
    have h2 : 0 ≤ (∫ x in a..b, U x) + (b - a) * ((∫ x in a..b, |U' x|) - U θ) := by
      rw [← hval]; exact hnonneg
    nlinarith [h2]
  -- divide by the positive number `b - a`
  have hc : (0 : ℝ) ≤ 1 / (b - a) := by positivity
  have h1 : (1 / (b - a)) * ((b - a) * U θ) = U θ := by
    rw [← mul_assoc, one_div_mul_cancel (ne_of_gt hbda), one_mul]
  have h2 : (1 / (b - a)) * ((∫ x in a..b, U x) + (b - a) * (∫ x in a..b, |U' x|))
      = (1 / (b - a)) * (∫ x in a..b, U x) + ∫ x in a..b, |U' x| := by
    rw [mul_add, ← mul_assoc, one_div_mul_cancel (ne_of_gt hbda), one_mul]
  calc U θ = (1 / (b - a)) * ((b - a) * U θ) := h1.symm
    _ ≤ (1 / (b - a)) * ((∫ x in a..b, U x) + (b - a) * (∫ x in a..b, |U' x|)) :=
        mul_le_mul_of_nonneg_left hmain hc
    _ = (1 / (b - a)) * (∫ x in a..b, U x) + ∫ x in a..b, |U' x| := h2

end Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux
