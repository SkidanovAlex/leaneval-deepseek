import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory

namespace Work.MRMT.Found

/-- Given a continuous `g : ℝ → ℝ` and `0 < a < R`, there exists `r ∈ (a, R)` with
`r ^ 2 * g r * log (R / a) ≤ ∫ x in a..R, x * g x`.

Equivalently, the weighted average `(1 / log (R / a)) * ∫ x in a..R, x * g x` — which is
the mean of `x ↦ x ^ 2 * g x` against the probability measure `dx / (x log (R / a))` on
`(a, R)` — dominates `x ^ 2 * g x` at some interior point. -/
theorem exists_sq_mul_le_integral {g : ℝ → ℝ} (hg : Continuous g)
    {a R : ℝ} (ha : 0 < a) (haR : a < R) :
    ∃ r ∈ Set.Ioo a R,
      r ^ 2 * g r * Real.log (R / a) ≤ ∫ x in (a : ℝ)..R, x * g x := by
  have hRpos : 0 < R := lt_trans ha haR
  have hlogpos : 0 < Real.log (R / a) :=
    Real.log_pos (by rw [one_lt_div ha]; exact haR)
  by_contra hcon
  push Not at hcon
  -- `hcon`: for every interior `r`, `∫ x in a..R, x * g x < r ^ 2 * g r * log (R / a)`.
  -- Dividing by the positive `log (R / a)` gives a strict bound for every interior point.
  have key : ∀ x ∈ Set.Ioo a R,
      (∫ y in a..R, y * g y) / Real.log (R / a) < x ^ 2 * g x := by
    intro x hx
    rw [div_lt_iff₀ hlogpos]
    exact hcon x hx
  have hxm : IntervalIntegrable (fun x : ℝ => x * g x) volume a R :=
    (continuous_id.mul hg).intervalIntegrable a R
  have hKm_cont : ContinuousOn (fun x : ℝ => (∫ y in a..R, y * g y) / Real.log (R / a) / x)
      (Set.Icc a R) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hKm : IntervalIntegrable (fun x : ℝ => (∫ y in a..R, y * g y) / Real.log (R / a) / x)
      volume a R := hKm_cont.intervalIntegrable_of_Icc haR.le
  -- The continuous difference `x * g x - (∫ y in a..R, y * g y) / log (R / a) / x` is
  -- strictly positive on the interior, hence has strictly positive integral.
  have hpos : ∀ x ∈ Set.Ioo a R,
      0 < x * g x - (∫ y in a..R, y * g y) / Real.log (R / a) / x := by
    intro x hx
    have hxpos : 0 < x := lt_trans ha hx.1
    have h1 := key x hx
    have h2 : (∫ y in a..R, y * g y) / Real.log (R / a) / x < x * g x := by
      rw [div_lt_iff₀ hxpos]
      nlinarith [h1]
    exact sub_pos.mpr h2
  have hψint : IntervalIntegrable
      (fun x : ℝ => x * g x - (∫ y in a..R, y * g y) / Real.log (R / a) / x) volume a R :=
    hxm.sub hKm
  have hψpos : 0 < ∫ x in a..R,
      (x * g x - (∫ y in a..R, y * g y) / Real.log (R / a) / x) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hψint hpos haR
  rw [intervalIntegral.integral_sub hxm hKm] at hψpos
  -- Computing the second integral: `∫ x in a..R, K / x = K * log (R / a)` with
  -- `K = (∫ y in a..R, y * g y) / log (R / a)`, i.e. exactly the original integral.
  have hA : ∫ x in a..R, (∫ y in a..R, y * g y) / Real.log (R / a) / x
      = ∫ y in a..R, y * g y := by
    rw [show (fun x : ℝ => (∫ y in a..R, y * g y) / Real.log (R / a) / x)
        = (fun x : ℝ => ((∫ y in a..R, y * g y) / Real.log (R / a)) * x⁻¹) from by
          funext x; ring]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hRpos]
    exact div_mul_cancel₀ _ (ne_of_gt hlogpos)
  rw [hA, sub_self] at hψpos
  exact lt_irrefl 0 hψpos

end Work.MRMT.Found
