import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/radGreen_sup_le`

The **sup-based sharp bound** for the radial Euler Green function `radGreen α m c`,
with *two* source bounds: one on the near field `(0,z]` and one on the far field `[z,∞)`.

## The computation

With

  `q := (2m+5)/α > 0`,   `p := 2m/α > 0`,   `K := 1/(α(4m+5))`,

the definition is

  `radGreen α m c z = K · ( z^{-q} · ∫_0^z c t · t^{q-1} dt + z^{p} · ∫_z^∞ c t · t^{-p-1} dt )`.

If `|c t| ≤ M₁` for `0 < t ≤ z` and `|c t| ≤ M₂` for `t ≥ z`, then using the two elementary
rpow integrals (`∫_0^z t^{q-1} = z^q/q` for `q > 0`, `∫_z^∞ t^{-p-1} = z^{-p}/p` for `p > 0`,
`z > 0`):

  `z^{-q} · |∫_0^z c t^{q-1}| ≤ z^{-q} · M₁ z^q/q = M₁/q = M₁ α/(2m+5)`,
  `z^{p} · |∫_z^∞ c t^{-p-1}| ≤ z^{p} · M₂ z^{-p}/p = M₂/p = M₂ α/(2m)`,

whence

  `|radGreen α m c z| ≤ K · (M₁ α/(2m+5) + M₂ α/(2m))`
    `= M₁/((4m+5)(2m+5)) + M₂/((4m+5)(2m))`,

which is exactly the claimed bound.  Nothing beyond the two pointwise bounds on `c` and
`z > 0` is used.  (In particular the statement is insensitive to the junk-integral
convention: if either integrand of the Green formula is not integrable, the corresponding
Bochner integral is `0`, and the estimate still holds.)

The two integral estimates are the private lemmas `near_int_bound_sup` and `far_int_bound_sup`;
they are the half-line-(`(0,z]` / `[z,∞)`) refinements of the global-bound lemmas
`near_int_bound` / `far_int_bound` of `FTS/ClassCHon/radGreen_size_bound.lean`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon

/-- **The near-field (`0 < t ≤ z`) integral estimate.**  For `z > 0`, `Q > 0` and a source
bounded by `M₁` on `(0,z]`,

  `|∫_0^z c t · t^{Q-1} dt| ≤ M₁ · z^Q / Q`.

This is the sharp bound: the dominating function `M₁ t^{Q-1}` is integrable on `(0,z)`
precisely because `Q - 1 > -1`, and its integral is `M₁ z^Q/Q`. -/
private theorem near_int_bound_sup {z M Q : ℝ} (hz : 0 < z) (hQ : 0 < Q) {c : ℝ → ℝ}
    (hc : ∀ t : ℝ, 0 < t → t ≤ z → |c t| ≤ M) :
    |∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1)| ≤ M * z ^ Q / Q := by
  have hQ1 : (-1 : ℝ) < Q - 1 := by linarith
  have hbnd : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      t ∈ Set.Ioc (0 : ℝ) z → ‖c t * t ^ (Q - 1)‖ ≤ M * t ^ (Q - 1) := by
    filter_upwards with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact mul_le_mul_of_nonneg_right (hc t ht.1 ht.2) (Real.rpow_nonneg ht.1.le _)
  have hint : IntervalIntegrable (fun t : ℝ => M * t ^ (Q - 1)) MeasureTheory.volume (0 : ℝ) z :=
    (intervalIntegral.intervalIntegrable_rpow' hQ1).const_mul M
  have h2 : ∫ t in (0 : ℝ)..z, M * t ^ (Q - 1) = M * z ^ Q / Q := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hQ1)]
    have h : Q - 1 + 1 = Q := by ring
    rw [h, Real.zero_rpow hQ.ne', sub_zero]
    ring
  have h1 := intervalIntegral.norm_integral_le_of_norm_le hz.le hbnd hint
  rw [h2] at h1
  rwa [Real.norm_eq_abs] at h1

/-- **The far-field (`t ≥ z`) integral estimate.**  For `z > 0`, `P > 0` and a source bounded
by `M₂` on `[z,∞)`,

  `|∫_z^∞ c t · t^{-P-1} dt| ≤ M₂ · z^{-P} / P`.

Here the dominating function `M₂ t^{-P-1}` is integrable on `(z,∞)` (for `z > 0`) precisely
because `-P - 1 < -1`, and its integral is `M₂ z^{-P}/P`. -/
private theorem far_int_bound_sup {z M P : ℝ} (hz : 0 < z) (hP : 0 < P) {c : ℝ → ℝ}
    (hc : ∀ t : ℝ, z ≤ t → |c t| ≤ M) :
    |∫ t in Set.Ioi z, c t * t ^ (-P - 1)| ≤ M * z ^ (-P) / P := by
  have hP1 : -P - 1 < (-1 : ℝ) := by linarith
  have hg : MeasureTheory.Integrable (fun t : ℝ => M * t ^ (-P - 1))
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    (integrableOn_Ioi_rpow_of_lt hP1 hz).const_mul M
  have hbnd : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi z)),
      ‖c t * t ^ (-P - 1)‖ ≤ M * t ^ (-P - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_mul_of_nonneg_right (hc t ht.le) (Real.rpow_nonneg ht0.le _)
  have h2 : ∫ t in Set.Ioi z, M * t ^ (-P - 1) = M * z ^ (-P) / P := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt hP1 hz]
    have h : -P - 1 + 1 = -P := by ring
    rw [h]
    field_simp
  have h1 := MeasureTheory.norm_integral_le_of_norm_le hg hbnd
  rw [h2] at h1
  rwa [Real.norm_eq_abs] at h1

/-- **The sup-based sharp bound for the mode-`m` radial Green function.**  If the source `c` is
bounded by `M₁` on `(0,z]` and by `M₂` on `[z,∞)` then

  `|radGreen α m c z| ≤ M₁/((4m+5)(2m+5)) + M₂/((4m+5)(2m))`. -/
theorem radGreen_sup_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) {c : ℝ → ℝ}
    {z M₁ M₂ : ℝ} (hz : 0 < z) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ t : ℝ, 0 < t → t ≤ z → |c t| ≤ M₁)
    (h₂ : ∀ t : ℝ, z ≤ t → |c t| ≤ M₂) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ M₁ / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5))
        + M₂ / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) := by
  -- the two exponents `Q = (2m+5)/α` (decaying branch) and `P = 2m/α` (growing branch)
  set Q : ℝ := (2 * (m : ℝ) + 5) / α with hQ
  set P : ℝ := 2 * (m : ℝ) / α with hP
  set L : ℝ := 1 / (α * (4 * (m : ℝ) + 5)) with hL
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hPpos : 0 < P := by rw [hP]; positivity
  have hLpos : 0 < L := by rw [hL]; positivity
  -- the two integral estimates
  have hI1 : |∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1)| ≤ M₁ * z ^ Q / Q :=
    near_int_bound_sup hz hQpos h₁
  have hI2 : |∫ t in Set.Ioi z, c t * t ^ (-P - 1)| ≤ M₂ * z ^ (-P) / P :=
    far_int_bound_sup hz hPpos h₂
  -- `radGreen` in terms of `Q`, `P`, `L`
  have hrad : Work.FTS.PhiStar.Radial.radGreen α m c z
      = L * (z ^ (-Q) * (∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1))
          + z ^ P * (∫ t in Set.Ioi z, c t * t ^ (-P - 1))) := by
    simp only [Work.FTS.PhiStar.Radial.radGreen, hQ, hP, hL]
    rw [neg_div]
  have hzQ : z ^ (-Q) * z ^ Q = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  have hzP : z ^ P * z ^ (-P) = 1 := by
    rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero]
  -- the absolute value of `radGreen`
  have hmain : |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ L * (M₁ / Q + M₂ / P) := by
    rw [hrad, abs_mul, abs_of_pos hLpos]
    calc L * |z ^ (-Q) * (∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1))
              + z ^ P * (∫ t in Set.Ioi z, c t * t ^ (-P - 1))|
        ≤ L * (z ^ (-Q) * |∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1)|
              + z ^ P * |∫ t in Set.Ioi z, c t * t ^ (-P - 1)|) := by
          apply mul_le_mul_of_nonneg_left _ hLpos.le
          calc |z ^ (-Q) * (∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1))
                + z ^ P * (∫ t in Set.Ioi z, c t * t ^ (-P - 1))|
              ≤ |z ^ (-Q) * (∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1))|
                + |z ^ P * (∫ t in Set.Ioi z, c t * t ^ (-P - 1))| := abs_add_le _ _
            _ = z ^ (-Q) * |∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1)|
                + z ^ P * |∫ t in Set.Ioi z, c t * t ^ (-P - 1)| := by
                rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz _),
                    abs_of_pos (Real.rpow_pos_of_pos hz _)]
      _ ≤ L * (z ^ (-Q) * (M₁ * z ^ Q / Q) + z ^ P * (M₂ * z ^ (-P) / P)) := by
          apply mul_le_mul_of_nonneg_left _ hLpos.le
          exact add_le_add
            (mul_le_mul_of_nonneg_left hI1 (le_of_lt (Real.rpow_pos_of_pos hz _)))
            (mul_le_mul_of_nonneg_left hI2 (le_of_lt (Real.rpow_pos_of_pos hz _)))
      _ = L * (M₁ / Q + M₂ / P) := by
          have hA : z ^ (-Q) * (M₁ * z ^ Q / Q) = M₁ / Q := by
            rw [← mul_div_assoc, mul_comm M₁ (z ^ Q), ← mul_assoc, hzQ, one_mul]
          have hB : z ^ P * (M₂ * z ^ (-P) / P) = M₂ / P := by
            rw [← mul_div_assoc, mul_comm M₂ (z ^ (-P)), ← mul_assoc, hzP, one_mul]
          rw [hA, hB]
  -- the pure arithmetic: `L·(M₁/Q + M₂/P)` is the claimed right-hand side
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hLQ : L * (1 / Q) = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5)) := by
    rw [hL, hQ]
    field_simp
  have hLP : L * (1 / P) = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) := by
    rw [hL, hP]
    field_simp
  have harith : L * (M₁ / Q + M₂ / P)
      = M₁ / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5))
        + M₂ / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) := by
    rw [show M₁ / Q = M₁ * (1 / Q) from by ring,
        show M₂ / P = M₂ * (1 / P) from by ring,
        mul_add,
        show L * (M₁ * (1 / Q)) = M₁ * (L * (1 / Q)) from by ring,
        show L * (M₂ * (1 / P)) = M₂ * (L * (1 / P)) from by ring,
        hLQ, hLP]
    ring
  calc |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ L * (M₁ / Q + M₂ / P) := hmain
    _ = M₁ / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5))
        + M₂ / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) := harith

end Work.FTS.ClassCHon
