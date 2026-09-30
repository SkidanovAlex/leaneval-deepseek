import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Integrating a block sum of shifted copies of a function

If `G : ℝ → ℝ` is nonnegative, measurable and bounded above by `C`, and the shifts
`(j : ℝ) * H'` for `j ∈ Finset.range m` all satisfy `(j : ℝ) * H' ≤ X`, then the integral over
`[X, 2X]` of the block sum `Σ_{j < m} G (x + j H')` is at most `m * ∫_X^{3X} G`.

This is the elementary estimate used when integrating the block decomposition
`‖g‖_{u^{k+1}[x,x+H]} ≤ (H'/H) Σ_j ‖g‖_{u^{k+1}[x+jH', x+jH'+H']} + (m + H' + 2)/H`
over `x ∈ [X, 2X]`: the shifted interval `[X + jH', 2X + jH']` is contained in `[X, 3X]`
because `jH' ≤ X`, and `G ≥ 0` lets us compare the integrals.
-/

namespace Work.BMF

open MeasureTheory intervalIntegral

/-- A measurable real function bounded (in norm) by a constant is interval integrable. -/
lemma intervalIntegrable_of_measurable_bound {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b :=
  IntegrableOn.intervalIntegrable (IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
    hf.aestronglyMeasurable.restrict C (Filter.Eventually.of_forall hC))

/-- **Block-sum integration.** For `G ≥ 0` measurable and bounded, and shifts `jH' ≤ X`
for all `j < m`, the integral of the block sum over `[X, 2X]` is at most `m` times the
integral of `G` over `[X, 3X]`. -/
theorem block_sum_integral_le (G : ℝ → ℝ) (X H' : ℝ) (m : ℕ) (C : ℝ)
    (hX : 0 < X) (hH' : 0 < H') (hGmeas : Measurable G)
    (hGnn : ∀ x : ℝ, 0 ≤ G x) (hGbdd : ∀ x : ℝ, G x ≤ C)
    (hjX : ∀ j ∈ Finset.range m, (j : ℝ) * H' ≤ X) :
    (∫ x in X..(2 * X), ∑ j ∈ Finset.range m, G (x + (j : ℝ) * H'))
      ≤ (m : ℝ) * ∫ y in X..(3 * X), G y := by
  have hGnorm : ∀ x, ‖G x‖ ≤ C := fun x => by
    rw [Real.norm_of_nonneg (hGnn x)]; exact hGbdd x
  have hG3int : IntervalIntegrable G volume X (3 * X) :=
    intervalIntegrable_of_measurable_bound hGmeas hGnorm X (3 * X)
  have hshift_int : ∀ j : ℕ,
      IntervalIntegrable (fun x : ℝ => G (x + (j : ℝ) * H')) volume X (2 * X) :=
    fun j => intervalIntegrable_of_measurable_bound
      (hGmeas.comp (measurable_id.add measurable_const))
      (fun x => hGnorm (x + (j : ℝ) * H')) X (2 * X)
  rw [intervalIntegral.integral_finsetSum (fun j _ => hshift_int j)]
  have hterm : ∀ j ∈ Finset.range m,
      ∫ x in X..(2 * X), G (x + (j : ℝ) * H') ≤ ∫ y in X..(3 * X), G y := by
    intro j hj
    have hjX' : (j : ℝ) * H' ≤ X := hjX j hj
    rw [intervalIntegral.integral_comp_add_right G ((j : ℝ) * H')]
    refine intervalIntegral.integral_mono_interval ?_ ?_ ?_ ?_ ?_
    · have : 0 ≤ (j : ℝ) * H' := mul_nonneg (Nat.cast_nonneg j) (le_of_lt hH')
      linarith
    · linarith
    · linarith
    · exact Filter.Eventually.of_forall (fun y => hGnn y)
    · exact hG3int
  calc ∑ j ∈ Finset.range m, ∫ x in X..(2 * X), G (x + (j : ℝ) * H')
      ≤ ∑ j ∈ Finset.range m, ∫ y in X..(3 * X), G y := Finset.sum_le_sum hterm
    _ = (m : ℝ) * ∫ y in X..(3 * X), G y := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Work.BMF
