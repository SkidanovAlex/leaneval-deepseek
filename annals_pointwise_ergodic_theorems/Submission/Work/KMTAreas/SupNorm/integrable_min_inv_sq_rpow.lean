import Mathlib

/-!
# Integrability of `x ↦ (min A (B / x²))^q` for `q > 1/2`

For nonnegative `A`, `B` and `q > 1/2`, the function

`x ↦ (min A (B / x ^ 2)) ^ q`

is Lebesgue integrable on `ℝ`.

The function is bounded by `A ^ q` near the origin and decays like `B ^ q |x| ^ (-2q)`
at infinity, and `2q > 1`.  The proof follows the standard "locally integrable and
`O` at `+∞` with the symmetry `‖f (-x)‖ = ‖f x‖`" route
(`MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant`):

* local integrability is immediate because `min A (B / x²) ≤ A`, so that
  `‖f x‖ ≤ A ^ q = A ^ q * ‖x‖ ^ 0` — the bound required by
  `MeasureTheory.locallyIntegrable_of_norm_le_rpow` with exponent `α = 0`;
* at `+∞` one has `f =O[atTop] (fun x ↦ x ^ (-2q))` since
  `(B / x ^ 2) ^ q = B ^ q * x ^ (-2q)` for `x > 0`, and `x ^ (-2q)` is integrable at
  `atTop` because `-2q < -1`;
* the symmetry is the evenness of `x ↦ x ^ 2`.
-/

namespace Work.KMTAreas.SupNorm

open MeasureTheory Filter Asymptotics

theorem integrable_min_inv_sq_rpow {A B q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 1 / 2 < q) :
    MeasureTheory.Integrable (fun x : ℝ => (min A (B / x ^ 2)) ^ q) MeasureTheory.volume := by
  have hq0 : 0 ≤ q := by linarith
  let f : ℝ → ℝ := fun x => (min A (B / x ^ 2)) ^ q
  have hfnnonneg : ∀ x, 0 ≤ f x := fun x =>
    Real.rpow_nonneg (le_min hA (div_nonneg hB (sq_nonneg x))) q
  -- Measurability: `min` of a constant and a quotient of measurable functions, then `rpow`.
  have hmeas : Measurable f := by
    change Measurable fun x : ℝ => (min A (B / x ^ 2)) ^ q
    exact (Real.continuous_rpow_const hq0).measurable.comp
      (Measurable.min measurable_const (measurable_const.div (measurable_id.pow_const 2)))
  -- Local integrability, from the global bound `f ≤ A ^ q` (exponent `α = 0`).
  have hdecay : ∀ᵐ x ∂(volume : Measure ℝ), ‖f x‖ ≤ A ^ q * ‖x‖ ^ (-(0 : ℝ)) := by
    filter_upwards with x
    simp only [neg_zero, Real.rpow_zero, mul_one]
    rw [Real.norm_of_nonneg (hfnnonneg x)]
    change (min A (B / x ^ 2)) ^ q ≤ A ^ q
    exact Real.rpow_le_rpow (le_min hA (div_nonneg hB (sq_nonneg x))) (min_le_left _ _) hq0
  have hloc : LocallyIntegrable f volume :=
    locallyIntegrable_of_norm_le_rpow (E := ℝ) (F := ℝ) (f := f) (C := A ^ q) (α := 0)
      (by norm_num) (by norm_num) hdecay hmeas.aestronglyMeasurable
  -- Evenness, used for the symmetry hypothesis at `-∞`.
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    simp only [f, neg_sq]
  -- Decay at `+∞`: `f =O[atTop] (fun x ↦ x ^ (-2q))`.
  have ho : f =O[atTop] (fun x : ℝ => x ^ (-(2 * q))) := by
    refine IsBigO.of_bound (B ^ q) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have h1 : f x ≤ (B / x ^ 2) ^ q := by
      change (min A (B / x ^ 2)) ^ q ≤ (B / x ^ 2) ^ q
      exact Real.rpow_le_rpow (le_min hA (div_nonneg hB (sq_nonneg x))) (min_le_right _ _) hq0
    have h2 : (B / x ^ 2) ^ q = B ^ q * x ^ (-(2 * q)) := by
      rw [Real.div_rpow hB (sq_nonneg x) q,
        show x ^ 2 = x ^ (2 : ℝ) by rw [Real.rpow_two, pow_two],
        ← Real.rpow_mul hx0.le 2 q, Real.rpow_neg hx0.le (2 * q), div_eq_mul_inv]
    rw [Real.norm_of_nonneg (hfnnonneg x), Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    rw [h2] at h1
    exact h1
  -- `x ^ (-2q)` is integrable at `+∞` because `-2q < -1`.
  have hg : IntegrableAtFilter (fun x : ℝ => x ^ (-(2 * q))) atTop volume :=
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) one_pos⟩
  have hsymm : norm ∘ f =ᵐ[(volume : Measure ℝ)] norm ∘ f ∘ Neg.neg := by
    refine Eventually.of_forall fun x => ?_
    simp only [Function.comp_apply]
    rw [heven x]
  exact hloc.integrable_of_isBigO_atTop_of_norm_isNegInvariant hsymm ho hg

end Work.KMTAreas.SupNorm
