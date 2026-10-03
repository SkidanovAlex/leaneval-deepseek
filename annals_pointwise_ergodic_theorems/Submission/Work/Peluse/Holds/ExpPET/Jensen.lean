import Mathlib

/-!
# The Jensen (power-mean) brick of `ExpansionPETShort`

`Work.Peluse.Holds.ExpansionPETShort`'s hypothesis bounds the average over `a ∈ [1,M₂]` of the
level-`s` box *norm* of `f`, while every later step of the proof works with the box-norm *power*
(`boxNorm s = (boxNormPow s)^{1/2^s}`).  The passage is the power-mean inequality: for `1 ≤ p` and
non-negative `y`,

  `(card s)⁻¹ ∑_{i ∈ s} (y i)^{1/p}  ^ p ≤ (card s)⁻¹ ∑_{i ∈ s} y i`,

i.e. the mean of the `1/p`-th powers, raised to the `p`-th power, is at most the mean.  It follows
from the convexity bound `(∑ x_i)^p ≤ (card)^{p-1} ∑ x_i^p` (Mathlib's
`Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg`) applied to `x_i = (y i)^{1/p}`, using
`((y)^{1/p})^p = y` for `y ≥ 0`.

Both forms are provided: the power-mean inequality itself, and the derived step
`δ ≤ mean (y^{1/p}) ⟹ δ^p ≤ mean y` which is the form the route consumes.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Holds.ExpPET

/-- **The power mean inequality** (the "Jensen" step of `ExpansionPETShort`).  For `1 ≤ p` and
non-negative `y`, the `p`-th power of the mean of the `1/p`-th powers of `y` is at most the mean of
`y`. -/
theorem pow_mean_avg_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) {p : ℝ} (hp : 1 ≤ p)
    (y : ι → ℝ) (hy : ∀ i ∈ s, 0 ≤ y i) :
    (((s.card : ℝ))⁻¹ * ∑ i ∈ s, (y i) ^ (1 / p)) ^ p
      ≤ ((s.card : ℝ))⁻¹ * ∑ i ∈ s, y i := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hne : p ≠ 0 := ne_of_gt hp0
  -- the convexity bound, applied to `i ↦ (y i)^{1/p}`
  have hstep := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := s)
    (f := fun i => (y i) ^ (1 / p)) hp (fun i hi => Real.rpow_nonneg (hy i hi) _)
  have hpow : ∀ i ∈ s, ((y i) ^ (1 / p)) ^ p = y i := by
    intro i hi
    rw [← Real.rpow_mul (hy i hi), one_div_mul_cancel hne, Real.rpow_one]
  rw [Finset.sum_congr rfl hpow] at hstep
  -- `(card)^(p-1) = (card)^p / card`, and `(card⁻¹)^p · (card^p / card) = card⁻¹`
  have hcoef : ((s.card : ℝ))⁻¹ ^ p * (((s.card : ℝ)) ^ (p - 1))
      = ((s.card : ℝ))⁻¹ := by
    rw [Real.inv_rpow hcard.le p, ← Real.rpow_neg hcard.le p, ← Real.rpow_add hcard (-p) (p - 1),
      show -p + (p - 1) = -1 by ring, Real.rpow_neg_one]
  calc (((s.card : ℝ))⁻¹ * ∑ i ∈ s, (y i) ^ (1 / p)) ^ p
      = ((s.card : ℝ))⁻¹ ^ p * (∑ i ∈ s, (y i) ^ (1 / p)) ^ p := by
        rw [Real.mul_rpow (by positivity)
          (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hy i hi) _)]
    _ ≤ ((s.card : ℝ))⁻¹ ^ p * (((s.card : ℝ)) ^ (p - 1) * ∑ i ∈ s, y i) := by
        refine mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg (by positivity) p)
    _ = ((s.card : ℝ))⁻¹ * ∑ i ∈ s, y i := by
        rw [← mul_assoc, hcoef]

/-- The form consumed by the route: from a bound on the mean of the `1/p`-th powers, one for the
mean of the powers. -/
theorem pow_le_avg_of_le_avg_rpow {ι : Type*} (s : Finset ι) (hs : s.Nonempty) {p δ : ℝ}
    (hp : 1 ≤ p) (hδ : 0 ≤ δ) (y : ι → ℝ) (hy : ∀ i ∈ s, 0 ≤ y i)
    (h : δ ≤ ((s.card : ℝ))⁻¹ * ∑ i ∈ s, (y i) ^ (1 / p)) :
    δ ^ p ≤ ((s.card : ℝ))⁻¹ * ∑ i ∈ s, y i := by
  have hmean : 0 ≤ ((s.card : ℝ))⁻¹ * ∑ i ∈ s, (y i) ^ (1 / p) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hy i hi) _)
  exact le_trans (Real.rpow_le_rpow hδ h (le_trans zero_le_one hp)) (pow_mean_avg_le s hs hp y hy)

end Work.Peluse.Holds.ExpPET
