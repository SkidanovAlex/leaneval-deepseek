import Mathlib

/-!
# Auxiliary lemmas for `integral_one_div_add_abs_le`

We bound `∫ s in a..b, (C + |s - M|)⁻¹` by its value in the centred case.  Everything rests on
the primitive

  `G C x = ∫ t in 0..x, (C + |t|)⁻¹`

of `t ↦ (C + |t|)⁻¹`, which is `Real.log (1 + x / C)` for `x ≥ 0` and
`-Real.log (1 + (-x) / C)` for `x ≤ 0`, together with the elementary logarithmic inequality
`Real.log (1 + L / C) ≤ 2 * Real.log (1 + L / (2 * C))`.

The substitution `s ↦ s - M` turns the integral of the target into `G C (b - M) - G C (a - M)`,
and the case analysis on where `M` sits relative to `[a, b]` is done by the three lemmas
`G_left_le`, `G_center_le`, `G_right_le`.
-/

namespace Work.Pert.PinLogDev

/-- The primitive of `t ↦ (C + |t|)⁻¹`, normalised by `G C 0 = 0`. -/
noncomputable def G (C x : ℝ) : ℝ := ∫ t in 0..x, (C + |t|)⁻¹

/-- On the nonnegative half-line the integrand of `G` is `(C + t)⁻¹`. -/
lemma G_of_nonneg (C x : ℝ) (hC : 0 < C) (hx : 0 ≤ x) :
    G C x = Real.log (1 + x / C) := by
  unfold G
  have hcongr : (∫ t in 0..x, (C + |t|)⁻¹) = ∫ t in 0..x, (C + t)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht
    show (C + |t|)⁻¹ = (C + t)⁻¹
    rw [Set.uIcc, Set.mem_Icc] at ht
    have ht0 : 0 ≤ t := by
      have := ht.1
      rwa [inf_eq_left.2 hx] at this
    rw [abs_of_nonneg ht0]
  rw [hcongr]
  have h1 : (∫ t in 0..x, (C + t)⁻¹) = ∫ u in C..C + x, u⁻¹ := by simp
  rw [h1, integral_inv_of_pos (by linarith) (by linarith), add_div, div_self (ne_of_gt hC)]

/-- On the nonpositive half-line the integrand of `G` is `(C - t)⁻¹`. -/
lemma G_of_nonpos (C x : ℝ) (hC : 0 < C) (hx : x ≤ 0) :
    G C x = -Real.log (1 + (-x) / C) := by
  unfold G
  have hcongr : (∫ t in 0..x, (C + |t|)⁻¹) = ∫ t in 0..x, (C - t)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht
    show (C + |t|)⁻¹ = (C - t)⁻¹
    rw [Set.uIcc, Set.mem_Icc] at ht
    have ht0 : t ≤ 0 := by
      have := ht.2
      rwa [sup_eq_left.2 hx] at this
    rw [abs_of_nonpos ht0, sub_eq_add_neg]
  rw [hcongr]
  have h1 : (∫ t in 0..x, (C - t)⁻¹) = ∫ u in C - x..C, u⁻¹ := by simp
  rw [h1, integral_inv_of_pos (by linarith) (by linarith)]
  have h2 : C / (C - x) = ((C + -x) / C)⁻¹ := by rw [inv_div, sub_eq_add_neg]
  rw [h2, Real.log_inv]
  congr 1
  rw [add_div, div_self (ne_of_gt hC)]

/-- `Real.log (1 + L / C) ≤ 2 * Real.log (1 + L / (2 * C))` for `0 < C` and `0 ≤ L`. -/
lemma log_one_add_div_le (C L : ℝ) (hC : 0 < C) (hL : 0 ≤ L) :
    Real.log (1 + L / C) ≤ 2 * Real.log (1 + L / (2 * C)) := by
  have hsq : 1 + L / C ≤ (1 + L / (2 * C)) ^ 2 := by
    have h : (1 + L / (2 * C)) ^ 2 = 1 + L / C + (L / (2 * C)) ^ 2 := by ring
    rw [h]
    have := sq_nonneg (L / (2 * C))
    linarith
  calc Real.log (1 + L / C) ≤ Real.log ((1 + L / (2 * C)) ^ 2) :=
        Real.log_le_log (by positivity) hsq
    _ = 2 * Real.log (1 + L / (2 * C)) := by rw [Real.log_pow]; norm_num

end Work.Pert.PinLogDev
