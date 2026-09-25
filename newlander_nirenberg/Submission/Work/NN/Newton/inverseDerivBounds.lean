import Mathlib

namespace Work.NN.Newton

/-- If `a * b = 1` and `a` is within `1/2` of the identity in a normed ring, then `‖b‖ ≤ 2`.

The argument avoids the inverse: writing `1 - a =: s`, we get `b = 1 + s * b` from
`(1 - s) * b = 1`, hence `‖b‖ ≤ ‖1‖ + ‖s‖ * ‖b‖ ≤ 1 + (1/2) * ‖b‖` and therefore `‖b‖ ≤ 2`. -/
private lemma norm_le_two_of_mul_eq_one {R : Type*} [NormedRing R]
    (h1 : ‖(1 : R)‖ ≤ 1) {a b : R} (ha : ‖a - 1‖ ≤ (1 / 2 : ℝ))
    (hab : a * b = 1) : ‖b‖ ≤ 2 := by
  have hkey : b = 1 + (1 - a) * b := by
    have h : b - (1 - a) * b = 1 := by
      rw [sub_mul, one_mul, hab]
      abel
    rwa [sub_eq_iff_eq_add] at h
  have hle1 : ‖1 - a‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_sub_rev]; exact ha
  have hmain : ‖b‖ ≤ 1 + (1 / 2 : ℝ) * ‖b‖ := by
    calc ‖b‖ = ‖1 + (1 - a) * b‖ := by conv_lhs => rw [hkey]
      _ ≤ ‖(1 : R)‖ + ‖(1 - a) * b‖ := norm_add_le _ _
      _ ≤ 1 + ‖1 - a‖ * ‖b‖ := add_le_add h1 (norm_mul_le _ _)
      _ ≤ 1 + (1 / 2 : ℝ) * ‖b‖ :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hle1 (norm_nonneg _))
  linarith

/-- If `‖a - 1‖ ≤ 1/2` then left multiplication by `a` is injective: `a * x = 0` forces `x = 0`.

Indeed `a = 1 - (1 - a)`, so `a * x = 0` gives `x = (1 - a) * x`, whence
`‖x‖ ≤ ‖1 - a‖ * ‖x‖ ≤ (1/2) * ‖x‖` and `x = 0`. -/
private lemma eq_zero_of_mul_eq_zero_of_norm_sub_one {R : Type*} [NormedRing R]
    {a : R} (ha : ‖a - 1‖ ≤ (1 / 2 : ℝ)) :
    ∀ x : R, a * x = 0 → x = 0 := by
  intro x hx
  have hxa : x = (1 - a) * x := by
    have h : (1 - (1 - a)) * x = 0 := by rw [sub_sub_self]; exact hx
    rw [sub_mul, one_mul, sub_eq_zero] at h
    exact h
  have hle1 : ‖1 - a‖ ≤ (1 / 2 : ℝ) := by rw [norm_sub_rev]; exact ha
  have hmain : ‖x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := by
    calc ‖x‖ = ‖(1 - a) * x‖ := by conv_lhs => rw [hxa]
      _ ≤ ‖1 - a‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ (1 / 2 : ℝ) * ‖x‖ := mul_le_mul_of_nonneg_right hle1 (norm_nonneg _)
  have : ‖x‖ ≤ 0 := by linarith
  exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))

/-- If `a * b = 1` and `‖a - 1‖ ≤ 1/2` then `b` is also a left inverse of `a`, i.e. `b * a = 1`.
This uses injectivity of left multiplication by `a` applied to `a * (b * a - 1) = 0`. -/
private lemma mul_comm_eq_one_of_mul_eq_one {R : Type*} [NormedRing R]
    {a b : R} (ha : ‖a - 1‖ ≤ (1 / 2 : ℝ))
    (hab : a * b = 1) : b * a = 1 := by
  have hinj := eq_zero_of_mul_eq_zero_of_norm_sub_one ha
  have h0 : a * (b * a - 1) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc a b a, hab, one_mul, sub_self]
  exact sub_eq_zero.mp (hinj (b * a - 1) h0)

/-- The difference of two right inverses, written as a conjugation by the left inverse: if
`a' * b' = 1` and `b * a = 1` then `b - b' = b * (a' - a) * b'`. -/
private lemma sub_eq_mul_sub_mul {R : Type*} [Ring R] {a a' b b' : R}
    (ha'b' : a' * b' = 1) (hba : b * a = 1) :
    b - b' = b * (a' - a) * b' := by
  have h : b * (a' - a) * b' = b - b' := by
    rw [mul_sub, sub_mul, mul_assoc b a' b', ha'b', mul_one, hba, one_mul]
  exact h.symm

theorem inverseDerivBounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F Ψ : E → E} {s t : Set E} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hchain : ∀ y ∈ t, (fderiv ℝ F (Ψ y)).comp (fderiv ℝ Ψ y) = ContinuousLinearMap.id ℝ E)
    (hb : ∀ x ∈ s, ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 2 : ℝ))
    (hh : ∀ x ∈ s, ∀ x' ∈ s, ‖fderiv ℝ F x - fderiv ℝ F x'‖ ≤ (1 / 16 : ℝ) * ‖x - x'‖ ^ α)
    (hmem : ∀ y ∈ t, Ψ y ∈ s)
    (hlip : ∀ y ∈ t, ∀ y' ∈ t, ‖Ψ y - Ψ y'‖ ≤ 2 * ‖y - y'‖) :
    (∀ y ∈ t, ‖fderiv ℝ Ψ y‖ ≤ 2) ∧
    (∀ y ∈ t, ∀ y' ∈ t, ‖fderiv ℝ Ψ y - fderiv ℝ Ψ y'‖ ≤ (1 / 2 : ℝ) * ‖y - y'‖ ^ α) := by
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  constructor
  · intro y hy
    have ha : ‖fderiv ℝ F (Ψ y) - 1‖ ≤ (1 / 2 : ℝ) := hb (Ψ y) (hmem y hy)
    have hab : fderiv ℝ F (Ψ y) * fderiv ℝ Ψ y = 1 := hchain y hy
    exact norm_le_two_of_mul_eq_one h1 ha hab
  · intro y hy y' hy'
    set a := fderiv ℝ F (Ψ y) with ha_def
    set a' := fderiv ℝ F (Ψ y') with ha'_def
    set b := fderiv ℝ Ψ y with hb_def
    set b' := fderiv ℝ Ψ y' with hb'_def
    have hA1 : ‖a - 1‖ ≤ (1 / 2 : ℝ) := by
      rw [ha_def]; exact hb (Ψ y) (hmem y hy)
    have hA2 : ‖a' - 1‖ ≤ (1 / 2 : ℝ) := by
      rw [ha'_def]; exact hb (Ψ y') (hmem y' hy')
    have hab1 : a * b = 1 := by
      rw [ha_def, hb_def]; exact hchain y hy
    have hab2 : a' * b' = 1 := by
      rw [ha'_def, hb'_def]; exact hchain y' hy'
    have hba1 : b * a = 1 := mul_comm_eq_one_of_mul_eq_one hA1 hab1
    have hnormb : ‖b‖ ≤ 2 := norm_le_two_of_mul_eq_one h1 hA1 hab1
    have hnormb' : ‖b'‖ ≤ 2 := norm_le_two_of_mul_eq_one h1 hA2 hab2
    have hAbound : ‖a' - a‖ ≤ (1 / 16 : ℝ) * ‖Ψ y - Ψ y'‖ ^ α := by
      rw [norm_sub_rev]
      have hthis := hh (Ψ y) (hmem y hy) (Ψ y') (hmem y' hy')
      rw [← ha_def, ← ha'_def] at hthis
      exact hthis
    have hΨ : ‖Ψ y - Ψ y'‖ ^ α ≤ 2 * ‖y - y'‖ ^ α := by
      have hle : ‖Ψ y - Ψ y'‖ ^ α ≤ (2 * ‖y - y'‖) ^ α :=
        Real.rpow_le_rpow (norm_nonneg _) (hlip y hy y' hy') (le_of_lt hα0)
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)] at hle
      have h2 : (2 : ℝ) ^ α ≤ 2 := by
        have hh2 := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hα1
        rwa [Real.rpow_one] at hh2
      calc ‖Ψ y - Ψ y'‖ ^ α ≤ 2 ^ α * ‖y - y'‖ ^ α := hle
        _ ≤ 2 * ‖y - y'‖ ^ α :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) _)
    have hdiff : b * (a' - a) * b' = b - b' :=
      (sub_eq_mul_sub_mul hab2 hba1).symm
    rw [← hdiff]
    calc ‖b * (a' - a) * b'‖
        ≤ (‖b‖ * ‖a' - a‖) * ‖b'‖ := by
          calc ‖b * (a' - a) * b'‖ ≤ ‖b * (a' - a)‖ * ‖b'‖ := norm_mul_le _ _
            _ ≤ (‖b‖ * ‖a' - a‖) * ‖b'‖ :=
                mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (2 * ((1 / 16 : ℝ) * ‖Ψ y - Ψ y'‖ ^ α)) * 2 := by
          have h1' : ‖b‖ * ‖a' - a‖ ≤ 2 * ((1 / 16 : ℝ) * ‖Ψ y - Ψ y'‖ ^ α) := by
            have h2' : ‖b‖ * ‖a' - a‖ ≤ 2 * ‖a' - a‖ :=
              mul_le_mul_of_nonneg_right hnormb (norm_nonneg _)
            have h3' : 2 * ‖a' - a‖ ≤ 2 * ((1 / 16 : ℝ) * ‖Ψ y - Ψ y'‖ ^ α) :=
              mul_le_mul_of_nonneg_left hAbound (by norm_num)
            linarith
          have h4' : (2 * ((1 / 16 : ℝ) * ‖Ψ y - Ψ y'‖ ^ α)) * ‖b'‖
              ≤ (2 * ((1 / 16 : ℝ) * ‖Ψ y - Ψ y'‖ ^ α)) * 2 :=
            mul_le_mul_of_nonneg_left hnormb' (by positivity)
          exact le_trans (mul_le_mul_of_nonneg_right h1' (norm_nonneg _)) h4'
      _ = (1 / 4 : ℝ) * ‖Ψ y - Ψ y'‖ ^ α := by ring
      _ ≤ (1 / 4 : ℝ) * (2 * ‖y - y'‖ ^ α) :=
          mul_le_mul_of_nonneg_left hΨ (by norm_num)
      _ = (1 / 2 : ℝ) * ‖y - y'‖ ^ α := by ring

end Work.NN.Newton
