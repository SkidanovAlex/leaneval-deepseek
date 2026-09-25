import Mathlib

namespace Work.NN.Newton.ThinProfile

/-- **Lipschitz bound for a radial vector field.**  Let `F : ℝ → ℝ` satisfy
`|F s| ≤ M0 * c`, `|F s| ≤ M1 * c ^ 2 * |b ^ 2 - s|` (the "flatness" bound at the boundary) and
`|F s - F s'| ≤ M1 * c ^ 2 * |s - s'|`, and let `F s = 0` for `s ≥ b ^ 2`.  Then the radial field
`ζ ↦ F (‖ζ‖²) · ζ` is Lipschitz with constant `M0 * c + 2 b² M1 c²`.

Proof route (case analysis on whether `‖ζ‖² ≤ b²`): write
`(F x) ζ - (F y) ζ' = F x · (ζ - ζ') + (F x - F y) · ζ'` with `x = normSq ζ`, `y = normSq ζ'`.
* both `‖ζ‖, ‖ζ'‖ ≤ b`: `h0` bounds the first term, and for the second
  `|x - y| = |‖ζ‖-‖ζ'‖| (‖ζ‖+‖ζ'‖) ≤ 2b ‖ζ - ζ'‖` together with `h2` and `‖ζ'‖ ≤ b`.
* both `≥ b`: `hz` makes both terms vanish.
* `‖ζ'‖ ≥ b > ‖ζ‖`: `hz` kills `F y`, and `h1` gives
  `|F x| ≤ M1c²(b-‖ζ‖)(b+‖ζ‖) ≤ 2b²M1c²(b-‖ζ‖) ≤ 2b²M1c²‖ζ-ζ'‖` (use
  `b - ‖ζ‖ ≤ ‖ζ-ζ'‖`, from `abs_norm_sub_norm_le`). -/
lemma lipschitz_radial_field {F : ℝ → ℝ} {b M0 M1 c : ℝ} (hb : 0 < b) (hM0 : 0 ≤ M0)
    (hM1 : 0 ≤ M1) (hc : 0 ≤ c)
    (h0 : ∀ s : ℝ, |F s| ≤ M0 * c)
    (h1 : ∀ s : ℝ, |F s| ≤ M1 * c ^ 2 * |b ^ 2 - s|)
    (h2 : ∀ s s' : ℝ, |F s - F s'| ≤ M1 * c ^ 2 * |s - s'|)
    (hz : ∀ s : ℝ, b ^ 2 ≤ s → F s = 0) :
    ∀ ζ ζ' : ℂ, ‖(F (Complex.normSq ζ) : ℂ) * ζ - (F (Complex.normSq ζ') : ℂ) * ζ'‖
      ≤ (M0 * c + 2 * b ^ 2 * M1 * c ^ 2) * ‖ζ - ζ'‖ := by
  intro ζ ζ'
  by_cases hζ : ‖ζ‖ ≤ b
  · by_cases hζ' : ‖ζ'‖ ≤ b
    · -- Case 1: both points inside the radius `b`.
      have hxny : |Complex.normSq ζ - Complex.normSq ζ'| ≤ 2 * b * ‖ζ - ζ'‖ := by
        rw [Complex.normSq_eq_norm_sq ζ, Complex.normSq_eq_norm_sq ζ', sq_sub_sq, abs_mul,
          abs_of_nonneg (by positivity)]
        have h1' : |‖ζ‖ - ‖ζ'‖| ≤ ‖ζ - ζ'‖ := abs_norm_sub_norm_le ζ ζ'
        have h2' : ‖ζ‖ + ‖ζ'‖ ≤ 2 * b := by linarith
        calc (‖ζ‖ + ‖ζ'‖) * |‖ζ‖ - ‖ζ'‖| = |‖ζ‖ - ‖ζ'‖| * (‖ζ‖ + ‖ζ'‖) := by ring
          _ ≤ ‖ζ - ζ'‖ * (2 * b) := mul_le_mul h1' h2' (by positivity) (by positivity)
          _ = 2 * b * ‖ζ - ζ'‖ := by ring
      have hid : (F (Complex.normSq ζ) : ℂ) * ζ - (F (Complex.normSq ζ') : ℂ) * ζ'
          = (F (Complex.normSq ζ) : ℂ) * (ζ - ζ')
            + ((F (Complex.normSq ζ) : ℂ) - (F (Complex.normSq ζ') : ℂ)) * ζ' := by ring
      rw [hid]
      have hterm1 : |F (Complex.normSq ζ)| * ‖ζ - ζ'‖ ≤ (M0 * c) * ‖ζ - ζ'‖ :=
        mul_le_mul_of_nonneg_right (h0 _) (norm_nonneg _)
      have hterm2 : |F (Complex.normSq ζ) - F (Complex.normSq ζ')| * ‖ζ'‖
          ≤ (2 * b ^ 2 * M1 * c ^ 2) * ‖ζ - ζ'‖ := by
        have h2'' : |F (Complex.normSq ζ) - F (Complex.normSq ζ')|
            ≤ M1 * c ^ 2 * (2 * b * ‖ζ - ζ'‖) := by
          have hh := h2 (Complex.normSq ζ) (Complex.normSq ζ')
          nlinarith [hxny, mul_nonneg hM1 (sq_nonneg c)]
        calc |F (Complex.normSq ζ) - F (Complex.normSq ζ')| * ‖ζ'‖
            ≤ (M1 * c ^ 2 * (2 * b * ‖ζ - ζ'‖)) * b :=
              mul_le_mul h2'' hζ' (norm_nonneg _) (by positivity)
          _ = (2 * b ^ 2 * M1 * c ^ 2) * ‖ζ - ζ'‖ := by ring
      calc ‖(F (Complex.normSq ζ) : ℂ) * (ζ - ζ')
            + ((F (Complex.normSq ζ) : ℂ) - (F (Complex.normSq ζ') : ℂ)) * ζ'‖
          ≤ ‖(F (Complex.normSq ζ) : ℂ) * (ζ - ζ')‖
            + ‖((F (Complex.normSq ζ) : ℂ) - (F (Complex.normSq ζ') : ℂ)) * ζ'‖ := norm_add_le _ _
        _ = |F (Complex.normSq ζ)| * ‖ζ - ζ'‖
            + |F (Complex.normSq ζ) - F (Complex.normSq ζ')| * ‖ζ'‖ := by
              rw [norm_mul, norm_mul,
                show (F (Complex.normSq ζ) : ℂ) - (F (Complex.normSq ζ') : ℂ)
                  = ((F (Complex.normSq ζ) - F (Complex.normSq ζ') : ℝ) : ℂ) by
                    rw [Complex.ofReal_sub]]
              simp only [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (M0 * c) * ‖ζ - ζ'‖ + (2 * b ^ 2 * M1 * c ^ 2) * ‖ζ - ζ'‖ :=
              add_le_add hterm1 hterm2
        _ = (M0 * c + 2 * b ^ 2 * M1 * c ^ 2) * ‖ζ - ζ'‖ := by ring
    · -- Case 2: `‖ζ‖ ≤ b < ‖ζ'‖`.
      have hb2 : b < ‖ζ'‖ := not_le.mp hζ'
      have hw : b ^ 2 ≤ Complex.normSq ζ' := by
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ hb.le hb2.le 2
      have hFw : F (Complex.normSq ζ') = 0 := hz _ hw
      have hFz : |F (Complex.normSq ζ)| ≤ M1 * c ^ 2 * (b ^ 2 - Complex.normSq ζ) := by
        have hle : Complex.normSq ζ ≤ b ^ 2 := by
          rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg ζ) hζ 2
        have key : |b ^ 2 - Complex.normSq ζ| = b ^ 2 - Complex.normSq ζ :=
          abs_of_nonneg (by linarith)
        simpa [key] using h1 (Complex.normSq ζ)
      have hd : b - ‖ζ‖ ≤ ‖ζ - ζ'‖ := by
        have h' : |‖ζ‖ - ‖ζ'‖| ≤ ‖ζ - ζ'‖ := abs_norm_sub_norm_le ζ ζ'
        have h'' : |‖ζ‖ - ‖ζ'‖| = ‖ζ'‖ - ‖ζ‖ := by
          rw [abs_of_nonpos (by linarith)]
          ring
        linarith
      rw [hFw, Complex.ofReal_zero, zero_mul, sub_zero]
      calc ‖(F (Complex.normSq ζ) : ℂ) * ζ‖
          = |F (Complex.normSq ζ)| * ‖ζ‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (M1 * c ^ 2 * (b ^ 2 - Complex.normSq ζ)) * ‖ζ‖ :=
              mul_le_mul_of_nonneg_right hFz (norm_nonneg _)
        _ = M1 * c ^ 2 * (b ^ 2 - ‖ζ‖ ^ 2) * ‖ζ‖ := by rw [Complex.normSq_eq_norm_sq]
        _ ≤ 2 * b ^ 2 * M1 * c ^ 2 * ‖ζ - ζ'‖ := by
              have hN : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg _
              have hkey : (b ^ 2 - ‖ζ‖ ^ 2) * ‖ζ‖ ≤ 2 * b ^ 2 * (b - ‖ζ‖) := by
                nlinarith [sq_nonneg (b - ‖ζ‖), hN, hb.le]
              calc M1 * c ^ 2 * (b ^ 2 - ‖ζ‖ ^ 2) * ‖ζ‖
                  = M1 * c ^ 2 * ((b ^ 2 - ‖ζ‖ ^ 2) * ‖ζ‖) := by ring
                _ ≤ M1 * c ^ 2 * (2 * b ^ 2 * (b - ‖ζ‖)) :=
                      mul_le_mul_of_nonneg_left hkey (mul_nonneg hM1 (sq_nonneg c))
                _ ≤ M1 * c ^ 2 * (2 * b ^ 2 * ‖ζ - ζ'‖) :=
                      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (by positivity))
                        (mul_nonneg hM1 (sq_nonneg c))
                _ = 2 * b ^ 2 * M1 * c ^ 2 * ‖ζ - ζ'‖ := by ring
        _ ≤ (M0 * c + 2 * b ^ 2 * M1 * c ^ 2) * ‖ζ - ζ'‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              nlinarith [mul_nonneg hM0 hc]
  · by_cases hζ' : ‖ζ'‖ ≤ b
    · -- Case 3: `b < ‖ζ‖` and `‖ζ'‖ ≤ b`.
      have hb1 : b < ‖ζ‖ := not_le.mp hζ
      have hx : b ^ 2 ≤ Complex.normSq ζ := by
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ hb.le hb1.le 2
      have hFx : F (Complex.normSq ζ) = 0 := hz _ hx
      have hFy : |F (Complex.normSq ζ')| ≤ M1 * c ^ 2 * (b ^ 2 - Complex.normSq ζ') := by
        have hle : Complex.normSq ζ' ≤ b ^ 2 := by
          rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg ζ') hζ' 2
        have key : |b ^ 2 - Complex.normSq ζ'| = b ^ 2 - Complex.normSq ζ' :=
          abs_of_nonneg (by linarith)
        simpa [key] using h1 (Complex.normSq ζ')
      have hd : b - ‖ζ'‖ ≤ ‖ζ - ζ'‖ := by
        have h' : |‖ζ‖ - ‖ζ'‖| ≤ ‖ζ - ζ'‖ := abs_norm_sub_norm_le ζ ζ'
        have h'' : |‖ζ‖ - ‖ζ'‖| = ‖ζ‖ - ‖ζ'‖ := by
          rw [abs_of_nonneg (by linarith)]
        linarith
      rw [hFx, Complex.ofReal_zero, zero_mul, zero_sub, norm_neg]
      calc ‖(F (Complex.normSq ζ') : ℂ) * ζ'‖
          = |F (Complex.normSq ζ')| * ‖ζ'‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (M1 * c ^ 2 * (b ^ 2 - Complex.normSq ζ')) * ‖ζ'‖ :=
              mul_le_mul_of_nonneg_right hFy (norm_nonneg _)
        _ = M1 * c ^ 2 * (b ^ 2 - ‖ζ'‖ ^ 2) * ‖ζ'‖ := by rw [Complex.normSq_eq_norm_sq]
        _ ≤ 2 * b ^ 2 * M1 * c ^ 2 * ‖ζ - ζ'‖ := by
              have hN : (0:ℝ) ≤ ‖ζ'‖ := norm_nonneg _
              have hkey : (b ^ 2 - ‖ζ'‖ ^ 2) * ‖ζ'‖ ≤ 2 * b ^ 2 * (b - ‖ζ'‖) := by
                nlinarith [sq_nonneg (b - ‖ζ'‖), hN, hb.le]
              calc M1 * c ^ 2 * (b ^ 2 - ‖ζ'‖ ^ 2) * ‖ζ'‖
                  = M1 * c ^ 2 * ((b ^ 2 - ‖ζ'‖ ^ 2) * ‖ζ'‖) := by ring
                _ ≤ M1 * c ^ 2 * (2 * b ^ 2 * (b - ‖ζ'‖)) :=
                      mul_le_mul_of_nonneg_left hkey (mul_nonneg hM1 (sq_nonneg c))
                _ ≤ M1 * c ^ 2 * (2 * b ^ 2 * ‖ζ - ζ'‖) :=
                      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (by positivity))
                        (mul_nonneg hM1 (sq_nonneg c))
                _ = 2 * b ^ 2 * M1 * c ^ 2 * ‖ζ - ζ'‖ := by ring
        _ ≤ (M0 * c + 2 * b ^ 2 * M1 * c ^ 2) * ‖ζ - ζ'‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              nlinarith [mul_nonneg hM0 hc]
    · -- Case 4: both points outside the radius `b`.
      have hx : b ^ 2 ≤ Complex.normSq ζ := by
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ hb.le (not_le.mp hζ).le 2
      have hy : b ^ 2 ≤ Complex.normSq ζ' := by
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ hb.le (not_le.mp hζ').le 2
      rw [hz _ hx, hz _ hy, Complex.ofReal_zero, zero_mul, zero_mul, sub_zero, norm_zero]
      exact mul_nonneg (by positivity) (norm_nonneg _)

end Work.NN.Newton.ThinProfile
