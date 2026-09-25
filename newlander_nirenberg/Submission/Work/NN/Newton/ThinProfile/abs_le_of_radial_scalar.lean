import Mathlib

namespace Work.NN.Newton.ThinProfile

/-- **Lipschitz bound for a radial scalar profile.**  Let `φ : ℝ → ℝ` be `M`-Lipschitz and
suppose `φ (c * (b ^ 2 - s)) = 0` whenever `b ^ 2 ≤ s`.  Then
`ζ ↦ φ (c * (b ^ 2 - ‖ζ‖²))` is Lipschitz with constant `2 b M c`.

Proof route: set `t = ‖ζ‖`, `t' = ‖ζ'‖` and `x = c(b²-t²)`, `x' = c(b²-t'²)`; use
`hLip` and `|t - t'| ≤ ‖ζ - ζ'‖` (`abs_norm_sub_norm_le`).  If `t, t' ≤ b` then
`|x - x'| = c|t - t'|(t + t') ≤ 2bc|t - t'|`.  If `t, t' ≥ b` then `hz` makes both sides zero.
If `t ≤ b ≤ t'` then `hz` kills the second value and `|φ x| ≤ M|x| = Mc(b-t)(b+t) ≤ 2bMc(b-t)
≤ 2bMc|t - t'|`. -/
lemma abs_le_of_radial_scalar {φ : ℝ → ℝ} {b M c : ℝ} (hb : 0 < b) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hlip : ∀ x y : ℝ, |φ x - φ y| ≤ M * |x - y|)
    (hz : ∀ s : ℝ, b ^ 2 ≤ s → φ (c * (b ^ 2 - s)) = 0) :
    ∀ ζ ζ' : ℂ, |φ (c * (b ^ 2 - Complex.normSq ζ)) - φ (c * (b ^ 2 - Complex.normSq ζ'))|
      ≤ 2 * b * M * c * ‖ζ - ζ'‖ := by
  intro ζ ζ'
  rw [Complex.normSq_eq_norm_sq ζ, Complex.normSq_eq_norm_sq ζ']
  -- Real-variable core, ordered form `t ≤ t'`.
  have key_ordered : ∀ t t' : ℝ, 0 ≤ t → 0 ≤ t' → t ≤ t' →
      |φ (c * (b ^ 2 - t ^ 2)) - φ (c * (b ^ 2 - t' ^ 2))| ≤ 2 * b * M * c * |t - t'| := by
    intro t t' ht ht' hle
    by_cases ht'b : t' ≤ b
    · -- both on the inner side of the boundary
      have htb : t ≤ b := le_trans hle ht'b
      have hstep : |c * (b ^ 2 - t ^ 2) - c * (b ^ 2 - t' ^ 2)| = c * (|t - t'| * (t + t')) := by
        rw [show c * (b ^ 2 - t ^ 2) - c * (b ^ 2 - t' ^ 2) = c * (t' ^ 2 - t ^ 2) by ring]
        rw [abs_mul, abs_of_nonneg hc]
        rw [show t' ^ 2 - t ^ 2 = (t' - t) * (t' + t) by ring]
        rw [abs_mul, abs_sub_comm t' t, abs_of_nonneg (by linarith : (0:ℝ) ≤ t' + t)]
        ring
      calc |φ (c * (b ^ 2 - t ^ 2)) - φ (c * (b ^ 2 - t' ^ 2))|
          ≤ M * |c * (b ^ 2 - t ^ 2) - c * (b ^ 2 - t' ^ 2)| := hlip _ _
        _ = M * (c * (|t - t'| * (t + t'))) := by rw [hstep]
        _ ≤ 2 * b * M * c * |t - t'| := by
              have hsum : t + t' ≤ 2 * b := by linarith
              have hnn : (0:ℝ) ≤ M * c * |t - t'| := by positivity
              calc M * (c * (|t - t'| * (t + t')))
                  = (M * c * |t - t'|) * (t + t') := by ring
                _ ≤ (M * c * |t - t'|) * (2 * b) := mul_le_mul_of_nonneg_left hsum hnn
                _ = 2 * b * M * c * |t - t'| := by ring
    · by_cases htb : t ≤ b
      · -- `t ≤ b < t'`: `hz` kills the second value
        have htb' : b < t' := not_le.mp ht'b
        have hB : φ (c * (b ^ 2 - t' ^ 2)) = 0 := hz (t' ^ 2) (by nlinarith [hb, ht', htb'])
        have hφ0 : φ 0 = 0 := by simpa using hz (b ^ 2) le_rfl
        have hle_t2 : t ^ 2 ≤ b ^ 2 := by nlinarith [htb, ht, hb]
        have hxnn : (0:ℝ) ≤ c * (b ^ 2 - t ^ 2) := mul_nonneg hc (by linarith)
        have hdiff : b - t ≤ |t - t'| := by
          have h2 : |t - t'| = t' - t := by rw [abs_of_neg (by linarith)]; ring
          linarith
        calc |φ (c * (b ^ 2 - t ^ 2)) - φ (c * (b ^ 2 - t' ^ 2))|
            = |φ (c * (b ^ 2 - t ^ 2))| := by rw [hB, sub_zero]
          _ = |φ (c * (b ^ 2 - t ^ 2)) - φ 0| := by rw [hφ0, sub_zero]
          _ ≤ M * |c * (b ^ 2 - t ^ 2) - 0| := hlip _ _
          _ = M * (c * (b ^ 2 - t ^ 2)) := by rw [sub_zero, abs_of_nonneg hxnn]
          _ = M * (c * ((b - t) * (b + t))) := by ring
          _ ≤ M * (c * ((b - t) * (2 * b))) := by
                apply mul_le_mul_of_nonneg_left _ hM
                apply mul_le_mul_of_nonneg_left _ hc
                exact mul_le_mul_of_nonneg_left (by linarith : b + t ≤ 2 * b)
                  (by linarith : (0:ℝ) ≤ b - t)
          _ ≤ M * (c * (|t - t'| * (2 * b))) := by
                apply mul_le_mul_of_nonneg_left _ hM
                apply mul_le_mul_of_nonneg_left _ hc
                exact mul_le_mul_of_nonneg_right hdiff (by linarith : (0:ℝ) ≤ 2 * b)
          _ = 2 * b * M * c * |t - t'| := by ring
      · -- `b < t ≤ t'`: `hz` kills both values
        have htb' : b < t := not_le.mp htb
        have ht'b' : b < t' := not_le.mp ht'b
        have hA : φ (c * (b ^ 2 - t ^ 2)) = 0 := hz (t ^ 2) (by nlinarith [hb, ht, htb'])
        have hB : φ (c * (b ^ 2 - t' ^ 2)) = 0 := hz (t' ^ 2) (by nlinarith [hb, ht', ht'b'])
        rw [hA, hB, sub_zero, abs_zero]
        positivity
  have ht : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg ζ
  have ht' : (0:ℝ) ≤ ‖ζ'‖ := norm_nonneg ζ'
  by_cases hle : ‖ζ‖ ≤ ‖ζ'‖
  · calc |φ (c * (b ^ 2 - ‖ζ‖ ^ 2)) - φ (c * (b ^ 2 - ‖ζ'‖ ^ 2))|
        ≤ 2 * b * M * c * |‖ζ‖ - ‖ζ'‖| := key_ordered _ _ ht ht' hle
      _ ≤ 2 * b * M * c * ‖ζ - ζ'‖ :=
            mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le ζ ζ') (by positivity)
  · have hle' : ‖ζ'‖ ≤ ‖ζ‖ := le_of_not_ge hle
    calc |φ (c * (b ^ 2 - ‖ζ‖ ^ 2)) - φ (c * (b ^ 2 - ‖ζ'‖ ^ 2))|
        = |φ (c * (b ^ 2 - ‖ζ'‖ ^ 2)) - φ (c * (b ^ 2 - ‖ζ‖ ^ 2))| := by rw [abs_sub_comm]
      _ ≤ 2 * b * M * c * |‖ζ'‖ - ‖ζ‖| := key_ordered _ _ ht' ht hle'
      _ = 2 * b * M * c * |‖ζ‖ - ‖ζ'‖| := by rw [abs_sub_comm (‖ζ'‖) (‖ζ‖)]
      _ ≤ 2 * b * M * c * ‖ζ - ζ'‖ :=
            mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le ζ ζ') (by positivity)

end Work.NN.Newton.ThinProfile
