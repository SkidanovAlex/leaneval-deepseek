import Mathlib
import Submission.Work.Drive.ZerosCircle.Defs

namespace Work.Drive.ZerosCircle

open scoped InnerProductSpace

/-- **Local surjectivity of the arc parametrisation.**  If `z` and `v` are orthonormal vectors of
`EuclideanSpace ℝ (Fin 2)`, the arc `s ↦ cos s • z + sin s • v` through `z` covers a neighbourhood
of `z` on the unit circle: every unit vector close enough to `z` is `zcArcPt z v s` for some
parameter `s` of modulus `< ε`. -/
theorem zc_exists_arc_param (z v : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) (hv : ‖v‖ = 1)
    (hzv : inner ℝ z v = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z' : EuclideanSpace ℝ (Fin 2), ‖z'‖ = 1 → ‖z' - z‖ < δ →
      ∃ s : ℝ, |s| < ε ∧ z' = zcArcPt z v s := by
  -- the angular radius of the arc we want to cover
  set ε₁ : ℝ := min (ε / 2) (Real.pi / 2) with hε₁def
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]; exact lt_min (by linarith) (by linarith [Real.pi_pos])
  have hε₁lt : ε₁ < ε := by
    rw [hε₁def]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε₁le_pi : ε₁ ≤ Real.pi := by
    rw [hε₁def]; exact le_trans (min_le_right _ _) (by linarith [Real.pi_pos])
  have hcos_lt_one : Real.cos ε₁ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := ε₁) le_rfl hε₁le_pi hε₁pos
    simpa using this
  have h2pos : 0 < 2 - 2 * Real.cos ε₁ := by linarith
  have hdelta_pos : 0 < Real.sqrt (2 - 2 * Real.cos ε₁) := by
    rw [Real.sqrt_pos]; exact h2pos
  refine ⟨Real.sqrt (2 - 2 * Real.cos ε₁), hdelta_pos, ?_⟩
  intro z' hz' hd
  set a : ℝ := ⟪z, z'⟫_ℝ with hadef
  set b : ℝ := ⟪v, z'⟫_ℝ with hbdef
  -- expand `z'` in the orthonormal basis `(z, v)`
  have hexp : z' = a • z + b • v := by
    rw [hadef, hbdef]; exact zc_expand z v z' hz hv hzv
  -- and the coefficients lie on the unit circle
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have h1 : ‖z'‖ ^ 2 = ‖a • z + b • v‖ ^ 2 := by rw [hexp]
    have horth : ⟪a • z, b • v⟫_ℝ = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, hzv, mul_zero, mul_zero]
    have h2 : ‖a • z + b • v‖ ^ 2 = ‖a • z‖ ^ 2 + ‖b • v‖ ^ 2 := by
      simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    have h3 : ‖a • z‖ ^ 2 + ‖b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hz, hv, mul_one, mul_one,
        sq_abs, sq_abs]
    rw [hz'] at h1
    linarith
  have ha_le : a ≤ 1 := by nlinarith [hab, sq_nonneg b]
  have ha_ge : -1 ≤ a := by nlinarith [hab, sq_nonneg b]
  -- the chord distance
  have hdist : ‖z' - z‖ ^ 2 = 2 - 2 * a := by
    rw [norm_sub_sq_real, hz', hz]
    have hiz : ⟪z', z⟫_ℝ = a := by rw [real_inner_comm z z', ← hadef]
    rw [hiz]; ring
  have hdist_lt : ‖z' - z‖ ^ 2 < 2 - 2 * Real.cos ε₁ := by
    have hδsq : Real.sqrt (2 - 2 * Real.cos ε₁) ^ 2 = 2 - 2 * Real.cos ε₁ :=
      Real.sq_sqrt (le_of_lt h2pos)
    nlinarith [hd, hdelta_pos, norm_nonneg (z' - z), hδsq]
  have hcos_lt : Real.cos ε₁ < a := by linarith
  -- so the polar angle is small
  have harccos_le : Real.arccos a ≤ ε₁ := by
    have h := Real.arccos_le_arccos (le_of_lt hcos_lt)
    rwa [Real.arccos_cos (le_of_lt hε₁pos) hε₁le_pi] at h
  have hb2 : b ^ 2 = 1 - a ^ 2 := by linarith
  have habs_b : |b| = Real.sqrt (1 - a ^ 2) := by rw [← hb2, Real.sqrt_sq_eq_abs]
  -- the parametrising angle, with the sign of `s` chosen to match `b`
  have hs : ∃ s, Real.cos s = a ∧ Real.sin s = b ∧ |s| ≤ ε₁ := by
    by_cases hb : 0 ≤ b
    · refine ⟨Real.arccos a, Real.cos_arccos ha_ge ha_le, ?_, ?_⟩
      · rw [Real.sin_arccos, ← habs_b, abs_of_nonneg hb]
      · rw [abs_of_nonneg (Real.arccos_nonneg a)]; exact harccos_le
    · refine ⟨-(Real.arccos a), by rw [Real.cos_neg, Real.cos_arccos ha_ge ha_le], ?_, ?_⟩
      · have hb' : b < 0 := not_le.1 hb
        rw [Real.sin_neg, Real.sin_arccos, ← habs_b, abs_of_neg hb']; ring
      · rw [abs_neg, abs_of_nonneg (Real.arccos_nonneg a)]; exact harccos_le
  obtain ⟨s, hcos_s, hsin_s, hsle⟩ := hs
  exact ⟨s, lt_of_le_of_lt hsle hε₁lt, by rw [hexp, zcArcPt, hcos_s, hsin_s]⟩

end Work.Drive.ZerosCircle
