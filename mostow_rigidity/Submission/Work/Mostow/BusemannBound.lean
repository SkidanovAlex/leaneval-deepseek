import Mathlib
import Submission.Work.Mostow.BCGDefs

/-!
# Uniform bounds for the gradient and Hessian of the Busemann function

The Euclidean gradient and Hessian of `y ↦ busemann ξ y` are

  `gradB n ξ y = (tpart y - ⟪y,ξ⟫)⁻¹ • ((tpart y)⁻¹ • y - ξ)`,
  `hessB n ξ y = (tpart y - ⟪y,ξ⟫)⁻¹ • ((tpart y)⁻¹ • 1 - (tpart y ^ 3)⁻¹ • (innerSL ℝ y).smulRight y)
                  - (innerSL ℝ (gradB n ξ y)).smulRight (gradB n ξ y)`.

Writing `s = tpart y = √(1+‖y‖²)`, `g = s - ⟪y,ξ⟫` and `r = ‖y‖`, for `ξ ∈ Sph n`
Cauchy–Schwarz gives `⟪y,ξ⟫ ≤ r < s`, hence `g ≥ s - r > 0`, and

  `g⁻¹ ≤ (s - r)⁻¹ = s + r ≤ √(1+R²) + R`  whenever `r ≤ R , R ≥ 0`.

From this the two bound statements are immediate triangle-inequality estimates.
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

variable {n : ℕ}

/-- `tpart y = √(1+‖y‖²)` dominates `‖y‖`. -/
lemma norm_lt_tpart_BusemannBound (y : E n) : ‖y‖ < tpart y := by
  rw [tpart, Real.lt_sqrt (norm_nonneg y)]
  nlinarith [sq_nonneg ‖y‖]

/-- `tpart y = √(1+‖y‖²) ≥ 1`. -/
lemma one_le_tpart_BusemannBound (y : E n) : (1 : ℝ) ≤ tpart y := by
  rw [tpart]
  have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + ‖y‖ ^ 2 by nlinarith [sq_nonneg ‖y‖])
  rwa [Real.sqrt_one] at this

/-- `tpart y > 0`. -/
lemma tpart_pos' (y : E n) : 0 < tpart y := by rw [tpart]; positivity

/-- Rationalising: `(tpart y - ‖y‖)⁻¹ = tpart y + ‖y‖`. -/
lemma inv_tpart_sub_norm (y : E n) : (tpart y - ‖y‖)⁻¹ = tpart y + ‖y‖ := by
  have hs : tpart y ^ 2 = 1 + ‖y‖ ^ 2 := by rw [tpart]; exact Real.sq_sqrt (by positivity)
  exact inv_eq_of_mul_eq_one_right (by nlinarith [hs])

/-- Monotonicity of `tpart`. -/
lemma tpart_le_sqrt {R : ℝ} (y : E n) (hy : ‖y‖ ≤ R) (hR : 0 ≤ R) :
    tpart y ≤ Real.sqrt (1 + R ^ 2) := by
  rw [tpart]; apply Real.sqrt_le_sqrt
  nlinarith [hy, hR, norm_nonneg y]

/-- The key lower bound on `g = tpart y - ⟪y,ξ⟫` on the ball of radius `R`. -/
lemma inv_g_le (ξ y : E n) (hξ : ξ ∈ Sph n) {R : ℝ} (hR : 0 ≤ R) (hy : ‖y‖ ≤ R) :
    (tpart y - inner ℝ y ξ)⁻¹ ≤ Real.sqrt (1 + R ^ 2) + R := by
  have hξ1 : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have hinner : inner ℝ y ξ ≤ ‖y‖ := by
    have := real_inner_le_norm y ξ
    rwa [hξ1, mul_one] at this
  have hspos : 0 < tpart y - ‖y‖ := by have := norm_lt_tpart_BusemannBound y; linarith
  have h1 : (tpart y - inner ℝ y ξ)⁻¹ ≤ (tpart y - ‖y‖)⁻¹ := inv_anti₀ hspos (by linarith)
  rw [inv_tpart_sub_norm y] at h1
  have h2 : tpart y + ‖y‖ ≤ Real.sqrt (1 + R ^ 2) + R := by
    have := tpart_le_sqrt y hy hR; linarith
  linarith

/-- Uniform bound on the Euclidean gradient of the Busemann function. -/
lemma norm_gradB_le (ξ y : E n) (hξ : ξ ∈ Sph n) {R : ℝ} (hR : 0 ≤ R) (hy : ‖y‖ ≤ R) :
    ‖gradB n ξ y‖ ≤ (Real.sqrt (1 + R ^ 2) + R) * (R + 1) := by
  have hξ1 : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have hKnn : 0 ≤ Real.sqrt (1 + R ^ 2) + R := by
    have := Real.sqrt_nonneg (1 + R ^ 2); linarith
  have hinner : inner ℝ y ξ ≤ ‖y‖ := by
    have := real_inner_le_norm y ξ
    rwa [hξ1, mul_one] at this
  have hgpos : 0 < tpart y - inner ℝ y ξ := by have := norm_lt_tpart_BusemannBound y; linarith
  have hinv := inv_g_le ξ y hξ hR hy
  have hinvnn : 0 ≤ (tpart y - inner ℝ y ξ)⁻¹ := inv_nonneg.mpr hgpos.le
  have hnum : ‖(tpart y)⁻¹ • y - ξ‖ ≤ R + 1 := by
    have ht1 : (1 : ℝ) ≤ tpart y := one_le_tpart_BusemannBound y
    have hty : (tpart y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
    have hsm : ‖(tpart y)⁻¹ • y‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (tpart_pos' y).le)]
      calc (tpart y)⁻¹ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hty (norm_nonneg y)
        _ ≤ R := by rw [one_mul]; exact hy
    calc ‖(tpart y)⁻¹ • y - ξ‖ ≤ ‖(tpart y)⁻¹ • y‖ + ‖ξ‖ := norm_sub_le _ _
      _ ≤ R + 1 := by rw [hξ1]; linarith
  rw [gradB]
  calc ‖(tpart y - inner ℝ y ξ)⁻¹ • ((tpart y)⁻¹ • y - ξ)‖
      = |(tpart y - inner ℝ y ξ)⁻¹| * ‖(tpart y)⁻¹ • y - ξ‖ := norm_smul _ _
    _ = (tpart y - inner ℝ y ξ)⁻¹ * ‖(tpart y)⁻¹ • y - ξ‖ := by rw [abs_of_nonneg hinvnn]
    _ ≤ (Real.sqrt (1 + R ^ 2) + R) * (R + 1) := mul_le_mul hinv hnum (norm_nonneg _) hKnn

/-- Uniform bound on the Euclidean Hessian of the Busemann function. -/
lemma norm_hessB_le (ξ y : E n) (hξ : ξ ∈ Sph n) {R : ℝ} (hR : 0 ≤ R) (hy : ‖y‖ ≤ R) :
    ‖hessB n ξ y‖ ≤
      (Real.sqrt (1 + R ^ 2) + R) * (1 + R ^ 2)
        + ((Real.sqrt (1 + R ^ 2) + R) * (R + 1)) ^ 2 := by
  have hKnn : 0 ≤ Real.sqrt (1 + R ^ 2) + R := by
    have := Real.sqrt_nonneg (1 + R ^ 2); linarith
  have hinner : inner ℝ y ξ ≤ ‖y‖ := by
    have := real_inner_le_norm y ξ
    have hξ1 : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
    rwa [hξ1, mul_one] at this
  have hgpos : 0 < tpart y - inner ℝ y ξ := by have := norm_lt_tpart_BusemannBound y; linarith
  have hinv := inv_g_le ξ y hξ hR hy
  have hinvnn : 0 ≤ (tpart y - inner ℝ y ξ)⁻¹ := inv_nonneg.mpr hgpos.le
  have ht1 : (1 : ℝ) ≤ tpart y := one_le_tpart_BusemannBound y
  have hty : (tpart y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
  have ht3 : ((tpart y) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ht1)
  have hsm : ‖(innerSL ℝ y).smulRight y‖ = ‖y‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]; ring
  have hid : ‖(1 : E n →L[ℝ] E n)‖ ≤ 1 := by
    rw [show (1 : E n →L[ℝ] E n) = ContinuousLinearMap.id ℝ (E n) from rfl]
    exact ContinuousLinearMap.norm_id_le
  have hfirst : ‖(tpart y)⁻¹ • (1 : E n →L[ℝ] E n)
      - ((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y‖ ≤ 1 + R ^ 2 := by
    have h1 : ‖(tpart y)⁻¹ • (1 : E n →L[ℝ] E n)‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (tpart_pos' y).le)]
      calc (tpart y)⁻¹ * ‖(1 : E n →L[ℝ] E n)‖ ≤ 1 * 1 :=
            mul_le_mul hty hid (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    have h2 : ‖((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y‖ ≤ R ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (tpart_pos' y).le 3)), hsm]
      calc ((tpart y) ^ 3)⁻¹ * ‖y‖ ^ 2 ≤ 1 * R ^ 2 := by
            apply mul_le_mul ht3 _ (by positivity) (by norm_num)
            nlinarith [hy, norm_nonneg y]
        _ = R ^ 2 := by ring
    calc ‖(tpart y)⁻¹ • (1 : E n →L[ℝ] E n)
          - ((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y‖
        ≤ ‖(tpart y)⁻¹ • (1 : E n →L[ℝ] E n)‖
          + ‖((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y‖ := norm_sub_le _ _
      _ ≤ 1 + R ^ 2 := add_le_add h1 h2
  have hsecond : ‖(innerSL ℝ (gradB n ξ y)).smulRight (gradB n ξ y)‖ ≤
      ((Real.sqrt (1 + R ^ 2) + R) * (R + 1)) ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    have hg := norm_gradB_le ξ y hξ hR hy
    have h0 : 0 ≤ ‖gradB n ξ y‖ := norm_nonneg _
    calc ‖gradB n ξ y‖ * ‖gradB n ξ y‖ = ‖gradB n ξ y‖ ^ 2 := by ring
      _ ≤ ((Real.sqrt (1 + R ^ 2) + R) * (R + 1)) ^ 2 := by
            simpa using pow_le_pow_left₀ h0 hg 2
  rw [hessB]
  calc ‖(tpart y - inner ℝ y ξ)⁻¹ • ((tpart y)⁻¹ • (1 : E n →L[ℝ] E n)
          - ((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y)
        - (innerSL ℝ (gradB n ξ y)).smulRight (gradB n ξ y)‖
      ≤ ‖(tpart y - inner ℝ y ξ)⁻¹ • ((tpart y)⁻¹ • (1 : E n →L[ℝ] E n)
          - ((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y)‖
        + ‖(innerSL ℝ (gradB n ξ y)).smulRight (gradB n ξ y)‖ := norm_sub_le _ _
    _ = |(tpart y - inner ℝ y ξ)⁻¹| * ‖(tpart y)⁻¹ • (1 : E n →L[ℝ] E n)
          - ((tpart y) ^ 3)⁻¹ • (innerSL ℝ y).smulRight y‖
        + ‖(innerSL ℝ (gradB n ξ y)).smulRight (gradB n ξ y)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (Real.sqrt (1 + R ^ 2) + R) * (1 + R ^ 2)
          + ((Real.sqrt (1 + R ^ 2) + R) * (R + 1)) ^ 2 := by
        rw [abs_of_nonneg hinvnn]
        exact add_le_add (mul_le_mul hinv hfirst (norm_nonneg _) hKnn) hsecond

theorem BusemannBound (n : ℕ) :
    (∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ y : Submission.Mostow.E n, ‖y‖ ≤ R → ‖Work.Mostow.gradB n ξ y‖ ≤ C) ∧
    (∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ y : Submission.Mostow.E n, ‖y‖ ≤ R → ‖Work.Mostow.hessB n ξ y‖ ≤ C) := by
  constructor
  · intro R hR
    exact ⟨(Real.sqrt (1 + R ^ 2) + R) * (R + 1),
      fun ξ hξ y hy => norm_gradB_le ξ y hξ hR hy⟩
  · intro R hR
    exact ⟨(Real.sqrt (1 + R ^ 2) + R) * (1 + R ^ 2)
        + ((Real.sqrt (1 + R ^ 2) + R) * (R + 1)) ^ 2,
      fun ξ hξ y hy => norm_hessB_le ξ y hξ hR hy⟩

end

end Work.Mostow
