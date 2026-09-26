import Mathlib
import Submission.Work.Drive.Mono.OneEventNDDefs

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

variable {a₀ b₀ : R3}

/-- **The norm of `τ • a₀ + b₀`** for an orthonormal pair `a₀, b₀`: it is `√(1 + τ²)`, so the
projective coordinate `τ` really is the tangent of the angle. -/
theorem norm_smul_add_eq_sqrt (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (τ : ℝ) : ‖τ • a₀ + b₀‖ = Real.sqrt (1 + τ ^ 2) := by
  have hsq : ‖τ • a₀ + b₀‖ ^ 2 = 1 + τ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq a₀, real_inner_self_eq_norm_sq b₀, ha, hb, hab,
      show inner ℝ b₀ a₀ = 0 from by rw [real_inner_comm]; exact hab]
    ring
  rw [← Real.sqrt_sq (norm_nonneg _), hsq]

/-- **The basic form of `dirOf`**: the unit direction of the projective coordinate `τ` is the
normalised vector `τ • a₀ + b₀`. -/
theorem dirOf_eq_sqrt_smul (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (τ : ℝ) :
    Work.Drive.Mono.Band.dirOf τ a₀ b₀
      = (Real.sqrt (1 + τ ^ 2))⁻¹ • (τ • a₀ + b₀) := by
  rw [Work.Drive.Mono.Band.dirOf, norm_smul_add_eq_sqrt ha hb hab τ]

/-- **The scalar algebra of the derivative of `dirOf`.**  For `S = √(1 + τ²)` the derivative of
`(v ↦ (√(1 + v²))⁻¹ • (v • a + b))` computed by the product rule, namely
`S⁻¹ • a + (-(τ / S) / S²) • (τ • a + b)`, collapses to `(S³)⁻¹ • (a - τ • b)`. -/
theorem smul_algebra_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E)
    (S τ : ℝ) (hS : S ^ 2 = 1 + τ ^ 2) (hSne : S ≠ 0) :
    S⁻¹ • a + (-(τ / S) / S ^ 2) • (τ • a + b) = (S ^ 3)⁻¹ • (a - τ • b) := by
  have h1 : -(τ / S) / S ^ 2 = -(τ / S ^ 3) := by field_simp
  have hc1 : S⁻¹ + -(τ / S ^ 3) * τ = (S ^ 3)⁻¹ := by
    field_simp
    nlinarith [hS]
  have hc2 : τ / S ^ 3 = (S ^ 3)⁻¹ * τ := by field_simp
  rw [h1, smul_add, smul_smul, ← add_assoc, ← add_smul]
  rw [smul_sub, smul_smul, sub_eq_add_neg, neg_smul]
  rw [hc1, hc2]

/-- **`dirOf` is `C²`.** -/
theorem contDiff_two_dirOf (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) :
    ContDiff ℝ 2 (fun τ : ℝ => Work.Drive.Mono.Band.dirOf τ a₀ b₀) := by
  rw [show (fun τ : ℝ => Work.Drive.Mono.Band.dirOf τ a₀ b₀)
      = fun τ : ℝ => (Real.sqrt (1 + τ^2))⁻¹ • (τ • a₀ + b₀) from
    funext (dirOf_eq_sqrt_smul ha hb hab)]
  refine ContDiff.smul (𝕜' := ℝ) ?_ ?_
  · refine ContDiff.inv ?_ ?_
    · rw [contDiff_iff_contDiffAt]
      intro x
      exact (Real.contDiffAt_sqrt (x := 1 + x^2) (by positivity)).comp x
        ((contDiff_const.add (contDiff_id.pow 2)).contDiffAt)
    · intro x
      exact ne_of_gt (Real.sqrt_pos_of_pos (by positivity))
  · exact (contDiff_id.smul contDiff_const).add contDiff_const

/-- **The derivative of `dirOf`**: `d/dτ dirOf τ a₀ b₀ = (√(1+τ²))⁻³ • (a₀ - τ • b₀)`. -/
theorem hasDerivAt_dirOf (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀)
      (((Real.sqrt (1 + τ ^ 2)) ^ 3)⁻¹ • (a₀ - τ • b₀)) τ := by
  have hSpos : 0 < Real.sqrt (1 + τ ^ 2) := Real.sqrt_pos_of_pos (by positivity)
  have hSne : Real.sqrt (1 + τ ^ 2) ≠ 0 := ne_of_gt hSpos
  have hS2 : Real.sqrt (1 + τ ^ 2) ^ 2 = 1 + τ ^ 2 := Real.sq_sqrt (by positivity)
  rw [show (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀)
      = fun s : ℝ => (Real.sqrt (1 + s^2))⁻¹ • (s • a₀ + b₀) from
    funext (fun s => by rw [Work.Drive.Mono.Band.dirOf, norm_smul_add_eq_sqrt ha hb hab s])]
  have hu : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * τ) τ := by
    have h := (hasDerivAt_const (x := τ) (1:ℝ)).add ((hasDerivAt_id τ).pow 2)
    norm_num at h
    exact h
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2)) (τ / Real.sqrt (1 + τ^2)) τ := by
    have h := hu.sqrt (by positivity : (1 + τ^2) ≠ 0)
    rwa [mul_div_mul_left τ (Real.sqrt (1 + τ^2)) (by norm_num : (2:ℝ) ≠ 0)] at h
  have hinv : HasDerivAt (fun x : ℝ => (Real.sqrt (1 + x ^ 2))⁻¹)
      (-(τ / Real.sqrt (1 + τ^2)) / (Real.sqrt (1 + τ^2))^2) τ := hs.inv hSne
  have hv : HasDerivAt (fun x : ℝ => x • a₀ + b₀) a₀ τ := by
    simpa using (((hasDerivAt_id τ).smul_const a₀).add_const b₀)
  have hprod := hinv.smul hv
  rw [smul_algebra_deriv a₀ b₀ (Real.sqrt (1 + τ^2)) τ hS2 hSne] at hprod
  exact hprod

/-- The derivative of `dirOf` in value form. -/
theorem deriv_dirOf (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (τ : ℝ) :
    deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ
      = ((Real.sqrt (1 + τ ^ 2)) ^ 3)⁻¹ • (a₀ - τ • b₀) :=
  (hasDerivAt_dirOf ha hb hab τ).deriv

/-- `a₀ - τ • b₀` never vanishes for an orthonormal pair. -/
theorem sub_smul_ne_zero (ha : ‖a₀‖ = 1) (_hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (τ : ℝ) :
    a₀ - τ • b₀ ≠ 0 := by
  intro h0
  have h : inner ℝ (a₀ - τ • b₀) a₀ = 1 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, ha,
      show inner ℝ b₀ a₀ = 0 from by rw [real_inner_comm]; exact hab]
    ring
  rw [h0, inner_zero_left] at h
  exact one_ne_zero h.symm

theorem dirOfBasic {a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3}
    (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) :
    (∀ τ : ℝ, Work.Drive.Mono.Band.dirOf τ a₀ b₀
        = (Real.sqrt (1 + τ ^ 2))⁻¹ • (τ • a₀ + b₀)) ∧
    ContDiff ℝ 2 (fun τ : ℝ => Work.Drive.Mono.Band.dirOf τ a₀ b₀) ∧
    (∀ (τ : ℝ) (X : LeanEval.KnotTheory.PardonDistortion.R3),
      inner ℝ X (Work.Drive.Mono.Band.dirOf τ a₀ b₀) = 0 →
      inner ℝ X (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ) = 0 →
      inner ℝ X a₀ = 0 ∧ inner ℝ X b₀ = 0) ∧
    (∀ τ : ℝ, deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ ≠ 0) := by
  refine ⟨dirOf_eq_sqrt_smul ha hb hab, contDiff_two_dirOf ha hb hab, ?_, ?_⟩
  · intro τ X hd1 hd2
    have hSne : Real.sqrt (1 + τ ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by positivity))
    have hcne : ((Real.sqrt (1 + τ ^ 2))^3)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 3 hSne)
    have h1 : inner ℝ X (τ • a₀ + b₀) = 0 := by
      rw [dirOf_eq_sqrt_smul ha hb hab τ, real_inner_smul_right] at hd1
      exact (mul_eq_zero.mp hd1).resolve_left (inv_ne_zero hSne)
    have h2 : inner ℝ X (a₀ - τ • b₀) = 0 := by
      rw [deriv_dirOf ha hb hab τ, real_inner_smul_right] at hd2
      exact (mul_eq_zero.mp hd2).resolve_left hcne
    constructor
    · have hv : (1 + τ^2) • a₀ = τ • (τ • a₀ + b₀) + (a₀ - τ • b₀) := by module
      have h3 : inner ℝ X ((1 + τ^2) • a₀) = 0 := by
        rw [hv, inner_add_right, real_inner_smul_right, h1, h2]
        ring
      rw [real_inner_smul_right] at h3
      exact (mul_eq_zero.mp h3).resolve_left (by positivity)
    · have hv : (1 + τ^2) • b₀ = (τ • a₀ + b₀) - τ • (a₀ - τ • b₀) := by module
      have h3 : inner ℝ X ((1 + τ^2) • b₀) = 0 := by
        rw [hv, inner_sub_right, real_inner_smul_right, h1, h2, mul_zero, sub_zero]
      rw [real_inner_smul_right] at h3
      exact (mul_eq_zero.mp h3).resolve_left (by positivity)
  · intro τ
    rw [deriv_dirOf ha hb hab τ]
    have hSne : Real.sqrt (1 + τ ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by positivity))
    exact smul_ne_zero (inv_ne_zero (pow_ne_zero 3 hSne)) (sub_smul_ne_zero ha hb hab τ)

end

end Work.Drive.Mono
