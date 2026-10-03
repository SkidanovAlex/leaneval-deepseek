import Mathlib

namespace Work.A6Clean

open scoped ENNReal

/-- Arithmetic–geometric mean inequality in `ℝ≥0∞` (extended nonnegative reals):
`2 u v ≤ u² + v²`.  Stated for `ℝ≥0∞`, where `x - y` is not available, so we use the
canonical-form argument `v = u + w` (resp. `u = v + w`) supplied by the linear order. -/
lemma two_mul_mul_le_sq_add_sq (u v : ENNReal) : 2 * (u * v) ≤ u ^ 2 + v ^ 2 := by
  rcases le_total u v with h | h
  · obtain ⟨w, hw⟩ := le_iff_exists_add.mp h
    rw [hw]
    have hring : u ^ 2 + (u + w) ^ 2 = 2 * (u * (u + w)) + w ^ 2 := by ring
    rw [hring]
    exact le_add_right le_rfl
  · obtain ⟨w, hw⟩ := le_iff_exists_add.mp h
    rw [hw]
    have hring : (v + w) ^ 2 + v ^ 2 = 2 * ((v + w) * v) + w ^ 2 := by ring
    rw [hring]
    exact le_add_right le_rfl

/-- Cauchy–Schwarz (weighted form) for `ℝ≥0∞`-valued series:
`(∑ aᵢ hᵢ)² ≤ (∑ aᵢ)(∑ aᵢ hᵢ²)`.

It is proved by expanding the square as a double series and applying the pointwise
arithmetic–geometric mean inequality, so no subtraction or square roots are needed. -/
lemma ennreal_tsum_mul_sq_le {ι : Type*} (a h : ι → ENNReal) :
    (∑' i, a i * h i) ^ 2 ≤ (∑' i, a i) * (∑' i, a i * h i ^ 2) := by
  have hsq : (∑' i, a i * h i) ^ 2
      = ∑' i, ∑' k, (a i * h i) * (a k * h k) := by
    rw [pow_two, ← ENNReal.tsum_mul_right]
    simp_rw [← ENNReal.tsum_mul_left]
  have hF : (∑' i, ∑' k, a i * a k * h i ^ 2)
      = (∑' i, a i * h i ^ 2) * (∑' i, a i) := by
    have hinner : ∀ i, (∑' k, a i * a k * h i ^ 2) = (a i * h i ^ 2) * (∑' k, a k) := by
      intro i
      have h1 : (fun k => a i * a k * h i ^ 2) = (fun k => (a i * h i ^ 2) * a k) := by
        funext k; ring
      rw [h1, ENNReal.tsum_mul_left]
    simp_rw [hinner]
    rw [ENNReal.tsum_mul_right]
  have hF' : (∑' i, ∑' k, a i * a k * h k ^ 2)
      = (∑' i, a i) * (∑' i, a i * h i ^ 2) := by
    have hinner : ∀ i, (∑' k, a i * a k * h k ^ 2) = a i * (∑' k, a k * h k ^ 2) := by
      intro i
      have h1 : (fun k => a i * a k * h k ^ 2) = (fun k => a i * (a k * h k ^ 2)) := by
        funext k; ring
      rw [h1, ENNReal.tsum_mul_left]
    simp_rw [hinner]
    rw [ENNReal.tsum_mul_right]
  have hstep : 2 * (∑' i, a i * h i) ^ 2
      ≤ ∑' i, ∑' k, (a i * a k * h i ^ 2 + a i * a k * h k ^ 2) := by
    rw [hsq, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => ?_
    have h1 : 2 * (h i * h k) ≤ h i ^ 2 + h k ^ 2 := two_mul_mul_le_sq_add_sq _ _
    calc 2 * ((a i * h i) * (a k * h k))
        = (2 * (h i * h k)) * (a i * a k) := by ring
      _ ≤ (h i ^ 2 + h k ^ 2) * (a i * a k) := mul_le_mul_left h1 _
      _ = a i * a k * h i ^ 2 + a i * a k * h k ^ 2 := by ring
  have hfinal : 2 * (∑' i, a i * h i) ^ 2
      ≤ 2 * ((∑' i, a i) * (∑' i, a i * h i ^ 2)) := by
    calc 2 * (∑' i, a i * h i) ^ 2
        ≤ ∑' i, ∑' k, (a i * a k * h i ^ 2 + a i * a k * h k ^ 2) := hstep
      _ = (∑' i, ∑' k, a i * a k * h i ^ 2) + (∑' i, ∑' k, a i * a k * h k ^ 2) := by
            simp_rw [ENNReal.tsum_add]
      _ = (∑' i, a i * h i ^ 2) * (∑' i, a i)
            + (∑' i, a i) * (∑' i, a i * h i ^ 2) := by rw [hF, hF']
      _ = 2 * ((∑' i, a i) * (∑' i, a i * h i ^ 2)) := by ring
  refine (ENNReal.mul_le_mul_iff_left (c := 2) (by norm_num) (by norm_num)).mp ?_
  calc (∑' i, a i * h i) ^ 2 * 2 = 2 * (∑' i, a i * h i) ^ 2 := by ring
    _ ≤ 2 * ((∑' i, a i) * (∑' i, a i * h i ^ 2)) := hfinal
    _ = ((∑' i, a i) * (∑' i, a i * h i ^ 2)) * 2 := by ring

/-- Translation invariance of the `ℓ²`-sum of a `ℤ`-indexed `ℝ≥0∞`-valued sequence. -/
lemma tsum_sq_sub (g : ℤ → ENNReal) (j : ℤ) :
    (∑' m : ℤ, (g (m - j)) ^ 2) = (∑' m : ℤ, (g m) ^ 2) :=
  (Equiv.addRight (-j)).tsum_eq (fun m : ℤ => (g m) ^ 2)

theorem ennreal_tsum_conv_sq_le (f g : ℤ → ENNReal) :
    (∑' m : ℤ, (∑' j : ℤ, f j * g (m - j)) ^ (2 : ℕ))
      ≤ (∑' j : ℤ, f j) ^ (2 : ℕ) * ∑' m : ℤ, (g m) ^ (2 : ℕ) := by
  calc (∑' m : ℤ, (∑' j : ℤ, f j * g (m - j)) ^ (2 : ℕ))
      ≤ ∑' m : ℤ, (∑' j : ℤ, f j)
          * (∑' j : ℤ, f j * (g (m - j)) ^ (2 : ℕ)) := by
        refine ENNReal.tsum_le_tsum (f := fun m : ℤ =>
            (∑' j : ℤ, f j * g (m - j)) ^ (2 : ℕ)) (g := fun m : ℤ =>
            (∑' j : ℤ, f j) * (∑' j : ℤ, f j * (g (m - j)) ^ (2 : ℕ))) ?_
        intro m
        exact ennreal_tsum_mul_sq_le f (fun j => g (m - j))
    _ = (∑' j : ℤ, f j) * (∑' m : ℤ, ∑' j : ℤ, f j * (g (m - j)) ^ (2 : ℕ)) := by
        rw [ENNReal.tsum_mul_left]
    _ = (∑' j : ℤ, f j) * (∑' j : ℤ, ∑' m : ℤ, f j * (g (m - j)) ^ (2 : ℕ)) := by
        rw [ENNReal.tsum_comm]
    _ = (∑' j : ℤ, f j)
          * (∑' j : ℤ, f j * (∑' m : ℤ, (g (m - j)) ^ (2 : ℕ))) := by
        apply congrArg ((∑' j : ℤ, f j) * ·)
        apply tsum_congr
        intro j
        exact ENNReal.tsum_mul_left
    _ = (∑' j : ℤ, f j)
          * (∑' j : ℤ, f j * (∑' m : ℤ, (g m) ^ (2 : ℕ))) := by
        apply congrArg ((∑' j : ℤ, f j) * ·)
        apply tsum_congr
        intro j
        rw [tsum_sq_sub g j]
    _ = (∑' j : ℤ, f j)
          * ((∑' j : ℤ, f j) * (∑' m : ℤ, (g m) ^ (2 : ℕ))) := by
        rw [ENNReal.tsum_mul_right]
    _ = (∑' j : ℤ, f j) ^ (2 : ℕ) * ∑' m : ℤ, (g m) ^ (2 : ℕ) := by ring

end Work.A6Clean
