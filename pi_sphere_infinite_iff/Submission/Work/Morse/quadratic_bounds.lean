import Mathlib

set_option synthInstance.maxHeartbeats 400000

/-!
# Bounds for a positive-definite continuous bilinear form on `ℝⁿ`

For a continuous bilinear form `A` on `EuclideanSpace ℝ (Fin n)` which is positive on the
diagonal off the origin (`A v v > 0` for `v ≠ 0`), there are constants `c > 0` and `C` with
`c * ‖y‖^2 ≤ A y y ≤ C * ‖y‖^2` for every `y`.

The upper bound is immediate from continuity of `A` (with `C = ‖A‖`); the lower bound follows
from compactness of the unit sphere, on which `y ↦ A y y` attains a positive minimum.
-/

namespace Work.Morse

open Metric

/-- A positive-definite continuous bilinear form on `ℝⁿ` is bounded below by `c * ‖y‖^2` for
some `c > 0`, and above by `C * ‖y‖^2` for `C = ‖A‖`. -/
theorem quadratic_bounds {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hApos : ∀ v, v ≠ 0 → 0 < A v v) :
    ∃ c > 0, ∃ C, ∀ y : EuclideanSpace ℝ (Fin n),
      c * ‖y‖^2 ≤ A y y ∧ A y y ≤ C * ‖y‖^2 := by
  -- The upper bound only uses continuity of `A`.
  have hupper : ∀ y : EuclideanSpace ℝ (Fin n), A y y ≤ ‖A‖ * ‖y‖^2 := by
    intro y
    have h2 : ‖A y y‖ ≤ ‖A‖ * ‖y‖^2 := by
      calc ‖A y y‖ ≤ ‖A y‖ * ‖y‖ := ContinuousLinearMap.le_opNorm (A y) y
        _ ≤ (‖A‖ * ‖y‖) * ‖y‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm A y) (norm_nonneg y)
        _ = ‖A‖ * ‖y‖^2 := by ring
    calc A y y ≤ |A y y| := le_abs_self _
      _ = ‖A y y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖A‖ * ‖y‖^2 := h2
  by_cases hn : n = 0
  · -- The space is trivial, so the lower bound is vacuous.
    subst hn
    refine ⟨1, one_pos, ‖A‖, ?_⟩
    intro y
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    exact ⟨by simp, hupper 0⟩
  · -- The unit sphere is compact and `y ↦ A y y` attains a positive minimum on it.
    have hne : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    have hcont : Continuous fun y : EuclideanSpace ℝ (Fin n) => A y y :=
      A.continuous.clm_apply continuous_id
    obtain ⟨i⟩ := hne
    have hmem : EuclideanSpace.single i (1 : ℝ) ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simp only [mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single, norm_one]
    obtain ⟨y₀, hy₀S, hy₀min⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMinOn ⟨_, hmem⟩
        hcont.continuousOn
    have hy₀n : ‖y₀‖ = 1 := by
      rw [mem_sphere] at hy₀S
      rwa [dist_eq_norm, sub_zero] at hy₀S
    have hy₀ne : y₀ ≠ 0 := by
      intro h
      rw [h] at hy₀n
      simp at hy₀n
    refine ⟨A y₀ y₀, hApos y₀ hy₀ne, ‖A‖, ?_⟩
    intro y
    refine ⟨?_, hupper y⟩
    by_cases hy : y = 0
    · subst hy
      simp
    · have hynorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
      have hsphere : (‖y‖⁻¹ : ℝ) • y ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        rw [mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg (norm_nonneg y), inv_mul_cancel₀ hynorm]
      have hmin : A y₀ y₀ ≤ A ((‖y‖⁻¹ : ℝ) • y) ((‖y‖⁻¹ : ℝ) • y) := by
        simpa using hy₀min hsphere
      have hval : A ((‖y‖⁻¹ : ℝ) • y) ((‖y‖⁻¹ : ℝ) • y) = (‖y‖⁻¹)^2 * A y y := by
        have h1 : A ((‖y‖⁻¹ : ℝ) • y) = (‖y‖⁻¹ : ℝ) • A y :=
          ContinuousLinearMap.map_smul A _ y
        rw [h1, smul_apply, ContinuousLinearMap.map_smul]
        simp only [smul_eq_mul]
        ring
      rw [hval] at hmin
      have hle : ‖y‖^2 * (A y₀ y₀) ≤ ‖y‖^2 * ((‖y‖⁻¹)^2 * A y y) :=
        mul_le_mul_of_nonneg_left hmin (by positivity)
      have h2 : ‖y‖^2 * ((‖y‖⁻¹)^2 * A y y) = A y y := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hynorm, one_pow, one_mul]
      calc A y₀ y₀ * ‖y‖^2 = ‖y‖^2 * (A y₀ y₀) := by ring
        _ ≤ ‖y‖^2 * ((‖y‖⁻¹)^2 * A y y) := hle
        _ = A y y := h2

end Work.Morse
