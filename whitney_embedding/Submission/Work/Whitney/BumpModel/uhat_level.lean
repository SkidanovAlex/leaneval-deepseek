import Mathlib
import Submission.Work.Whitney.BumpModel.Defs

namespace Work.Whitney.BumpModel

open Work.Whitney

/-- Coordinates of `t • e₀`: only the zeroth coordinate survives. -/
theorem smul_e0_apply (n : ℕ) [NeZero n] (t : ℝ) (i : Fin n) :
    (t • e0 n : Fin n → ℝ) i = if i = 0 then t else 0 := by
  simp only [Pi.smul_apply, e0, Pi.single_apply]
  by_cases h : i = 0 <;> simp [h]

/-- `∑ᵢ (t • e₀)ᵢ² = t²`, hence `u (t • e₀) = 1 + t²`. -/
theorem bumpU_smul_e0 (n : ℕ) [NeZero n] (t : ℝ) :
    bumpU n (t • e0 n) = 1 + t ^ 2 := by
  have h : ∀ i : Fin n, (t • e0 n) i ^ 2 = if i = 0 then t ^ 2 else 0 := by
    intro i
    rw [smul_e0_apply n t i]
    by_cases h : i = 0 <;> simp [h]
  rw [bumpU, Finset.sum_congr rfl fun i _ => h i]
  rw [Finset.sum_ite_eq']
  simp

/-- Along the axis, `û` is just `χ` divided by `1 + t²`. -/
theorem uhat_smul_e0 (n : ℕ) [NeZero n] (χ : (Fin n → ℝ) → ℝ) (t : ℝ) :
    uhat n χ (t • e0 n) = χ (t • e0 n) / (1 + t ^ 2) := by
  rw [uhat, bumpU_smul_e0]

/-- Level set of `û = χ/(1 + ∑xᵢ²)` on the axis: if `χ = 1` on the closed ball of radius `2` and `χ ≤ 1` everywhere, then `û` takes the value `1/2` on the axis exactly at `±e₀`. -/
theorem uhat_level (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ} (hχ1 : ∀ x, ‖x‖ ≤ 2 → χ x = 1)
    (hχle : ∀ x, χ x ≤ 1) (t : ℝ) :
    Work.Whitney.uhat n χ (t • Work.Whitney.e0 n) = 1 / 2 ↔ t = 1 ∨ t = -1 := by
  rw [uhat_smul_e0]
  constructor
  · intro h
    have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have ht2 : t ^ 2 ≤ 1 := by
      have h' : χ (t • e0 n) = (1 / 2) * (1 + t ^ 2) := (div_eq_iff hden.ne').mp h
      nlinarith [hχle (t • e0 n)]
    have ht : |t| ≤ 1 := (sq_le_one_iff_abs_le_one t).mp ht2
    have hnorm : ‖t • e0 n‖ ≤ 2 := by rw [norm_smul_e0 n]; linarith
    have hc1 : χ (t • e0 n) = 1 := hχ1 _ hnorm
    rw [hc1] at h
    have ht1 : t ^ 2 = 1 := by
      have h' := (div_eq_iff hden.ne').mp h
      nlinarith
    exact sq_eq_one_iff.mp ht1
  · rintro (rfl | rfl)
    · have hc : χ (e0 n) = 1 := hχ1 _ (by rw [norm_e0 n]; norm_num)
      rw [one_smul, hc]
      norm_num
    · have hc : χ (-(e0 n)) = 1 := hχ1 _ (by rw [norm_neg, norm_e0 n]; norm_num)
      rw [neg_smul, one_smul, hc]
      norm_num

end Work.Whitney.BumpModel
