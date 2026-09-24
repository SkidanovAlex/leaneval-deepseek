import Mathlib

namespace Work.GM.Affine

theorem ceil_C0T_bounds {C₀ T : ℝ} (hC₀ : 1 ≤ C₀) (hT : 1 ≤ T) :
    1 ≤ Nat.ceil (C₀ * T) ∧ (Nat.ceil (C₀ * T) : ℝ) ≤ 2 * C₀ * T ∧
      C₀ ≤ 1 / C₀ + (Nat.ceil (C₀ * T) : ℝ) * (1 / T) := by
  have hx1 : 1 ≤ C₀ * T := by nlinarith
  have hxpos : 0 < C₀ * T := by nlinarith
  have hTpos : 0 < T := by linarith
  have hCpos : 0 < C₀ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.one_le_ceil_iff]; exact hxpos
  · have h := Nat.ceil_lt_add_one (le_of_lt hxpos) (a := C₀ * T)
    have h2 : C₀ * T + 1 ≤ 2 * C₀ * T := by nlinarith
    linarith
  · have h := Nat.le_ceil (C₀ * T)
    have h2 : C₀ ≤ (Nat.ceil (C₀ * T) : ℝ) / T := by
      rw [le_div_iff₀ hTpos]; linarith
    have h3 : (0:ℝ) ≤ 1 / C₀ := by positivity
    have he : (Nat.ceil (C₀ * T) : ℝ) * (1 / T) = (Nat.ceil (C₀ * T) : ℝ) / T := by ring
    linarith [he]

end Work.GM.Affine
