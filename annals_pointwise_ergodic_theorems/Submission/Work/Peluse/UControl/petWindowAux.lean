import Mathlib
import Submission.Work.Peluse.UControl.petWindowBookkeeping

/-!
# Elementary properties of the chain window

`petWindow γ D n = min 1 (petChainLevel γ (n-1)^2 / (20000 (2^{n-1} D + 1)))` is positive when
`n ≥ 1`, bounded by `1` and bounded by `γ` (for `0 < γ ≤ 1`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

lemma petWindow_le_one (γ : ℝ) (D n : ℕ) : petWindow γ D n ≤ 1 := min_le_left _ _

lemma petWindow_pos (γ : ℝ) (D n : ℕ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hn : 1 ≤ n)
    (hD : 1 ≤ D) : 0 < petWindow γ D n := by
  have h := petWindow_lower γ D n hγ0 hγ1 hn hD
  have h2 : 0 < γ ^ (2 ^ n + 1) / (2000 ^ (2 ^ n) * 20000 * (2 : ℝ) ^ n * (D : ℝ)) := by
    positivity
  linarith

lemma petWindow_le_gamma (γ : ℝ) (D n : ℕ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hn : 1 ≤ n) :
    petWindow γ D n ≤ γ := by
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hγp : γ ^ (2 ^ n) ≤ γ := by
    have := pow_le_pow_of_le_one hγ0.le hγ1 hpow
    simpa using this
  have hden : (1 : ℝ) ≤ 2000 ^ (2 ^ n - 2) := one_le_pow₀ (by norm_num)
  have hdenpos : (0 : ℝ) < 2000 ^ (2 ^ n - 2) := by positivity
  have h1a : (0 : ℝ) ≤ (((2 ^ (n - 1) * D : ℕ) : ℝ)) := by positivity
  have h1 : (1 : ℝ) ≤ 20000 * (((2 ^ (n - 1) * D : ℕ) : ℝ) + 1) := by nlinarith
  have hx : petChainLevel γ (n - 1) ^ 2 / (20000 * (((2 ^ (n - 1) * D : ℕ) : ℝ) + 1)) ≤ γ := by
    rw [petChainLevel_sq_pred γ n hn, div_div]
    rw [div_le_iff₀ (by positivity :
      (0 : ℝ) < 2000 ^ (2 ^ n - 2) * (20000 * (((2 ^ (n - 1) * D : ℕ) : ℝ) + 1)))]
    have hBC : (1 : ℝ) ≤ 2000 ^ (2 ^ n - 2) * (20000 * (((2 ^ (n - 1) * D : ℕ) : ℝ) + 1)) := by
      nlinarith [hden, h1]
    have hle : γ ≤ γ * (2000 ^ (2 ^ n - 2) * (20000 * (((2 ^ (n - 1) * D : ℕ) : ℝ) + 1))) := by
      have := mul_le_mul_of_nonneg_left hBC hγ0.le
      simpa using this
    linarith [hγp, hle]
  calc petWindow γ D n
      = min 1 (petChainLevel γ (n - 1) ^ 2 / (20000 * (((2 ^ (n - 1) * D : ℕ) : ℝ) + 1))) := rfl
    _ ≤ _ := min_le_right _ _
    _ ≤ γ := hx

end

end Work.Peluse.UControl
