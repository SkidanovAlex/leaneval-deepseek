import Mathlib
import Submission.Work.Peluse.LadderP.stepPState

namespace Work.Peluse.LadderP

theorem coreLeU (j n : ℕ) {e₅₁ : ℕ} (he₅₁ : 1 ≤ e₅₁) {C C₅₁ cη u γ : ℝ} {e : ℕ}
    (hC : 0 < C) (hC₅₁ : 0 < C₅₁) (hcη : 0 < cη)
    (hγ : γ = u ^ (2 ^ (2 ^ (j+1) - 1 + n)) / 4)
    (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hege : 2 ^ (2 ^ (j+1) - 1 + n) * (1 + 2 * e₅₁) * e₅₁ ≤ e)
    (hCle : C ≤ C₅₁ * cη ^ e₅₁ / 4 ^ ((1 + 2 * e₅₁) * e₅₁)) :
    C * u ^ e ≤ C₅₁ * cη ^ e₅₁ * γ ^ ((1 + 2 * e₅₁) * e₅₁) := by
  -- Write `m` for the (huge) exponent of `u` appearing in `γ`, and `N` for `(1+2e₅₁)e₅₁`.
  set m : ℕ := 2 ^ (2 ^ (j+1) - 1 + n) with hm
  set N : ℕ := (1 + 2 * e₅₁) * e₅₁ with hN
  have hu0' : (0:ℝ) ≤ u := le_of_lt hu0
  have h4N : (0:ℝ) < 4 ^ N := pow_pos (by norm_num) N
  -- `γ = u^m/4` and `m * N ≤ e`, so `u^e ≤ u^(m*N)` (as `0 < u ≤ 1`)
  have hmNe : m * N ≤ e := by
    rw [hN, ← Nat.mul_assoc]
    exact hege
  have hmono : u ^ e ≤ u ^ (m * N) := pow_le_pow_of_le_one hu0' hu1 hmNe
  have hγN : γ ^ N = u ^ (m * N) / 4 ^ N := by
    rw [hγ, div_pow, ← pow_mul]
  -- hence `u^e/4^N ≤ γ^N`, and the claim follows from `hCle`
  have hstep : u ^ e / 4 ^ N ≤ γ ^ N := by
    rw [hγN]
    exact div_le_div_of_nonneg_right hmono (le_of_lt h4N)
  have hCne : (0:ℝ) ≤ C₅₁ * cη ^ e₅₁ := by positivity
  calc C * u ^ e ≤ C₅₁ * cη ^ e₅₁ / 4 ^ N * u ^ e :=
        mul_le_mul_of_nonneg_right hCle (by positivity)
    _ = C₅₁ * cη ^ e₅₁ * (u ^ e / 4 ^ N) := by ring
    _ ≤ C₅₁ * cη ^ e₅₁ * γ ^ N := mul_le_mul_of_nonneg_left hstep hCne

end Work.Peluse.LadderP
