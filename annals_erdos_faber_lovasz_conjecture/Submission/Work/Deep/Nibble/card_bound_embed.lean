import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.AuxDefs

namespace Work.Deep.Nibble

/-- Elementary real-arithmetic estimate: if `β ≤ 1/4`, `D ≤ n`, and `2 r³ ≤ n`
(the paper's side condition `n` large compared with the rank `r`), then the
product `r (r-1)² ((1+β)D)³ n` is at most `n⁵`.

Indeed `r (r-1)² ≤ r³`, `(1+β)³ ≤ (5/4)³ ≤ 2` and `D³ ≤ n³`, so

`r (r-1)² ((1+β)D)³ n ≤ 2 r³ n⁴ ≤ n⁵`. -/
theorem card_bound_embed {r : ℕ} {β D n M : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1/4) (hD0 : 0 < D) (hDn : D ≤ n)
    (hn : 2 * r^3 ≤ n)
    (hM : M ≤ r * (r - 1)^2 * ((1+β)*D)^3 * n) : M ≤ n^5 := by
  have hn0 : 0 < n := lt_of_lt_of_le hD0 hDn
  have hD0' : 0 ≤ D := le_of_lt hD0
  have h1β0 : 0 ≤ 1 + β := by linarith
  have hA0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  -- the factor `(1+β)³` is at most `2`
  have hC : (1+β)^3 ≤ 2 := by
    have h1 : (1+β)^3 ≤ (5/4:ℝ)^3 := pow_le_pow_left₀ h1β0 (by linarith) 3
    have h2 : (5/4:ℝ)^3 ≤ 2 := by norm_num
    linarith
  -- `D³ ≤ n³`
  have hD3 : D^3 ≤ n^3 := pow_le_pow_left₀ hD0' hDn 3
  -- `r (r-1)² ≤ r³`
  have hS : (r:ℝ) * ((r:ℝ)-1)^2 ≤ (r:ℝ)^3 := by
    rcases Nat.eq_zero_or_pos r with h0 | hp
    · subst r
      norm_num
    · have hA1 : (1:ℝ) ≤ (r:ℝ) := by
        have h1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hp.ne'
        exact_mod_cast h1
      have hsq : ((r:ℝ)-1)^2 ≤ (r:ℝ)^2 := by
        have e : (r:ℝ)^2 - ((r:ℝ)-1)^2 = 2*(r:ℝ) - 1 := by ring
        linarith
      calc (r:ℝ) * ((r:ℝ)-1)^2 ≤ (r:ℝ) * (r:ℝ)^2 := mul_le_mul_of_nonneg_left hsq hA0
        _ = (r:ℝ)^3 := by ring
  have hCD0 : 0 ≤ (1+β)^3 * D^3 := mul_nonneg (pow_nonneg h1β0 3) (pow_nonneg hD0' 3)
  have hA30 : 0 ≤ (r:ℝ)^3 := pow_nonneg hA0 3
  have key : (r:ℝ) * ((r:ℝ)-1)^2 * ((1+β)^3 * D^3) ≤ (r:ℝ)^3 * (2 * n^3) :=
    mul_le_mul hS (mul_le_mul hC hD3 (pow_nonneg hD0' 3) (by norm_num)) hCD0 hA30
  refine le_trans hM ?_
  rw [mul_pow]
  refine le_trans (mul_le_mul_of_nonneg_right key (le_of_lt hn0)) ?_
  calc (r:ℝ)^3 * (2 * n^3) * n = 2 * (r:ℝ)^3 * n^4 := by ring
    _ ≤ n * n^4 := mul_le_mul_of_nonneg_right hn (pow_nonneg (le_of_lt hn0) 4)
    _ = n^5 := by ring

end Work.Deep.Nibble
