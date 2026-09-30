import Mathlib
import Submission.Work.BMF.liouville.vk_large_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Finset
open scoped BigOperators

noncomputable section

/-- Pure arithmetic input: `8 n² + n ≤ 2ⁿ` once `n ≥ 13`. -/
lemma eight_sq_add_le_two_pow (n : ℕ) (hn : 13 ≤ n) : 8 * n ^ 2 + n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 8 * n ^ 2 + 17 * n + 9 ≤ 16 * n ^ 2 + 2 * n := by
      nlinarith [Nat.mul_le_mul_right n hn]
    calc 8 * (n + 1) ^ 2 + (n + 1) = 8 * n ^ 2 + 17 * n + 9 := by ring
      _ ≤ 16 * n ^ 2 + 2 * n := h2
      _ = 2 * (8 * n ^ 2 + n) := by ring
      _ ≤ 2 * 2 ^ n := by linarith
      _ = 2 ^ (n + 1) := by ring

/-- `dS lam ≤ 2 ^ dG lam` for `lam ≥ 13/5`. -/
lemma dS_le_two_pow_dG (lam : ℝ) (hlam : 13/5 ≤ lam) : (dS lam : ℝ) ≤ 2 ^ (dG lam) := by
  have hg : (5:ℝ) * lam ≤ (dG lam : ℝ) := Nat.le_ceil (5 * lam)
  have hg0 : (0:ℝ) < (dG lam : ℝ) := by
    have : (0:ℝ) < 5 * lam := by linarith
    have : 0 < dG lam := Nat.ceil_pos.mpr (by linarith)
    exact_mod_cast this
  have h0 : (0:ℝ) ≤ 200 * lam ^ 2 / (dG lam : ℝ) := div_nonneg (by positivity) (le_of_lt hg0)
  have hgu : (dSp lam : ℝ) ≤ 200 * lam ^ 2 / (dG lam : ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one h0)
  have hg2 : 25 * lam ^ 2 ≤ (dG lam : ℝ) ^ 2 := by nlinarith [hg, hg0]
  have hsp : (dSp lam : ℝ) ≤ 8 * (dG lam : ℝ) + 1 := by
    have hle : 200 * lam ^ 2 / (dG lam : ℝ) ≤ 8 * (dG lam : ℝ) := by
      rw [div_le_iff₀ hg0]; nlinarith [hg2]
    linarith
  have hdS : (dS lam : ℝ) = (dG lam : ℝ) * (dSp lam : ℝ) := by rw [dS, Nat.cast_mul]
  have hg13 : 13 ≤ dG lam := by
    have h : (13:ℝ) ≤ (dG lam : ℝ) := by linarith [hg]
    exact_mod_cast h
  calc (dS lam : ℝ) = (dG lam : ℝ) * (dSp lam : ℝ) := hdS
    _ ≤ (dG lam : ℝ) * (8 * (dG lam : ℝ) + 1) := by nlinarith [hsp, le_of_lt hg0]
    _ = 8 * (dG lam : ℝ) ^ 2 + (dG lam : ℝ) := by ring
    _ ≤ (2:ℝ) ^ (dG lam) := by
        have h8 := eight_sq_add_le_two_pow (dG lam) hg13
        have hcast : ((8 * (dG lam) ^ 2 + (dG lam) : ℕ) : ℝ) ≤ ((2 ^ (dG lam) : ℕ) : ℝ) := by
          exact_mod_cast h8
        push_cast at hcast
        exact hcast

/-- All the elementary consequences of `λ ≥ 13/5` for the Ford §5 parameters
`h = ⌈λ⌉`, `g = ⌈5λ⌉`, `k = g+1`, `r' = ⌈300λ²/k⌉`, `r = k r'`, `s' = ⌈200λ²/g⌉`, `s = g s'`. -/
theorem vk_large_lam_bounds (lam : ℝ) (hlam : 13/5 ≤ lam) :
    (1 : ℝ) ≤ lam ∧ lam ≤ (dH lam : ℝ) ∧ (dH lam : ℝ) ≤ lam + 1 ∧
    (2 * lam + 1) ≤ (dG lam : ℝ) ∧ (dG lam : ℝ) ≤ 6 * lam + 1 ∧
    (dK lam : ℝ) = (dG lam : ℝ) + 1 ∧ 2 ≤ dK lam ∧ (dK lam : ℝ) ≤ 5 * lam + 2 ∧
    (5 * lam) ≤ (dG lam : ℝ) ∧ 1 ≤ dH lam ∧ dH lam ≤ dG lam ∧ dG lam ≤ dK lam ∧
    2 ≤ dR lam ∧ 1 ≤ dS lam ∧
    13 * (dG lam : ℝ) ≤ (dR lam : ℝ) ∧ (dS lam : ℝ) ≤ (2 : ℝ) ^ (dG lam) ∧
    (dS lam : ℝ) ≤ (dR lam : ℝ) ∧
    (300 * lam ^ 2 / (dK lam : ℝ) ≤ (dRp lam : ℝ)) ∧
    ((dRp lam : ℝ) ≤ 300 * lam ^ 2 / (dK lam : ℝ) + 1) ∧
    (200 * lam ^ 2 / (dG lam : ℝ) ≤ (dSp lam : ℝ)) ∧
    ((dSp lam : ℝ) ≤ 200 * lam ^ 2 / (dG lam : ℝ) + 1) ∧
    12 * 10 ^ 4 * lam ^ 4 ≤ 2 * (dR lam : ℝ) * (dS lam : ℝ) ∧
    2 * (dR lam : ℝ) * (dS lam : ℝ) ≤ 127 * 10 ^ 3 * lam ^ 4 := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam1 : (1:ℝ) ≤ lam := by linarith
  have hH2 : lam ≤ (dH lam : ℝ) := Nat.le_ceil lam
  have hH3 : (dH lam : ℝ) ≤ lam + 1 := le_of_lt (Nat.ceil_lt_add_one (le_of_lt hlam0))
  have hH4 : 1 ≤ dH lam := Nat.one_le_ceil_iff.mpr hlam0
  have hG5 : (5:ℝ) * lam ≤ (dG lam : ℝ) := Nat.le_ceil (5 * lam)
  have hG1 : (dG lam : ℝ) ≤ 5 * lam + 1 := le_of_lt (Nat.ceil_lt_add_one (by linarith))
  have hG6 : (dG lam : ℝ) ≤ 6 * lam + 1 := by linarith
  have hG21 : (2 * lam + 1) ≤ (dG lam : ℝ) := by linarith
  have hG1n : 1 ≤ dG lam := Nat.one_le_ceil_iff.mpr (by linarith : (0:ℝ) < 5 * lam)
  have hK1 : (dK lam : ℝ) = (dG lam : ℝ) + 1 := by simp [dK]
  have hK2 : 2 ≤ dK lam := by show 2 ≤ dG lam + 1; omega
  have hK5 : (dK lam : ℝ) ≤ 5 * lam + 2 := by rw [hK1]; linarith
  have hHK : dH lam ≤ dG lam := Nat.ceil_le_ceil (by linarith)
  have hGK : dG lam ≤ dK lam := Nat.le_succ _
  have hk0 : (0:ℝ) < (dK lam : ℝ) := by
    have : (0:ℝ) < (dG lam : ℝ) + 1 := by linarith [hG5, hlam]
    linarith
  have hg0 : (0:ℝ) < (dG lam : ℝ) := by
    have : (0:ℝ) < 5 * lam := by linarith
    have : 0 < dG lam := Nat.ceil_pos.mpr (by linarith)
    exact_mod_cast this
  have hRp1 : 300 * lam ^ 2 / (dK lam : ℝ) ≤ (dRp lam : ℝ) := Nat.le_ceil _
  have hRp2 : (dRp lam : ℝ) ≤ 300 * lam ^ 2 / (dK lam : ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (div_nonneg (by positivity) (le_of_lt hk0)))
  have hSp1 : 200 * lam ^ 2 / (dG lam : ℝ) ≤ (dSp lam : ℝ) := Nat.le_ceil _
  have hSp2 : (dSp lam : ℝ) ≤ 200 * lam ^ 2 / (dG lam : ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (div_nonneg (by positivity) (le_of_lt hg0)))
  have hdR_eq : (dR lam : ℝ) = (dK lam : ℝ) * (dRp lam : ℝ) := by rw [dR, Nat.cast_mul]
  have hdS_eq : (dS lam : ℝ) = (dG lam : ℝ) * (dSp lam : ℝ) := by rw [dS, Nat.cast_mul]
  have hR_low : 300 * lam ^ 2 ≤ (dR lam : ℝ) := by
    rw [hdR_eq]
    calc (300:ℝ) * lam ^ 2 = (dK lam : ℝ) * (300 * lam ^ 2 / (dK lam : ℝ)) := by
          field_simp
      _ ≤ (dK lam : ℝ) * (dRp lam : ℝ) := by nlinarith [hRp1, hk0]
  have hS_low : 200 * lam ^ 2 ≤ (dS lam : ℝ) := by
    rw [hdS_eq]
    calc (200:ℝ) * lam ^ 2 = (dG lam : ℝ) * (200 * lam ^ 2 / (dG lam : ℝ)) := by
          field_simp
      _ ≤ (dG lam : ℝ) * (dSp lam : ℝ) := by nlinarith [hSp1, hg0]
  have hR13 : 13 * (dG lam : ℝ) ≤ (dR lam : ℝ) := by
    have h : 13 * (dG lam : ℝ) ≤ 300 * lam ^ 2 := by nlinarith [hG1, hlam]
    linarith
  have hrp1 : 1 ≤ dRp lam := Nat.one_le_ceil_iff.mpr (div_pos (by positivity) hk0)
  have hsp1 : 1 ≤ dSp lam := Nat.one_le_ceil_iff.mpr (div_pos (by positivity) hg0)
  have hR2 : 2 ≤ dR lam := by
    show 2 ≤ dK lam * dRp lam
    calc 2 = 2 * 1 := by norm_num
      _ ≤ dK lam * dRp lam := Nat.mul_le_mul hK2 hrp1
  have hS2 : 1 ≤ dS lam := by
    show 1 ≤ dG lam * dSp lam
    calc 1 = 1 * 1 := by norm_num
      _ ≤ dG lam * dSp lam := Nat.mul_le_mul hG1n hsp1
  have hspRp : dSp lam ≤ dRp lam := by
    have h : 200 * lam ^ 2 / (dG lam : ℝ) ≤ (dRp lam : ℝ) := by
      have h1 : 200 * lam ^ 2 / (dG lam : ℝ) ≤ 300 * lam ^ 2 / (dK lam : ℝ) := by
        rw [div_le_div_iff₀ hg0 hk0, hK1]
        nlinarith [hG5, hlam, sq_nonneg lam]
      linarith [h1, hRp1]
    exact Nat.ceil_le.mpr h
  have hSleR : (dS lam : ℝ) ≤ (dR lam : ℝ) := by
    have h : dS lam ≤ dR lam := Nat.mul_le_mul hGK hspRp
    exact_mod_cast h
  have hR0 : (0:ℝ) ≤ (dR lam : ℝ) := by positivity
  have hS0 : (0:ℝ) ≤ (dS lam : ℝ) := by positivity
  have hprod_low : 12 * 10 ^ 4 * lam ^ 4 ≤ 2 * (dR lam : ℝ) * (dS lam : ℝ) := by
    have h := mul_le_mul hR_low hS_low (by positivity : (0:ℝ) ≤ 200 * lam ^ 2) hR0
    nlinarith [h]
  have hRup : (dR lam : ℝ) ≤ 300 * lam ^ 2 + (dK lam : ℝ) := by
    rw [hdR_eq]
    have h1 := mul_le_mul_of_nonneg_left hRp2 (le_of_lt hk0)
    have he : (dK lam : ℝ) * (300 * lam ^ 2 / (dK lam : ℝ) + 1)
        = 300 * lam ^ 2 + (dK lam : ℝ) := by field_simp
    linarith [h1, he.le]
  have hSup : (dS lam : ℝ) ≤ 200 * lam ^ 2 + (dG lam : ℝ) := by
    rw [hdS_eq]
    have h1 := mul_le_mul_of_nonneg_left hSp2 (le_of_lt hg0)
    have he : (dG lam : ℝ) * (200 * lam ^ 2 / (dG lam : ℝ) + 1)
        = 200 * lam ^ 2 + (dG lam : ℝ) := by field_simp
    linarith [h1, he.le]
  have hk_le7 : (dK lam : ℝ) ≤ 7 * lam ^ 2 := by nlinarith [hK5, hlam]
  have hg_le6 : (dG lam : ℝ) ≤ 6 * lam ^ 2 := by nlinarith [hG6, hlam]
  have hprod_up : 2 * (dR lam : ℝ) * (dS lam : ℝ) ≤ 127 * 10 ^ 3 * lam ^ 4 := by
    have hRu : (dR lam : ℝ) ≤ 307 * lam ^ 2 := by linarith [hRup, hk_le7]
    have hSu : (dS lam : ℝ) ≤ 206 * lam ^ 2 := by linarith [hSup, hg_le6]
    have h := mul_le_mul hRu hSu hS0 (by positivity : (0:ℝ) ≤ 307 * lam ^ 2)
    nlinarith only [h]
  exact ⟨hlam1, hH2, hH3, hG21, hG6, hK1, hK2, hK5, hG5, hH4, hHK, hGK, hR2, hS2,
    hR13, dS_le_two_pow_dG lam hlam, hSleR, hRp1, hRp2, hSp1, hSp2, hprod_low, hprod_up⟩

end
end Work.BMF.liouville
