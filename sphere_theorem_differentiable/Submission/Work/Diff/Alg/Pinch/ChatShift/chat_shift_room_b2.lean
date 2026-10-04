import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Room for the shift `Ĉ(s) → Ĉ(s+ε)` in the branch `s ≥ 1/2` (`b = b' = 1/2`)

For `s ≥ 1/2` the Brendle–Schoen family is `Ĉ(s) = ℓ_{s,1/2}(Dpic p)` with
`p = 1 - 4/(n - 2 + 8s)`.  The "shift inclusion" needs two scalar inequalities (`ChSRoom`)
controlling the coefficients

`γ₁ = chSg1 n b b' = (b - b')/(1 + (n-2)b')`  and
`γ₂ = chSg2 n a a' t σ = (t + 2σ(a-a')/n)/(1 + 2(n-1)a')`

of `linv a' b' (ℓ_{a,b} S + t • Iso n)`.  In the branch `s ≥ 1/2` both parameters `b, b'` equal
`1/2`, so `γ₁ = 0` and the two inequalities collapse to

* `0 ≤ chSg2` (the `C_EF`, `C_T`, `C_ric` terms carry the vanishing factor `|γ₁|`), and
* `chSg2 · (n-1) · (1 - P') ≥ σ (P' - P)/n`.

Both are elementary estimates.  Writing `M = n - 1`, `D = n - 2 + 8s`, `D' = n - 2 + 8(s+ε)`,
`N = 1 + 2M(s+ε)`, `t = α/(nM)`, the numerator is

`t - 2σε/n = (α - 2σεM)/(nM)`,

and the choice `ε ≤ min (1/4) (min (1/(8M)) (D/128))` gives

* `σ ≤ 1/S1 ≤ 1/2` and `εM ≤ 1/8`, hence `2σεM ≤ 1/8 ≤ α`;
* `N ≤ 2 S1` and `128ε ≤ D`, hence `64 ε N ≤ S1 D`,

so that (clearing the positive denominators `n`, `N`, `D'`, `D`)

`(α - 2σεM) D ≥ D/8 ≥ 8σεN`,

which is exactly the second inequality.  Note that the branch `b = b'` makes the three constants
`C_EF`, `C_T`, `C_ric` irrelevant; they reappear in the branch `s < 1/2`
(`chat_shift_room_b1`), where `γ₁ ≠ 0`.
-/

namespace Work.Diff.Alg.Pinch.ChatShift

open Work.Diff.Alg.Pinch

/-- In the branch `b = b' = 1/2` the `Ric₀ ∧ id`-coefficient `γ₁` vanishes. -/
private lemma chSg1_half (n : ℕ) : chSg1 n (1 / 2) (1 / 2) = 0 := by
  unfold chSg1
  norm_num

theorem chat_shift_room_b2 (n : ℕ) (hn : 2 ≤ n) (C_EF C_T C_ric : ℝ)
    (hC_EF : 0 ≤ C_EF) (hC_T : 0 ≤ C_T) (hC_ric : 0 ≤ C_ric) :
    ∀ s : ℝ, 1 / 2 ≤ s →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          ∀ α σ : ℝ, 1 / 4 ≤ α → α ≤ 1 → 0 < σ →
            σ ≤ 1 / (1 + 2 * ((n : ℝ) - 1) * s) →
            Work.Diff.Alg.Pinch.ChSRoom n C_EF C_T C_ric s (s + ε) (1 / 2) (1 / 2)
              (1 - 4 / ((n : ℝ) - 2 + 8 * s)) (1 - 4 / ((n : ℝ) - 2 + 8 * (s + ε)))
              (α / ((n : ℝ) * ((n : ℝ) - 1))) σ := by
  intro s hs
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hM1 : (1:ℝ) ≤ (n:ℝ) - 1 := by linarith
  have hM0 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hDpos : (0:ℝ) < (n:ℝ) - 2 + 8*s := by linarith
  have hS1ge : (2:ℝ) ≤ 1 + 2*((n:ℝ)-1)*s := by nlinarith [hM1, hs]
  have hS1pos : (0:ℝ) < 1 + 2*((n:ℝ)-1)*s := by linarith
  refine ⟨min (1/4) (min (1/(8*((n:ℝ)-1))) (((n:ℝ)-2+8*s)/128)), ?_, ?_, ?_⟩
  · refine lt_min (by norm_num) (lt_min ?_ ?_)
    · exact one_div_pos.mpr (by linarith)
    · exact div_pos hDpos (by norm_num)
  · exact le_trans (min_le_left _ _) (by norm_num)
  · intro ε hε hεle α σ hα1 hα2 hσ hσle
    have hεM : ε ≤ 1/(8*((n:ℝ)-1)) := le_trans hεle (le_trans (min_le_right _ _) (min_le_left _ _))
    have hεD : ε ≤ ((n:ℝ)-2+8*s)/128 := le_trans hεle (le_trans (min_le_right _ _) (min_le_right _ _))
    have hεM8 : ε * ((n:ℝ)-1) ≤ 1/8 := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < 8 * ((n:ℝ)-1))] at hεM
      nlinarith [hεM]
    have hσ2 : σ ≤ 1/2 := by
      have h := one_div_le_one_div_of_le (show (0:ℝ) < 2 by norm_num) hS1ge
      linarith [hσle, h]
    have h2σε : 2*σ*ε*((n:ℝ)-1) ≤ 1/8 := by nlinarith [hσ2, hσ.le, hεM8, hε.le]
    have h2σεα : 2*σ*ε*((n:ℝ)-1) ≤ α := by linarith [h2σε, hα1]
    have hNpos : (0:ℝ) < 1 + 2*((n:ℝ)-1)*(s+ε) := by
      have h : 0 ≤ 2*((n:ℝ)-1)*(s+ε) := by nlinarith [hM0, hε.le, hs]
      linarith
    have hNle : 1+2*((n:ℝ)-1)*(s+ε) ≤ 2*(1+2*((n:ℝ)-1)*s) := by
      have h1 : 2*((n:ℝ)-1)*ε ≤ 1/4 := by linarith [hεM8]
      nlinarith [h1, hS1ge]
    have h128 : 128*ε ≤ (n:ℝ)-2+8*s := by
      rw [le_div_iff₀ (show (0:ℝ) < 128 by norm_num)] at hεD
      linarith [hεD]
    have h64 : 64*ε*(1+2*((n:ℝ)-1)*(s+ε)) ≤ (1+2*((n:ℝ)-1)*s)*((n:ℝ)-2+8*s) := by
      nlinarith [hNle, h128, hS1ge, hε.le]
    have hD'pos : (0:ℝ) < (n:ℝ)-2+8*(s+ε) := by linarith
    -- the two inequalities, cleared of denominators
    have hmain : 8*σ*ε*(1+2*((n:ℝ)-1)*(s+ε)) ≤ ((n:ℝ)-2+8*s)*(α - 2*σ*ε*((n:ℝ)-1)) := by
      have hA : σ*(8*ε*(1+2*((n:ℝ)-1)*(s+ε))) ≤ 8*ε*(1+2*((n:ℝ)-1)*(s+ε))/(1+2*((n:ℝ)-1)*s) := by
        have h0 : 0 ≤ 8*ε*(1+2*((n:ℝ)-1)*(s+ε)) := by positivity
        calc σ*(8*ε*(1+2*((n:ℝ)-1)*(s+ε))) = (8*ε*(1+2*((n:ℝ)-1)*(s+ε)))*σ := by ring
          _ ≤ (8*ε*(1+2*((n:ℝ)-1)*(s+ε)))*(1/(1+2*((n:ℝ)-1)*s)) := mul_le_mul_of_nonneg_left hσle h0
          _ = 8*ε*(1+2*((n:ℝ)-1)*(s+ε))/(1+2*((n:ℝ)-1)*s) := by ring
      have hB : 8*ε*(1+2*((n:ℝ)-1)*(s+ε))/(1+2*((n:ℝ)-1)*s) ≤ ((n:ℝ)-2+8*s)/8 := by
        rw [div_le_div_iff₀ hS1pos (by norm_num : (0:ℝ) < 8)]
        linarith [h64]
      have hC : ((n:ℝ)-2+8*s)/8 ≤ ((n:ℝ)-2+8*s)*(α - 2*σ*ε*((n:ℝ)-1)) := by
        have h18 : (1:ℝ)/8 ≤ α - 2*σ*ε*((n:ℝ)-1) := by linarith [h2σε]
        nlinarith [h18, hDpos]
      linarith [hA, hB, hC]
    -- the first `ChSRoom` inequality: `0 ≤ chSg2`
    have hg1 : (0:ℝ) ≤ chSg2 n s (s+ε) (α/((n:ℝ)*((n:ℝ)-1))) σ := by
      have heq : chSg2 n s (s+ε) (α/((n:ℝ)*((n:ℝ)-1))) σ
          = (α - 2*σ*ε*((n:ℝ)-1))/(((n:ℝ)*((n:ℝ)-1))*(1+2*((n:ℝ)-1)*(s+ε))) := by
        unfold chSg2
        field_simp
        ring
      rw [heq]
      exact div_nonneg (by linarith [h2σεα]) (by positivity)
    -- the second `ChSRoom` inequality
    have hg2 : σ*(4/((n:ℝ)-2+8*s) - 4/((n:ℝ)-2+8*(s+ε)))/(n:ℝ)
        ≤ chSg2 n s (s+ε) (α/((n:ℝ)*((n:ℝ)-1))) σ * ((n:ℝ)-1) * (4/((n:ℝ)-2+8*(s+ε))) := by
      have hchSg2 : chSg2 n s (s+ε) (α/((n:ℝ)*((n:ℝ)-1))) σ
          = (α - 2*σ*ε*((n:ℝ)-1))/(((n:ℝ)*((n:ℝ)-1))*(1+2*((n:ℝ)-1)*(s+ε))) := by
        unfold chSg2
        field_simp
        ring
      have hP : (4:ℝ)/((n:ℝ)-2+8*s) - 4/((n:ℝ)-2+8*(s+ε))
          = 32*ε/(((n:ℝ)-2+8*s)*((n:ℝ)-2+8*(s+ε))) := by
        rw [div_sub_div _ _ (ne_of_gt hDpos) (ne_of_gt hD'pos)]
        congr 1
        ring
      have hL : (α - 2*σ*ε*((n:ℝ)-1))/(((n:ℝ)*((n:ℝ)-1))*(1+2*((n:ℝ)-1)*(s+ε))) * ((n:ℝ)-1) * (4/((n:ℝ)-2+8*(s+ε)))
          = 4*(α - 2*σ*ε*((n:ℝ)-1))/((n:ℝ)*(1+2*((n:ℝ)-1)*(s+ε))*((n:ℝ)-2+8*(s+ε))) := by
        field_simp
        try ring
      have hR : σ*(32*ε/(((n:ℝ)-2+8*s)*((n:ℝ)-2+8*(s+ε))))/(n:ℝ)
          = 32*σ*ε/(((n:ℝ)-2+8*s)*((n:ℝ)-2+8*(s+ε))*(n:ℝ)) := by
        field_simp
        try ring
      rw [hchSg2, hP, hL, hR]
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ((n:ℝ)-2+8*s)*((n:ℝ)-2+8*(s+ε))*(n:ℝ))
        (by positivity : (0:ℝ) < (n:ℝ)*(1+2*((n:ℝ)-1)*(s+ε))*((n:ℝ)-2+8*(s+ε)))]
      have h4 : (0:ℝ) ≤ 4*((n:ℝ)-2+8*(s+ε))*(n:ℝ) := by positivity
      have hmm := mul_le_mul_of_nonneg_right hmain h4
      linarith [hmm]
    unfold ChSRoom
    rw [chSg1_half]
    simp only [abs_zero, zero_mul, zero_add]
    have hre1 : (1:ℝ) - (1 - 4/((n:ℝ)-2+8*(s+ε))) = 4/((n:ℝ)-2+8*(s+ε)) := by ring
    have hre2 : (1 - 4/((n:ℝ)-2+8*(s+ε))) - (1 - 4/((n:ℝ)-2+8*s))
        = 4/((n:ℝ)-2+8*s) - 4/((n:ℝ)-2+8*(s+ε)) := by ring
    rw [hre1, hre2]
    exact ⟨hg1, hg2⟩

end Work.Diff.Alg.Pinch.ChatShift
