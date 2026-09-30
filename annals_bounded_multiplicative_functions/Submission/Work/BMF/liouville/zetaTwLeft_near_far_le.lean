import Mathlib
import Submission.Work.BMF.liouville.zeta_tw_vk_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- Left-edge bound for the twisted Perron rectangle, where the log-derivative datum is given
separately near the real axis (`|t+u| ≤ 4`, where `ζ'/ζ` is only bounded by `C₂ + 1/‖s-1‖`)
and away from it (`3 ≤ |t+u|`, where the zero-free-region bound applies).

Route: on `|t+u| ≤ 4` the bound `C₂ + 1/‖s-1‖ ≤ (B + C₂ + 1/(1-σ₁) + 1)·(log(|t+u|+3))²`
holds because `log 3 ≥ 1` and `1/‖s-1‖ ≤ 1/(1-σ₁)`; on `3 ≤ |t+u|` it holds because
`0 ≤ B`; so `Work.BMF.liouville.norm_zetaTwLeft_le` (in
`Submission.Work.BMF.liouville.zeta_tw_vk_sum`, already verified) applies with
`B := B + C₂ + 1/(1-σ₁) + 1`. -/
lemma zetaTwLeft_near_far_le {u x T σ₁ B C₂ : ℝ}
    (hx : 1 < x) (hT : 0 < T) (hσ₁ : 0 < σ₁) (hσ₁lt : σ₁ < 1) (hB : 0 ≤ B) (hC₂ : 0 ≤ C₂)
    (hfar : ∀ t : ℝ, |t| ≤ T → 3 ≤ |t + u| →
      ‖deriv riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I)‖
        ≤ B * (Real.log (|t + u| + 3)) ^ 2)
    (hnear : ∀ t : ℝ, |t + u| ≤ 4 →
      ‖deriv riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I)‖
        ≤ C₂ + 1 / ‖((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) - 1‖) :
    ‖zetaTwLeft u x T σ₁‖ ≤
      (B + C₂ + 1 / (1 - σ₁) + 1) * (Real.log (|u| + T + 3)) ^ 2 * x ^ σ₁ *
        (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) := by
  have hσ1pos : 0 < 1 - σ₁ := by linarith
  -- `1 ≤ log 3`, since `e < 3`
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
    rwa [Real.log_exp] at h
  set B' : ℝ := B + C₂ + 1 / (1 - σ₁) + 1 with hB'def
  have hB'nonneg : 0 ≤ B' := by
    have h1 : 0 ≤ 1 / (1 - σ₁) := div_nonneg zero_le_one hσ1pos.le
    rw [hB'def]; linarith
  refine norm_zetaTwLeft_le (B := B') hx hT hσ₁ hB'nonneg ?_
  intro t ht
  -- the logarithm factor is at least `1` (hence its square too)
  have hL1 : 1 ≤ Real.log (|t + u| + 3) := by
    refine hlog3.trans (Real.log_le_log (by norm_num) ?_)
    have := abs_nonneg (t + u)
    linarith
  have hL1sq : 1 ≤ (Real.log (|t + u| + 3)) ^ 2 := by
    have hp : (0 : ℝ) < Real.log (|t + u| + 3) := lt_of_lt_of_le one_pos hL1
    nlinarith
  rcases le_or_gt (|t + u|) 4 with hle | hgt
  · -- near the real axis: use the explicit `C₂ + 1/‖s-1‖` bound
    have hn := hnear t hle
    have hsre : ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I - 1).re = σ₁ - 1 := by simp
    have hnorm_ge : 1 - σ₁ ≤ ‖(σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I - 1‖ := by
      have h := Complex.abs_re_le_norm ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I - 1)
      rw [hsre, abs_of_neg (by linarith : σ₁ - 1 < 0)] at h
      linarith
    have hkey : 1 / ‖(σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I - 1‖ ≤ 1 / (1 - σ₁) :=
      one_div_le_one_div_of_le hσ1pos hnorm_ge
    calc ‖deriv riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) /
          riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I)‖
        ≤ C₂ + 1 / ‖(σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I - 1‖ := hn
      _ ≤ C₂ + 1 / (1 - σ₁) := by linarith
      _ ≤ B' := by rw [hB'def]; linarith
      _ ≤ B' * (Real.log (|t + u| + 3)) ^ 2 := le_mul_of_one_le_right hB'nonneg hL1sq
  · -- away from the real axis: use the zero-free-region bound
    have hf := hfar t ht (by linarith)
    have hBle : B ≤ B' := by
      have h1 : 0 < 1 / (1 - σ₁) := one_div_pos.mpr hσ1pos
      rw [hB'def]; linarith
    exact hf.trans (mul_le_mul_of_nonneg_right hBle (sq_nonneg _))

end Work.BMF.liouville
