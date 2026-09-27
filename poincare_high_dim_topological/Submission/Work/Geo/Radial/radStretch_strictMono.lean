import Mathlib
import Submission.Work.Geo.Radial.RadialDefs

namespace Work.Geo.Radial

/-- The one-dimensional radial stretch `t ↦ t + s (R - ε) radTent ε S t` is strictly
increasing whenever `0 < ε < R < S` and `0 ≤ s ≤ 1`.

Indeed `radStretch ε R S s t = t + s (R - ε) radTent ε S t`, the tent profile grows with
slope `1 / ε` on `[0, ε]` and decreases with slope `-1 / (S - ε)` on `[ε, S]`; the
coefficient `s (R - ε)` is at most `R - ε < S - ε`, so the total slope is positive on both
linear pieces and is `1` outside `[0, S]`. -/
theorem radStretch_strictMono {ε R S s : ℝ} (hε : 0 < ε) (hεR : ε < R) (hRS : R < S)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : StrictMono (radStretch ε R S s) := by
  have hεS : ε < S := lt_trans hεR hRS
  have hSε : 0 < S - ε := by linarith
  have hRε : 0 ≤ R - ε := by linarith
  have hA : 0 ≤ s * (R - ε) := mul_nonneg hs0 hRε
  -- the coefficient `s (R - ε) / (S - ε)` is `< 1`
  have hcoef : s * (R - ε) / (S - ε) < 1 := by
    rw [div_lt_one hSε]
    have := mul_le_of_le_one_left hRε hs1
    linarith
  intro t₁ t₂ h12
  have hD : 0 < t₂ - t₁ := by linarith
  -- the tent profile decreases at rate at most `1 / (S - ε)`
  have key : radTent ε S t₁ - radTent ε S t₂ ≤ (t₂ - t₁) / (S - ε) :=
    radTent_sub_le hε hεS h12.le
  have hAG : s * (R - ε) * (radTent ε S t₁ - radTent ε S t₂)
      ≤ s * (R - ε) * ((t₂ - t₁) / (S - ε)) :=
    mul_le_mul_of_nonneg_left key hA
  have hAD : s * (R - ε) * ((t₂ - t₁) / (S - ε)) < t₂ - t₁ := by
    have h1 : s * (R - ε) / (S - ε) * (t₂ - t₁) < 1 * (t₂ - t₁) :=
      mul_lt_mul_of_pos_right hcoef hD
    rw [one_mul] at h1
    have h2 : s * (R - ε) * ((t₂ - t₁) / (S - ε))
        = (s * (R - ε) / (S - ε)) * (t₂ - t₁) := by ring
    rw [h2]
    exact h1
  have hdiff : radStretch ε R S s t₂ - radStretch ε R S s t₁
      = (t₂ - t₁) - s * (R - ε) * (radTent ε S t₁ - radTent ε S t₂) := by
    simp only [radStretch]
    ring
  linarith

end Work.Geo.Radial
