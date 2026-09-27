import Mathlib
import Submission.Work.Geo.Prism.Defs
import Submission.Work.Geo.Prism.Stretch

/-!
# The prism stretch `prismTheta`

API for `Work.Geo.Prism.prismTheta s ℓ δ`, the two-step stretch of `ℝ`

`prismTheta s ℓ δ t = str (s+ℓ) (s+2ℓ) (s+ℓ+min δ ℓ) (str s (s+min δ ℓ) (s+ℓ) t)`.

With `μ = min δ ℓ`, `ℓ ≥ 0` and `δ > 0` it is the identity outside `[s, s+ℓ+μ]`, maps
`[s, s+μ]` linearly onto `[s, s+ℓ]` and maps `[s+μ, s+ℓ+μ]` linearly onto `[s+ℓ, s+ℓ+μ]`
(`prismTheta_image_Icc`, `prismTheta_self_of_le`, `prismTheta_self_of_ge`); its inverse is
`prismThetaInv` (`prismThetaInv_prismTheta`, `prismTheta_prismThetaInv`).  The degenerate
case `ℓ = 0` gives the identity (`prismTheta_zero`).  The displacement is bounded by `2ℓ`
(`prismTheta_dist_le`).

The continuity of the *parameterised* family is deliberately not part of this file: it is
proved where it is used (`prismPushFun_continuous`), since `str` is not jointly continuous
and the argument splits on `ℓ = 0`.
-/

open Set Metric
open scoped Topology
open Classical

namespace Work.Geo.Prism

/-- For `ℓ = 0` the prism stretch is the identity (any `δ ≥ 0`). -/
theorem prismTheta_zero {s δ t : ℝ} (hδ : 0 ≤ δ) : prismTheta s 0 δ t = t := by
  unfold prismTheta
  rw [min_eq_right hδ, add_zero, mul_zero, add_zero, str_self_of_eq, str_self_of_eq]

/-- `prismTheta` fixes everything at or below `s`. -/
theorem prismTheta_self_of_le {s ℓ δ t : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ) (h : t ≤ s) :
    prismTheta s ℓ δ t = t := by
  have hμ : 0 ≤ min δ ℓ := le_min hδ hℓ
  unfold prismTheta
  rw [str_self_of_le (by linarith : s ≤ s + min δ ℓ) h,
    str_self_of_le (by linarith : s + ℓ ≤ s + 2 * ℓ) (by linarith)]

/-- `prismTheta` fixes everything at or above `s + ℓ + min δ ℓ`. -/
theorem prismTheta_self_of_ge {s ℓ δ t : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 < δ)
    (h : s + ℓ + min δ ℓ ≤ t) : prismTheta s ℓ δ t = t := by
  rcases eq_or_lt_of_le hℓ with h0 | h0
  · rw [← h0] at h ⊢
    exact prismTheta_zero (le_of_lt hδ)
  · have hμ : 0 < min δ ℓ := lt_min hδ h0
    have hin : str s (s + min δ ℓ) (s + ℓ) t = t + (ℓ - min δ ℓ) := by
      rw [str_eq_of_ge (by linarith : s < s + min δ ℓ) (by linarith : s + min δ ℓ ≤ t)]
      ring
    have hout : str (s + ℓ) (s + 2 * ℓ) (s + ℓ + min δ ℓ) (t + (ℓ - min δ ℓ)) = t := by
      rw [str_eq_of_ge (by linarith : s + ℓ < s + 2 * ℓ)
        (by linarith : s + 2 * ℓ ≤ t + (ℓ - min δ ℓ))]
      ring
    unfold prismTheta
    rw [hin, hout]

/-- The displacement of `prismTheta` is at most `2ℓ`. -/
theorem prismTheta_dist_le {s ℓ δ t : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 < δ) :
    |prismTheta s ℓ δ t - t| ≤ 2 * ℓ := by
  have hμℓ : min δ ℓ ≤ ℓ := min_le_right _ _
  have hμ0 : 0 ≤ min δ ℓ := le_min (le_of_lt hδ) hℓ
  have h1 : |str (s + ℓ) (s + 2 * ℓ) (s + ℓ + min δ ℓ) (str s (s + min δ ℓ) (s + ℓ) t)
      - str s (s + min δ ℓ) (s + ℓ) t| ≤ ℓ - min δ ℓ := by
    refine le_trans (str_dist_le _ _ _ _) ?_
    rw [show (s + ℓ + min δ ℓ) - (s + 2 * ℓ) = min δ ℓ - ℓ by ring,
      abs_of_nonpos (by linarith : min δ ℓ - ℓ ≤ 0)]
    linarith
  have h2 : |str s (s + min δ ℓ) (s + ℓ) t - t| ≤ ℓ - min δ ℓ := by
    refine le_trans (str_dist_le _ _ _ _) ?_
    rw [show (s + ℓ) - (s + min δ ℓ) = ℓ - min δ ℓ by ring,
      abs_of_nonneg (by linarith : 0 ≤ ℓ - min δ ℓ)]
  unfold prismTheta
  calc |str (s + ℓ) (s + 2 * ℓ) (s + ℓ + min δ ℓ) (str s (s + min δ ℓ) (s + ℓ) t) - t|
      ≤ |str (s + ℓ) (s + 2 * ℓ) (s + ℓ + min δ ℓ) (str s (s + min δ ℓ) (s + ℓ) t)
          - str s (s + min δ ℓ) (s + ℓ) t|
        + |str s (s + min δ ℓ) (s + ℓ) t - t| := abs_sub_le _ _ _
    _ ≤ 2 * ℓ := by linarith

/-- `prismThetaInv` is a left inverse of `prismTheta`. -/
theorem prismThetaInv_prismTheta {s ℓ δ t : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 < δ) :
    prismThetaInv s ℓ δ (prismTheta s ℓ δ t) = t := by
  rcases eq_or_lt_of_le hℓ with h0 | h0
  · rw [← h0, prismTheta_zero (le_of_lt hδ)]
    unfold prismThetaInv
    rw [min_eq_right (le_of_lt hδ), add_zero, mul_zero, add_zero, str_self_of_eq, str_self_of_eq]
  · have hμ : 0 < min δ ℓ := lt_min hδ h0
    unfold prismThetaInv prismTheta
    rw [str_inv_left (by linarith : s + ℓ < s + 2 * ℓ) (by linarith : s + ℓ < s + ℓ + min δ ℓ),
      str_inv_left (by linarith : s < s + min δ ℓ) (by linarith : s < s + ℓ)]

/-- `prismThetaInv` is a right inverse of `prismTheta`. -/
theorem prismTheta_prismThetaInv {s ℓ δ t : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 < δ) :
    prismTheta s ℓ δ (prismThetaInv s ℓ δ t) = t := by
  rcases eq_or_lt_of_le hℓ with h0 | h0
  · rw [← h0, prismTheta_zero (le_of_lt hδ)]
    unfold prismThetaInv
    rw [min_eq_right (le_of_lt hδ), add_zero, mul_zero, add_zero, str_self_of_eq, str_self_of_eq]
  · have hμ : 0 < min δ ℓ := lt_min hδ h0
    unfold prismThetaInv prismTheta
    rw [str_inv_right (by linarith : s < s + min δ ℓ) (by linarith : s < s + ℓ),
      str_inv_right (by linarith : s + ℓ < s + 2 * ℓ) (by linarith : s + ℓ < s + ℓ + min δ ℓ)]

/-- `prismTheta s ℓ δ` maps `[s, s + min δ ℓ]` onto `[s, s+ℓ]`. -/
theorem prismTheta_image_Icc {s ℓ δ : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 < δ) :
    prismTheta s ℓ δ '' Icc s (s + min δ ℓ) = Icc s (s + ℓ) := by
  rcases eq_or_lt_of_le hℓ with h0 | h0
  · rw [← h0, min_eq_right (le_of_lt hδ), add_zero]
    ext t
    simp [prismTheta_zero (le_of_lt hδ)]
  · have hμ : 0 < min δ ℓ := lt_min hδ h0
    have hμℓ : min δ ℓ ≤ ℓ := min_le_right _ _
    have hfun : ∀ t ∈ Icc s (s + min δ ℓ),
        prismTheta s ℓ δ t = str s (s + min δ ℓ) (s + ℓ) t := by
      intro t ht
      rw [mem_Icc] at ht
      have hmem : str s (s + min δ ℓ) (s + ℓ) t ∈ Icc s (s + ℓ) := by
        have h1 : str s (s + min δ ℓ) (s + ℓ) t
            ∈ str s (s + min δ ℓ) (s + ℓ) '' Icc s (s + min δ ℓ) := ⟨t, ht, rfl⟩
        rwa [str_image_Icc (by linarith) (by linarith)] at h1
      unfold prismTheta
      exact str_self_of_le (by linarith : s + ℓ ≤ s + 2 * ℓ) hmem.2
    rw [Set.image_congr hfun]
    exact str_image_Icc (by linarith) (by linarith)

/-- Every point of `[s, s+ℓ]` is the image of a point of `[s, s + min δ ℓ]`. -/
theorem exists_prismTheta_eq {s ℓ δ t : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 < δ)
    (ht : t ∈ Icc s (s + ℓ)) : ∃ t' ∈ Icc s (s + min δ ℓ), prismTheta s ℓ δ t' = t := by
  have h : t ∈ prismTheta s ℓ δ '' Icc s (s + min δ ℓ) := by
    rw [prismTheta_image_Icc hℓ hδ]; exact ht
  exact h

end Work.Geo.Prism
