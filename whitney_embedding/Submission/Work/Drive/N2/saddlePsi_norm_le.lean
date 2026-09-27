import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2.saddleWindowBlock

/-!
# The norm bound for the saddle model map `Ψ = saddlePsi η δ`

`Ψ` is the level-separating map of the saddle movie: `(Ψ z)² = φ (z²)`, where
`φ (ζ) = σ (Re ζ, Im ζ) + i · Im ζ` and `σ (s, w) = s + M w · (-η - s)` with the plateau
`M = saddleM δ` taking values in `[0, 1]`.  Thus `σ (s, w)` is the convex combination
`(1 - M) · s + M · (-η)` of `s` and `-η`, so `(Re φ (z²))² ≤ η²` whenever `|Re z²| ≤ η`; and
`(Im φ (z²))² = (Im z²)² ≤ c₀²` whenever `|Im z²| ≤ c₀`.  Consequently
`‖Ψ z‖² = ‖(Ψ z)²‖ = ‖φ (z²)‖ ≤ √(η² + c₀²)`, which is the statement below.
-/

namespace Work.Drive.N2

open scoped ContDiff Topology

/-- The plateau `M` of the saddle model is nonnegative (it is a product of two `[0,1]`-valued
plateaus). -/
lemma saddleM_nonneg (δ t : ℝ) : 0 ≤ saddleM δ t := by
  rw [saddleM, saddleMu]
  exact mul_nonneg (Real.smoothTransition.nonneg _)
    (by linarith [Real.smoothTransition.le_one (|t| - 2)])

/-- The plateau `M` of the saddle model is at most one. -/
lemma saddleM_le_one (δ t : ℝ) : saddleM δ t ≤ 1 := by
  rw [saddleM, saddleMu]
  have ha : Real.smoothTransition ((|t| - (2 - 4 * δ)) / (2 * δ)) ≤ 1 :=
    Real.smoothTransition.le_one _
  have hb0 : 0 ≤ 1 - Real.smoothTransition (|t| - 2) :=
    by linarith [Real.smoothTransition.le_one (|t| - 2)]
  have hb1 : 1 - Real.smoothTransition (|t| - 2) ≤ 1 :=
    by linarith [Real.smoothTransition.nonneg (|t| - 2)]
  calc (Real.smoothTransition ((|t| - (2 - 4 * δ)) / (2 * δ))) * (1 - Real.smoothTransition (|t| - 2))
      ≤ 1 * (1 - Real.smoothTransition (|t| - 2)) := mul_le_mul_of_nonneg_right ha hb0
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb1 zero_le_one
    _ = 1 := by ring

/-- The level coordinate `σ (s, w) = s + M w · (-η - s)` is the convex combination
`(1 - M w) · s + M w · (-η)`; hence `|σ (s, w)| ≤ η` as soon as `|s| ≤ η`. -/
lemma saddleSigma_sq_le {η δ s t : ℝ} (hs : |s| ≤ η) (hm0 : 0 ≤ saddleM δ t)
    (hm1 : saddleM δ t ≤ 1) : (saddleSigma η δ (s, t)) ^ 2 ≤ η ^ 2 := by
  rw [saddleSigma_apply]
  have h1 : s ≤ η := (abs_le.mp hs).2
  have h2 : -η ≤ s := (abs_le.mp hs).1
  have hA : 0 ≤ η + s := by linarith
  have hle : s + saddleM δ t * (-η - s) ≤ η := by
    nlinarith [mul_nonneg hm0 hA]
  have hge : -η ≤ s + saddleM δ t * (-η - s) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - saddleM δ t) hA]
  nlinarith [hle, hge]

theorem saddlePsi_norm_le {η δ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ)
    (hδ' : δ < 1 / 10) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) {w : ℂ}
    (hre : |(w ^ 2).re| ≤ η) (him : |(w ^ 2).im| ≤ c₀) :
    ‖Work.Drive.N2.saddlePsi η δ w‖ ≤ Real.sqrt (Real.sqrt (η ^ 2 + c₀ ^ 2)) := by
  -- `hη`, `hη'` are not needed for the estimate and `hc₀` only to know `√(η² + c₀²) ≥ 0`;
  -- they are kept because the consumer supplies them.
  have _ := hη
  have _ := hη'
  have _ := hc₀
  have h2 : 0 ≤ 2 - 4 * δ := by linarith
  have hPsi2 : (saddlePsi η δ w) ^ 2 = saddlePhi η δ (w ^ 2) := saddlePsi_sq hδ h2 w
  -- the real part of `φ (w²)` is the level coordinate `σ`, which is bounded by `η`
  have hre' : (saddlePhi η δ (w ^ 2)).re ^ 2 ≤ η ^ 2 := by
    rw [saddlePhi_re]
    exact saddleSigma_sq_le hre (saddleM_nonneg δ (w ^ 2).im) (saddleM_le_one δ (w ^ 2).im)
  -- the imaginary part of `φ (w²)` is `Im w²`, bounded by `c₀`
  have him' : (saddlePhi η δ (w ^ 2)).im ^ 2 ≤ c₀ ^ 2 := by
    rw [saddlePhi_im]
    nlinarith [abs_le.mp him]
  have hsq : ‖saddlePhi η δ (w ^ 2)‖ ^ 2
      = (saddlePhi η δ (w ^ 2)).re ^ 2 + (saddlePhi η δ (w ^ 2)).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hPhi : ‖saddlePhi η δ (w ^ 2)‖ ≤ Real.sqrt (η ^ 2 + c₀ ^ 2) := by
    rw [Real.le_sqrt (norm_nonneg _) (by nlinarith [sq_nonneg η, sq_nonneg c₀, hc₀])]
    rw [hsq]
    linarith
  -- `‖Ψ w‖² = ‖(Ψ w)²‖ = ‖φ (w²)‖`
  have hnorm : ‖saddlePsi η δ w‖ ^ 2 = ‖saddlePhi η δ (w ^ 2)‖ := by
    rw [← hPsi2, norm_pow]
  rw [Real.le_sqrt (norm_nonneg _) (Real.sqrt_nonneg _), hnorm]
  exact hPhi

end Work.Drive.N2
