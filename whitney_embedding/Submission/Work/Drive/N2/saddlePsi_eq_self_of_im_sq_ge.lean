import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi

/-!
# `Ψ` is the identity outside the window of the plateau

The model map of the saddle movie is `Ψ z = z · √(φ (z²)/z²)`, where
`φ (ζ) = σ (Re ζ, Im ζ) + i · Im ζ`,  `σ (s, w) = s + M w · (-η - s)` and the plateau
`M = saddleM δ` is a product of two `smoothTransition` factors.  The *second* of those factors,
`1 - smoothTransition (|w| - 2)`, vanishes for `|w| ≥ 3`; hence `M` — and with it the displacement
`M w · (η + Re ζ)` — is `0` for `|Im ζ| ≥ 3`, so that `φ (ζ) = ζ` there and the ratio `φ (z²)/z²`
is `1`.

Consequently `Ψ` fixes every point `z` with `|Im z²| ≥ 3`; this is the row used by the saddle
journey (`saddleJourney_avoids`) at points far out in the chart, where the model must be the
identity.
-/

namespace Work.Drive.N2

/-- The plateau of the saddle model vanishes for `|w| ≥ 3`: the second factor of `saddleMu` is
`1 - smoothTransition (|w| - 2)`, which is `0` as soon as `|w| - 2 ≥ 1`. -/
lemma saddleM_eq_zero_of_three_le {δ w : ℝ} (h : 3 ≤ |w|) : saddleM δ w = 0 := by
  rw [saddleM, saddleMu, Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ |w| - 2)]
  ring

/-- The model map `Ψ` is the identity wherever `|Im z²| ≥ 3`: there the plateau vanishes, so the
level coordinate is unchanged, the ratio is `1` and the principal square root of `1` is `1`. -/
theorem saddlePsi_eq_self_of_im_sq_ge {η δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) {z : ℂ}
    (h : 3 ≤ |(z ^ 2).im|) : Work.Drive.N2.saddlePsi η δ z = z := by
  have hM : saddleM δ (z ^ 2).im = 0 := saddleM_eq_zero_of_three_le h
  have hz : z ≠ 0 := by
    rintro rfl
    simp at h
    linarith
  have hphi : saddlePhi η δ (z ^ 2) = z ^ 2 := by
    rw [saddlePhi, saddleSigma_apply, hM]
    ring_nf
    exact Complex.re_add_im (z ^ 2)
  have hr : saddleRatio η δ z = 1 := by
    rw [saddleRatio, if_neg hz, hphi, div_self (pow_ne_zero 2 hz)]
  rw [saddlePsi, hr, Complex.sqrt_one, mul_one]

end Work.Drive.N2
