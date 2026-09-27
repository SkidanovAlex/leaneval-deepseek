import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2Lead.modelArc_im_strictMonoOn
import Submission.Work.Drive.N2Lead.mobiusGeomDefs

/-!
# The model arc avoids the two rays of the upper certificate's `hhit` row

`Work.Drive.N2Lead.isCertifiedAt_of_starRegions` asks, for each region with centre `o` and a direction
`e ≠ 0`, that the ray `{o + s • e : s > 0}` meet the level's picture at most once.  For the two
regions `Ω_R = {Re > 0} ∩ ball 0 5` (centre `1`) and `Ω_L` (centre `-1`) of the upper certificate
(`NOTES_LEAD_saddlePacket.md` §4.3), the *model* and *remnant* parts of the upper level's picture are
the points `± √(σ(s,w) + i w)` with `s = ±ηs`; both never meet the rays `(1, ∞)` and `(-∞, -1)`:
the only real points of the arc are at `w = 0`, where the value is `±√s` with `s ≤ ηs < 1`, i.e. of
modulus `< 1`.  Hence for `hhit` only the *bridge* part of the picture contributes (see
`Work.Drive.N2Lead.polarBridgeRate` for its rate).
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology

/-- The real points of the model arc: if `√(σ(s,w) + i w)` is real then `w = 0` and the value is
`±√s`. -/
lemma mobiusRho_eq_ofReal_of_im_eq_zero {η δ s w : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    {t : ℝ} (h : mobiusRho η δ s w = (t : ℂ)) : t ^ 2 = s := by
  have hsq : (mobiusRho η δ s w) ^ 2
      = ((Work.Drive.N2.saddleSigma η δ (s, w) : ℝ) : ℂ) + (w : ℂ) * Complex.I := by
    rw [mobiusRho, Work.Drive.N2.saddleSigma]
    exact Work.Drive.N2.complex_sqrt_sq _
  have h1 : ((Work.Drive.N2.saddleSigma η δ (s, w) : ℝ) : ℂ) + (w : ℂ) * Complex.I
      = ((t ^ 2 : ℝ) : ℂ) := by
    rw [← hsq, h]
    push_cast
    ring
  have him : w = 0 := by
    have h2 : w = (((t ^ 2 : ℝ)) : ℂ).im := by
      have := congrArg Complex.im h1
      simpa using this
    simpa only [Complex.ofReal_im] using h2
  have hre : Work.Drive.N2.saddleSigma η δ (s, w) = t ^ 2 := by
    have h2 : Work.Drive.N2.saddleSigma η δ (s, w) = (((t ^ 2 : ℝ)) : ℂ).re := by
      have := congrArg Complex.re h1
      simpa using this
    simpa only [Complex.ofReal_re] using h2
  have hσ0 : Work.Drive.N2.saddleM δ 0 = 0 := saddleM_zero_of_lt_half hδ hδ'
  rw [Work.Drive.N2.saddleSigma_apply, him, hσ0] at hre
  simp only [zero_mul, add_zero] at hre
  rw [← hre]

/-- **The model arc never meets the ray `(1, ∞)`.** -/
theorem modelArc_not_mem_ray {η δ s w : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) (hs : s ≤ η)
    (hη : η < 1) : ¬ ∃ σ : ℝ, 0 < σ ∧ mobiusRho η δ s w = ((1 + σ : ℝ) : ℂ) := by
  rintro ⟨σ, hσ, h⟩
  have := mobiusRho_eq_ofReal_of_im_eq_zero hδ hδ' h
  nlinarith [hσ, hs, hη]

/-- **The model arc never meets the ray `(-∞, -1)`.** -/
theorem modelArc_not_mem_ray_neg {η δ s w : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) (hs : s ≤ η)
    (hη : η < 1) : ¬ ∃ σ : ℝ, 0 < σ ∧ mobiusRho η δ s w = -(((1 + σ : ℝ)) : ℂ) := by
  rintro ⟨σ, hσ, h⟩
  have h' : mobiusRho η δ s w = ((-(1 + σ) : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  have := mobiusRho_eq_ofReal_of_im_eq_zero hδ hδ' h'
  nlinarith [hσ, hs, hη]

end Work.Drive.N2Lead
