import Mathlib
import Submission.Work.Drive.Generic.HeightDefs

namespace Work.Drive.Generic

/-- A continuous linear functional on `ℝ × ℝ` vanishes iff it vanishes on the two standard
basis vectors `(1,0)` and `(0,1)`. -/
private lemma clm_eq_zero_iff_apply_pair (L : (ℝ × ℝ) →L[ℝ] ℝ) :
    L = 0 ↔ L (1, 0) = 0 ∧ L (0, 1) = 0 := by
  constructor
  · intro h
    rw [h]
    simp
  · rintro ⟨h1, h2⟩
    apply ContinuousLinearMap.ext
    intro w
    have hw : w = w.1 • ((1 : ℝ), 0) + w.2 • ((0 : ℝ), 1) := by ext <;> simp
    rw [hw, map_add, map_smul, map_smul, h1, h2, smul_zero, smul_zero, add_zero, zero_apply]

/-- The differential of the height function `q ↦ ⟪v, Φ q⟫` in the direction `w` is `⟪v, dΦ_p w⟫`. -/
private lemma fderiv_height_apply {Φ : ℝ × ℝ → E3} (hΦ : ContDiff ℝ 3 Φ)
    (v : E3) (p w : ℝ × ℝ) :
    fderiv ℝ (fun q => inner ℝ v (Φ q)) p w = inner ℝ v (fderiv ℝ Φ p w) := by
  have hΦd : DifferentiableAt ℝ Φ p := (hΦ.differentiable (by norm_num)).differentiableAt
  have h := fderiv_inner_apply (𝕜 := ℝ) (f := fun _ : ℝ × ℝ => v) (g := Φ)
    (x := p) (differentiableAt_const v) hΦd w
  simpa using h

/-- The height function `q ↦ ⟪v, Φ q⟫` has a critical point at `p` exactly when `v` is orthogonal
to the two partial derivative vectors `d1 Φ p` and `d2 Φ p` of `Φ` at `p`. -/
theorem fderiv_height_eq_zero_iff {Φ : ℝ × ℝ → Work.Drive.Generic.E3} (hΦ : ContDiff ℝ 3 Φ)
    (v : Work.Drive.Generic.E3) (p : ℝ × ℝ) :
    fderiv ℝ (fun q => inner ℝ v (Φ q)) p = 0 ↔
      inner ℝ v (Work.Drive.Generic.d1 Φ p) = 0 ∧
        inner ℝ v (Work.Drive.Generic.d2 Φ p) = 0 := by
  have hfd := fderiv_height_apply hΦ v p
  rw [clm_eq_zero_iff_apply_pair]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [hfd] at h1; simpa [d1] using h1,
           by rw [hfd] at h2; simpa [d2] using h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [hfd]; simpa [d1] using h1
    · rw [hfd]; simpa [d2] using h2

end Work.Drive.Generic
