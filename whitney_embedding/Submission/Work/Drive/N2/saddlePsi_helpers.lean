import Mathlib
import Submission.Work.Drive.N2.saddleCollarFoot

/-!
# Small structural lemmas about the saddle model `saddlePsi`

These are the elementary rows used by the *anchor picture* of the saddle window
(`Submission/Work/Drive/N2/anchorPictureBlend.lean`):

* on the anchor level `Re (·)² = -η` the model fixes its argument (`saddlePsi_sq_eq_self_of_re_eq_neg_eta`),
* the model maps the collar into itself (`saddlePsi_mem_collar`),
* consequently it is **idempotent** on the collar (`saddlePsi_idempotent_of_mem_collar`), which is what
  turns `Z (foot x) = saddlePsi η δ (Z x)` into the collar pinning
  `A₀ (foot x) = cE3 (saddlePsi η δ (Z x))` for a picture `A₀` defined by the model.
-/

namespace Work.Drive.N2

open scoped ContDiff

/-- On the level `Re ζ = -η` of the collar (the anchor level of the saddle window) the model `φ`
fixes `ζ`: the displacement `M (Im ζ) · (η + Re ζ)` vanishes. -/
lemma saddlePhi_eq_self_of_re_eq_neg_eta {η δ : ℝ} {ζ : ℂ} (hζ : ζ.re = -η) :
    saddlePhi η δ ζ = ζ := by
  rw [saddlePhi_eq_sub, hζ]
  simp

/-- Hence `saddlePsi` fixes its argument up to sign on that level: `(Ψ ζ)² = ζ²`. -/
theorem saddlePsi_sq_eq_self_of_re_eq_neg_eta {η δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2)
    {z : ℂ} (hre : ((z ^ 2).re) = -η) :
    (saddlePsi η δ z) ^ 2 = z ^ 2 := by
  have h2 : (0:ℝ) ≤ 2 - 4 * δ := by linarith
  rw [saddlePsi_sq hδ h2, saddlePhi_eq_self_of_re_eq_neg_eta hre]

/-- The model maps the collar into itself. -/
theorem saddlePsi_mem_collar {η δ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ)
    (hδ' : δ < 1 / 10) {w : ℂ} (hw : w ∈ saddleCollar η δ) :
    saddlePsi η δ w ∈ saddleCollar η δ := by
  have h := (saddlePsi_collar hη hη' hδ hδ' hw.1 hw.2.1 hw.2.2).1
  refine ⟨?_, ?_, ?_⟩
  · rw [h]
    simpa [abs_of_nonneg hη.le] using le_refl η
  · rw [h]; simpa using hw.2.1
  · rw [h]; simpa using hw.2.2

/-- **The model is idempotent on the collar.**  This is the row that makes the collar pinning of the
anchor picture well posed: the picture of the anchor level defined by the model at the feet of the
collar points takes there the value that the collage prescribes. -/
theorem saddlePsi_idempotent_of_mem_collar {η δ : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ)
    (hδ' : δ < 1 / 10) {w : ℂ} (hw : w ∈ saddleCollar η δ) :
    saddlePsi η δ (saddlePsi η δ w) = saddlePsi η δ w := by
  have hw' : saddlePsi η δ w ∈ saddleCollar η δ := saddlePsi_mem_collar hη hη' hδ hδ' hw
  have h1 : (saddlePsi η δ w) ^ 2 = -(η : ℂ) + (((w ^ 2).im : ℝ) : ℂ) * Complex.I :=
    (saddlePsi_collar hη hη' hδ hδ' hw.1 hw.2.1 hw.2.2).1
  have h2 := saddlePsi_collar hη hη' hδ hδ' hw'.1 hw'.2.1 hw'.2.2
  have hsq : (saddlePsi η δ (saddlePsi η δ w)) ^ 2 = (saddlePsi η δ w) ^ 2 := by
    rw [h2.1, h1]
    simp
  have hz0 : saddlePsi η δ w ≠ 0 := by
    intro h0
    have hsq0 : (saddlePsi η δ w) ^ 2 = 0 := by rw [h0]; ring
    rw [h1] at hsq0
    have him := congrArg Complex.im hsq0
    simp at him
    have habs : |(w ^ 2).im| = 0 := by rw [him]; simp
    have hle := hw.2.1
    rw [habs] at hle
    linarith
  have hfac : (saddlePsi η δ (saddlePsi η δ w) - saddlePsi η δ w) *
      (saddlePsi η δ (saddlePsi η δ w) + saddlePsi η δ w) = 0 := by
    have h' : saddlePsi η δ (saddlePsi η δ w) ^ 2 - saddlePsi η δ w ^ 2 = 0 := by
      rw [hsq]; ring
    linear_combination h'
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hneg : saddlePsi η δ (saddlePsi η δ w) = -saddlePsi η δ w :=
      eq_neg_of_add_eq_zero_left h
    rw [hneg] at h2
    have hpos := h2.2
    rw [neg_mul, Complex.neg_re] at hpos
    have hnorm : (saddlePsi η δ w * (starRingEnd ℂ) (saddlePsi η δ w)).re
        = Complex.normSq (saddlePsi η δ w) := by
      rw [Complex.mul_conj]
      simp
    rw [hnorm] at hpos
    have hpos' : 0 < Complex.normSq (saddlePsi η δ w) := Complex.normSq_pos.mpr hz0
    linarith

end Work.Drive.N2
