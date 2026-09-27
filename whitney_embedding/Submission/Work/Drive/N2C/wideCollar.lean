import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2.saddlePsi_helpers
import Submission.Work.Drive.N2.saddleCollarRow

/-!
# The **wide collar** of the saddle model (D2 blocker of `N2Lead/NOTES_LEAD_saddlePacket.md` §0.1)

`Work.Drive.N2.saddleCollar η δ` requires `|Re z²| ≤ η`, where `η` is the *anchor displacement* of
the model (the level `-η` is the anchor level of the saddle window).  The saddle window of tier `D2`
is drawn on the **wide band** `(f p - 2η, f p + 2η)` of the theorem, whose coordinate half-width is
`ηb = 2η/lam = (4/3)·(3η/(2lam)) = 4ηs/3 > ηs = η`; points of that band have `|Re z²|` up to `ηb`,
so every row stated with `saddleCollar η δ` is **false** at the strip frontier (a frontier point
with `|Im z²| = c₀` and `|Re z²| = 1.2 η > η` is a counterexample for `hcolFr` of
`Work.Drive.N2Lead.saddleWindow_of_packet_band_off`).

This file provides the same rows with the **wide collar** `saddleCollarWide ηb δ`, i.e. with the
real-part bound `ηb`:

* `saddlePsi_collarWide` — `saddlePsi η δ z` still lands on the anchor level `-η` in the wide
  collar, and keeps the positive side of the level direction (the positivity argument only needs
  `η · ηb < 1.8²`, which `η, ηb < 1/10` gives);
* `saddlePsi_mem_collarWide`, `saddlePsi_idempotent_of_mem_collarWide` — the model maps the wide
  collar into itself and is idempotent there (**this is the row the proof of
  `saddleWindow_of_packet_band_off` needs for `hidem`**);
* `saddlePsi_sq_dependsOn_imWide`, `saddlePsi_collarEqWide` — on the wide collar the square of the
  model is a function of `Im z²`, so the model is constant along the collar trajectories (the
  instance of `Work.Drive.N2.collarConstancy_of_sq_depends_on_im` for the wide collar).

Everything is namespace `Work.Drive.N2C` so that it cannot clash with the rows of the `N2`/`N2Lead`
lanes.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

/-- The **wide collar** of the saddle model: the collar of `Work.Drive.N2.saddleCollar` with the
real-part bound `ηb` in place of the anchor displacement `η`. -/
def saddleCollarWide (ηb δ : ℝ) : Set ℂ :=
  {z | |(z ^ 2).re| ≤ ηb ∧ 2 - 2 * δ ≤ |(z ^ 2).im| ∧ |(z ^ 2).im| ≤ 2}

@[simp] lemma mem_saddleCollarWide {ηb δ : ℝ} {z : ℂ} :
    z ∈ saddleCollarWide ηb δ ↔
      |(z ^ 2).re| ≤ ηb ∧ 2 - 2 * δ ≤ |(z ^ 2).im| ∧ |(z ^ 2).im| ≤ 2 := Iff.rfl

/-- **The model on the wide collar.**  For `z` with `|Re z²| ≤ ηb` (`η ≤ ηb`, `ηb < 1/10`) and
`2 - 2δ ≤ |Im z²| ≤ 2`, the model `saddlePsi η δ` lands on the anchor level `-η` and keeps the
positive side of the level direction.  (The only change with respect to
`Work.Drive.N2.saddlePsi_collar` is the positivity of `-η·Re z² + (Im z²)²`, which needs
`η · ηb < 1.8²` instead of `η² < 1.8²`.) -/
theorem saddlePsi_collarWide {η δ ηb : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ)
    (hδ' : δ < 1 / 10) (hηb : ηb < 1 / 10) {z : ℂ} (hs : |(z ^ 2).re| ≤ ηb)
    (hw₁ : 2 - 2 * δ ≤ |(z ^ 2).im|) (hw₂ : |(z ^ 2).im| ≤ 2) :
    Work.Drive.N2.saddlePsi η δ z ^ 2 = (-η : ℂ) + ((z ^ 2).im : ℂ) * Complex.I ∧
      0 < (Work.Drive.N2.saddlePsi η δ z * (starRingEnd ℂ) z).re := by
  have h2 : (0 : ℝ) < 2 - 4 * δ := by linarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hw₁
    simp at hw₁
    linarith
  have hsigma : Work.Drive.N2.saddleSigma η δ ((z ^ 2).re, (z ^ 2).im) = -η :=
    Work.Drive.N2.saddleSigma_eq_neg_eta hδ hw₁ hw₂
  have hre : 0 < (Work.Drive.N2.saddleRatio η δ z).re := by
    rw [Work.Drive.N2.saddleRatio, if_neg hz0, Complex.div_re, Work.Drive.N2.saddlePhi_re,
      Work.Drive.N2.saddlePhi_im, hsigma, ← add_div]
    apply div_pos
    · have hs' := abs_le.mp hs
      have hηb0 : 0 ≤ ηb := le_trans (abs_nonneg ((z ^ 2).re)) hs
      have h1 : -η * ηb ≤ -η * (z ^ 2).re := by nlinarith [hs'.2, hη]
      have hδ18 : (1.8 : ℝ) ≤ 2 - 2 * δ := by linarith
      have hw18 : (1.8 : ℝ) ≤ |(z ^ 2).im| := le_trans hδ18 hw₁
      have h3 : (1.8 : ℝ) * 1.8 ≤ (z ^ 2).im * (z ^ 2).im := by
        have h4 : (1.8 : ℝ) * 1.8 ≤ |(z ^ 2).im| * |(z ^ 2).im| :=
          by nlinarith [hw18, abs_nonneg ((z ^ 2).im)]
        rwa [abs_mul_abs_self] at h4
      have h5 : η * ηb < (1.8 : ℝ) * 1.8 := by
        have h6 : η * ηb < (1 / 10 : ℝ) * (1 / 10) := by
          have hA : η * ηb ≤ η * (1 / 10) :=
            mul_le_mul_of_nonneg_left hηb.le (le_of_lt hη)
          have hB : η * (1 / 10) < (1 / 10 : ℝ) * (1 / 10) := by nlinarith [hη']
          linarith
        linarith
      linarith
    · exact Complex.normSq_pos.mpr (pow_ne_zero 2 hz0)
  have hsqrt : 0 < (Complex.sqrt (Work.Drive.N2.saddleRatio η δ z)).re := by
    rw [Complex.sqrt, Complex.cpow_inv_two_re, Real.sqrt_pos]
    linarith [hre, norm_nonneg (Work.Drive.N2.saddleRatio η δ z)]
  constructor
  · rw [Work.Drive.N2.saddlePsi_sq hδ (le_of_lt h2), Work.Drive.N2.saddlePhi, hsigma]
    simp
  · rw [Work.Drive.N2.saddlePsi]
    have hconv : z * Complex.sqrt (Work.Drive.N2.saddleRatio η δ z) * (starRingEnd ℂ) z
        = Complex.sqrt (Work.Drive.N2.saddleRatio η δ z) * ((Complex.normSq z : ℝ) : ℂ) := by
      rw [show z * Complex.sqrt (Work.Drive.N2.saddleRatio η δ z) * (starRingEnd ℂ) z
          = Complex.sqrt (Work.Drive.N2.saddleRatio η δ z) * (z * (starRingEnd ℂ) z) by ring]
      rw [Complex.mul_conj]
    rw [hconv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hnorm : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
    nlinarith [hsqrt, hnorm]

/-- The model maps the wide collar into itself (`η ≤ ηb` puts the image level `-η` inside the
real-part bound `ηb`). -/
theorem saddlePsi_mem_collarWide {η δ ηb : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ)
    (hδ' : δ < 1 / 10) (hηb : ηb < 1 / 10) (hηle : η ≤ ηb) {w : ℂ}
    (hw : w ∈ saddleCollarWide ηb δ) : Work.Drive.N2.saddlePsi η δ w ∈ saddleCollarWide ηb δ := by
  have h := (saddlePsi_collarWide hη hη' hδ hδ' hηb hw.1 hw.2.1 hw.2.2).1
  have hre : ((-η : ℂ) + (((w ^ 2).im : ℝ) : ℂ) * Complex.I).re = -η := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [h, hre, abs_neg]
    exact abs_le.mpr ⟨by linarith, hηle⟩
  · rw [h]; simpa using hw.2.1
  · rw [h]; simpa using hw.2.2

/-- **The model is idempotent on the wide collar** — the row `hseam`/`hcolFr` of
`Work.Drive.N2Lead.saddleWindow_of_packet_band_off` need through `hidem`. -/
theorem saddlePsi_idempotent_of_mem_collarWide {η δ ηb : ℝ} (hη : 0 < η) (hη' : η < 1 / 10)
    (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hηb : ηb < 1 / 10) (hηle : η ≤ ηb) {w : ℂ}
    (hw : w ∈ saddleCollarWide ηb δ) :
    Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w)
      = Work.Drive.N2.saddlePsi η δ w := by
  have hw' : Work.Drive.N2.saddlePsi η δ w ∈ saddleCollarWide ηb δ :=
    saddlePsi_mem_collarWide hη hη' hδ hδ' hηb hηle hw
  have h1 : (Work.Drive.N2.saddlePsi η δ w) ^ 2
      = -(η : ℂ) + (((w ^ 2).im : ℝ) : ℂ) * Complex.I :=
    (saddlePsi_collarWide hη hη' hδ hδ' hηb hw.1 hw.2.1 hw.2.2).1
  have h2 := saddlePsi_collarWide hη hη' hδ hδ' hηb hw'.1 hw'.2.1 hw'.2.2
  have hsq : (Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w)) ^ 2
      = (Work.Drive.N2.saddlePsi η δ w) ^ 2 := by
    rw [h2.1, h1]
    simp
  have hz0 : Work.Drive.N2.saddlePsi η δ w ≠ 0 := by
    intro h0
    have hsq0 : (Work.Drive.N2.saddlePsi η δ w) ^ 2 = 0 := by rw [h0]; ring
    rw [h1] at hsq0
    have him := congrArg Complex.im hsq0
    simp at him
    have habs : |(w ^ 2).im| = 0 := by rw [him]; simp
    have hle := hw.2.1
    rw [habs] at hle
    linarith
  have hfac : (Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w)
        - Work.Drive.N2.saddlePsi η δ w)
      * (Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w)
        + Work.Drive.N2.saddlePsi η δ w) = 0 := by
    have h' : Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w) ^ 2
        - Work.Drive.N2.saddlePsi η δ w ^ 2 = 0 := by rw [hsq]; ring
    linear_combination h'
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hneg : Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w)
        = -Work.Drive.N2.saddlePsi η δ w := eq_neg_of_add_eq_zero_left h
    rw [hneg] at h2
    have hpos := h2.2
    rw [neg_mul, Complex.neg_re] at hpos
    have hnorm : (Work.Drive.N2.saddlePsi η δ w * (starRingEnd ℂ) (Work.Drive.N2.saddlePsi η δ w)).re
        = Complex.normSq (Work.Drive.N2.saddlePsi η δ w) := by
      rw [Complex.mul_conj]
      simp
    rw [hnorm] at hpos
    have hpos' : 0 < Complex.normSq (Work.Drive.N2.saddlePsi η δ w) :=
      Complex.normSq_pos.mpr hz0
    linarith

/-- On the wide collar the square of the model is a function of `Im z²`. -/
theorem saddlePsi_sq_dependsOn_imWide {η δ ηb : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ)
    (hδ' : δ < 1 / 10) (hηb : ηb < 1 / 10) :
    ∀ z, z ∈ saddleCollarWide ηb δ →
      (Work.Drive.N2.saddlePsi η δ z) ^ 2 = -(η : ℂ) + ((z ^ 2).im : ℂ) * Complex.I :=
  fun z hz => (saddlePsi_collarWide hη hη' hδ hδ' hηb hz.1 hz.2.1 hz.2.2).1

/-- **Collar constancy of the saddle model on the wide collar**: along a continuous path in the wide
collar on which `Im z²` is constant, the model is constant. -/
theorem saddlePsi_collarEqWide {η δ ηb : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ)
    (hδ' : δ < 1 / 10) (hηb : ηb < 1 / 10) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγC : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ saddleCollarWide ηb δ)
    (him : ∀ s ∈ Icc (0 : ℝ) 1, ((γ s) ^ 2).im = ((γ 0) ^ 2).im) :
    Work.Drive.N2.saddlePsi η δ (γ 1) = Work.Drive.N2.saddlePsi η δ (γ 0) := by
  have h2 : (0 : ℝ) < 2 - 4 * δ := by linarith
  have hne : (Work.Drive.N2.saddlePsi η δ (γ 0)) ^ 2 ≠ 0 := by
    rw [saddlePsi_sq_dependsOn_imWide hη hη' hδ hδ' hηb (γ 0)
      (hγC 0 ⟨le_rfl, by norm_num⟩)]
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  exact Work.Drive.N2.collarConstancy_of_sq_depends_on_im
    (P := fun w : ℝ => -(η : ℂ) + (w : ℂ) * Complex.I) hγ hγC
    ((Work.Drive.N2.contDiff_saddlePsi η δ hδ (by linarith)).continuous.continuousOn)
    (saddlePsi_sq_dependsOn_imWide hη hη' hδ hδ' hηb) him hne

end Work.Drive.N2C
