import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Work.KMTAreas.A7.FourierDecayExplicit

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped FourierTransform

/-- **`cw m j` is the Fourier transform of `m` at the integer frequency `j`.**

The two normalisations agree because `e(-jθ) = fourierChar (-(θ • j))` and `ee` is Mathlib's
`e^{2πi·}`.  This is the bridge that turns the decay theory of `𝓕` into the decay of the
`cw`-coefficients. -/
lemma cw_eq_fourierTransform (m : ℝ → ℂ) (j : ℤ) :
    cw m j = FourierTransform.fourier m (j : ℝ) := by
  rw [cw, Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  show m θ * ee (-(j : ℝ) * θ) = Real.fourierChar (-inner ℝ θ (j : ℝ)) • m θ
  have hinner : inner ℝ θ (j : ℝ) = θ * (j : ℝ) := by rw [RCLike.inner_apply]; simp [mul_comm]
  rw [hinner, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, ee]
  rw [mul_comm (m θ)]
  congr 1
  push_cast
  ring_nf

/-- **Quadratic decay of the Fourier coefficients `cw η_{≤c}` of the rescaled KMT cutoff.**

`η_{≤c} = etaCut kmtEta c` is `C²` with compact support (`contDiff_etaCut`,
`hasCompactSupport_etaCut`), so its Fourier transform decays like `|x|^{-2}`
(`FourierDecayExplicit`); the `+1` in the denominator makes the bound uniform near the origin,
where the trivial `L¹` bound controls it.  The constant is explicit and positive. -/
theorem cw_etaCut_decay (c : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℤ,
      ‖Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c) j‖
        ≤ C / (1 + |(j : ℝ)|)^2 := by
  set A := ∫ y : ℝ, ‖Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c y‖ with hA
  set B := ∫ y : ℝ,
    ‖iteratedDeriv 2 (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c) y‖ with hB
  refine ⟨4 * max A B + 1, ?_, ?_⟩
  · have hA0 : 0 ≤ A := by
      rw [hA]; exact integral_nonneg (fun y => norm_nonneg _)
    have hm : 0 ≤ max A B := le_max_of_le_left hA0
    linarith
  · intro j
    rw [cw_eq_fourierTransform]
    exact FourierDecayExplicit (g := Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c)
      ((contDiff_etaCut c).of_le (WithTop.coe_le_coe.mpr le_top))
      (hasCompactSupport_etaCut c) (j : ℝ)

end Work.KMTAreas.A7
