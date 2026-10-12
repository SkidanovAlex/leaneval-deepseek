import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.LatVec
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chat_eq_kinFT_of_even`

The corpus's cosine transform `Work.BoseFixR.chat W k = (kinFT (fun y => (W y : ℂ)) k).re`
(`p`-convention Fourier transform) agrees with the **complex** transform
`Submission.BoseGases.kinFT (fun y => (W y : ℂ)) k` whenever `W` is even: an even real weight has
a real Fourier transform.

This is the bridge needed to feed the honest weights `W₁ = wScaled ℓ (g₀ v h)` and
`W₁ω = wScaled ℓ (g₀·ω)` (both even, `Work.BoseBoxFock.kernelCompare_data`) into the `L²`
lattice-Fourier convergence `Work.BoseBoxFock.latFourier_tendsto_periodisation`, whose statement
is phrased with `kinFT` (a complex transform) while the honest row weights are `chat`-valued.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The `p`-convention transform of an **even** real weight is real, in the strong form
`kinFT W k = conj (kinFT W k)`. -/
theorem kinFT_eq_conj_of_even {W : E3 → ℝ} (hWev : ∀ z, W (-z) = W z) (k : E3) :
    Submission.BoseGases.kinFT (fun y => (W y : ℂ)) k
      = (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun y => (W y : ℂ)) k) := by
  -- substitution `y ↦ -y` turns `e^{-i⟪k,y⟫}W y` into `e^{i⟪k,y⟫}W y`
  have hsub : (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ k (-y) : ℂ))) * (W (-y) : ℂ))
      = ∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * (W y : ℂ) := by
    let e : E3 ≃ᵐ E3 := MeasurableEquiv.neg E3
    have hmp : MeasurePreserving (⇑e) (volume : Measure E3) (volume : Measure E3) := by
      simpa [e] using (Measure.measurePreserving_neg (volume : Measure E3))
    simpa [e] using (hmp.integral_comp' (f := e)
      (g := fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * (W y : ℂ)))
  calc Submission.BoseGases.kinFT (fun y => (W y : ℂ)) k
      = ∫ y : E3, Complex.exp (Complex.I * (inner ℝ k y : ℂ)) * (W y : ℂ) := by
        rw [Submission.BoseGases.kinFT, ← hsub]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only []
        rw [hWev y, inner_neg_right]
        congr 1
        push_cast
        ring
    _ = (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun y => (W y : ℂ)) k) := by
        rw [Submission.BoseGases.kinFT, ← integral_conj]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only []
        rw [map_mul, Complex.conj_ofReal]
        congr 1
        rw [← Complex.exp_conj]
        congr 1
        rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring

/-- The cosine transform `chat` of an even real weight equals the complex `p`-convention
transform `kinFT`. -/
theorem chat_eq_kinFT_of_even {W : E3 → ℝ} (hWev : ∀ z, W (-z) = W z) (k : E3) :
    ((Work.BoseFixR.chat W k : ℝ) : ℂ) = Submission.BoseGases.kinFT (fun y => (W y : ℂ)) k := by
  have hconj := kinFT_eq_conj_of_even hWev k
  have him : (Submission.BoseGases.kinFT (fun y => (W y : ℂ)) k).im = 0 := by
    have h := congrArg Complex.im hconj
    simp only [Complex.conj_im] at h
    linarith
  rw [Work.BoseFixR.chat]
  refine Complex.ext ?_ ?_
  · simp
  · simp [him]

end Work.BoseBoxFock
