import Mathlib
import Submission.Work.Analysis.IonescuWainger.MajorArcs

namespace Work.Analysis.IonescuWainger

open MeasureTheory

theorem multiplier_add (m m' : MeasureTheory.Lp ℂ ⊤ circleMeasure) :
    multiplier (m + m') = multiplier m + multiplier m' := by
  -- The Fourier transform `𝓕_ℤ` is an isometric isomorphism, so it suffices to check the
  -- two operators after conjugation by `𝓕_ℤ`, where both act as multiplication by the
  -- symbol (`fourierZ_multiplier`).  There the claim is the pointwise `add_smul`.
  apply ContinuousLinearMap.ext
  intro f
  have h : fourierZ (multiplier (m + m') f)
      = fourierZ ((multiplier m + multiplier m') f) := by
    rw [fourierZ_multiplier, add_apply, map_add, fourierZ_multiplier, fourierZ_multiplier]
    exact Lp.smul_add m m' (fourierZ f)
  calc multiplier (m + m') f
      = fourierZ.symm (fourierZ (multiplier (m + m') f)) :=
        (fourierZ.symm_apply_apply _).symm
    _ = fourierZ.symm (fourierZ ((multiplier m + multiplier m') f)) := by rw [h]
    _ = (multiplier m + multiplier m') f := fourierZ.symm_apply_apply _

end Work.Analysis.IonescuWainger
