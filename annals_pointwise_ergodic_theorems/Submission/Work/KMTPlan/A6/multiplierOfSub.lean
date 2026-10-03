import Mathlib
import Submission.Work.Analysis.IonescuWainger.MajorArcs

namespace Work.KMTPlan.A6

open MeasureTheory
open Work.Analysis.IonescuWainger

/-- **Linearity of the Fourier multiplier in its symbol.**  For two `L^∞` symbols `m`, `n` on the
frequency circle, `T_{m-n} = T_m - T_n`.

This is the subtraction analogue of `Work.Analysis.IonescuWainger.multiplier_add` and is proved
the same way: conjugate by the Fourier transform `𝓕_ℤ`, where the claim becomes the pointwise
identity `(m - n) • ξ = m • ξ - n • ξ` in `L²`. -/
theorem multiplier_sub (m n : Lp ℂ ⊤ circleMeasure) :
    multiplier (m - n) = multiplier m - multiplier n := by
  apply ContinuousLinearMap.ext
  intro f
  have h : fourierZ (multiplier (m - n) f) = fourierZ ((multiplier m - multiplier n) f) := by
    rw [sub_apply, map_sub, fourierZ_multiplier, fourierZ_multiplier, fourierZ_multiplier]
    rw [sub_eq_add_neg, Lp.smul_add, Lp.neg_smul, sub_eq_add_neg]
  calc multiplier (m - n) f = fourierZ.symm (fourierZ (multiplier (m - n) f)) :=
        (fourierZ.symm_apply_apply _).symm
    _ = fourierZ.symm (fourierZ ((multiplier m - multiplier n) f)) := by rw [h]
    _ = (multiplier m - multiplier n) f := fourierZ.symm_apply_apply _

theorem multiplierOfSub {f g : Work.Analysis.IonescuWainger.Circle → ℂ} (hf : MeasureTheory.MemLp f ⊤ Work.Analysis.IonescuWainger.circleMeasure) (hg : MeasureTheory.MemLp g ⊤ Work.Analysis.IonescuWainger.circleMeasure) (hfg : MeasureTheory.MemLp (f - g) ⊤ Work.Analysis.IonescuWainger.circleMeasure) : Work.Analysis.IonescuWainger.multiplierOf (f - g) hfg = Work.Analysis.IonescuWainger.multiplierOf f hf - Work.Analysis.IonescuWainger.multiplierOf g hg := by
  show multiplier (hfg.toLp (f - g)) = multiplier (hf.toLp f) - multiplier (hg.toLp g)
  rw [MemLp.toLp_sub hf hg, multiplier_sub]

end Work.KMTPlan.A6
