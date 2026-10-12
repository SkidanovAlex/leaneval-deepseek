import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsFS.chat_sub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS.CoulBilin

/-- **Additivity of the `p`-convention Fourier transform `Work.BoseFixR.chat` in its kernel.**

`Work.BoseFixR.chat W k = (∫ y, e^{−i⟪k,y⟫}W(y) dy).re`, an integral linear in the kernel, so for
integrable real `W U`,

  `chat (fun x => W x + U x) k = chat W k + chat U k`.

(The companion `Work.BoseRowsFS.chat_sub` for the difference is already in the workspace; the
Bochner-integral linearity step is `MeasureTheory.integral_add` applied to the phase-weighted
complexified kernels, whose integrability is `integrable_chat_integrand`.) -/
theorem chat_add {W U : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hU : MeasureTheory.Integrable U)
    (k : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat (fun x => W x + U x) k
      = Work.BoseFixR.chat W k + Work.BoseFixR.chat U k := by
  -- complexify the two kernels; integrability is preserved by `ofReal`
  have hg : MeasureTheory.Integrable (fun y => (W y : ℂ)) := hW.ofReal
  have hh : MeasureTheory.Integrable (fun y => (U y : ℂ)) := hU.ofReal
  -- the phase-weighted integrals are linear in the complexified kernel
  have key :
      (∫ y, Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))
            * (((fun x => W x + U x) y : ℝ) : ℂ))
        = (∫ y, Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * (W y : ℂ))
          + (∫ y, Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * (U y : ℂ)) := by
    rw [show (fun y => Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))
            * (((fun x => W x + U x) y : ℝ) : ℂ))
        = (fun y => Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * (W y : ℂ)
            + (Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * (U y : ℂ))) from by
      funext y
      push_cast
      ring]
    rw [MeasureTheory.integral_add (integrable_chat_integrand hg k)
      (integrable_chat_integrand hh k)]
  simp only [Work.BoseFixR.chat, Submission.BoseGases.kinFT]
  rw [key, Complex.add_re]

end Work.BoseRowsFS.CoulBilin
