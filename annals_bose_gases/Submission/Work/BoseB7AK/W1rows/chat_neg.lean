import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7AK.W1rows

open MeasureTheory
open scoped ComplexConjugate

/-- For a **real-valued** function `u`, the `p`-convention Fourier transform
`kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy` satisfies `kinFT u (−p) = conj (kinFT u p)`;
consequently its real part is even: `Re Ŵ(−p) = Re Ŵ(p)`. -/
lemma kinFT_re_neg (u : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    (Submission.BoseGases.kinFT (fun y => ((u y : ℝ) : ℂ)) (-p)).re
      = (Submission.BoseGases.kinFT (fun y => ((u y : ℝ) : ℂ)) p).re := by
  rw [Submission.BoseGases.kinFT, Submission.BoseGases.kinFT]
  have h : (∫ y, Complex.exp (-(Complex.I * (inner ℝ (-p) y : ℂ))) * ((u y : ℝ) : ℂ))
      = conj (∫ y, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((u y : ℝ) : ℂ)) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with y
    have key : -(Complex.I * (inner ℝ (-p) y : ℂ))
        = conj (-(Complex.I * (inner ℝ p y : ℂ))) := by
      rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, inner_neg_left]
      push_cast
      ring
    rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, ← key]
  rw [h, Complex.conj_re]

theorem chat_neg (W : EuclideanSpace ℝ (Fin 3) → ℝ) (k : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat W (-k) = Work.BoseFixR.chat W k := by
  simpa only [Work.BoseFixR.chat] using kinFT_re_neg W k

end Work.BoseB7AK.W1rows
