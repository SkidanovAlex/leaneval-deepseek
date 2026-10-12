import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRKDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.LatSym

open MeasureTheory

/-- The pointwise conjugation of the Fourier kernel:
`conj (exp (-(I ⟪p,x⟫))) = exp (I ⟪p,x⟫)`, since `⟪p,x⟫` is real and `conj I = -I`. -/
private lemma conj_exp_neg_I_inner (p x : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))))
      = Complex.exp (Complex.I * (inner ℝ p x : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem integral_conj_mul_exp_inner {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : MeasureTheory.Integrable g)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (g x) *
        Complex.exp (Complex.I * (inner ℝ p x : ℂ)))
      = (starRingEnd ℂ) (Submission.BoseGases.kinFT g p) := by
  rw [Submission.BoseGases.kinFT, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, conj_exp_neg_I_inner p x]
  ring

end Work.BoseBoxFock.LatSym
