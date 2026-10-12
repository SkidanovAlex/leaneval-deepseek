import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB7AK.C3Q.I2_integral_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

/-- The phase `e^{−i⟪k,y⟫}` has modulus one. -/
lemma norm_chat_phase (k y : EuclideanSpace ℝ (Fin 3)) :
    ‖Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re]

/-- Multiplication by the phase `e^{−i⟪k,y⟫}` preserves integrability. -/
lemma integrable_chat_integrand {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hu : MeasureTheory.Integrable u) (k : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable
      (fun y => Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * u y) := by
  refine hu.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall (fun y => ?_))
  rw [norm_chat_phase]

/-- `Work.BoseFixR.chat` is additive in its kernel: `chat W k = (∫ y, e^{−i⟪k,y⟫}W(y)dy).re`, and the Bochner integral is linear on integrable functions. (`Work.OneBodyKin.kinFT_sub_smul` applies to the complexified kernels.) -/
theorem chat_sub {W W' : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hW' : MeasureTheory.Integrable W')
    (k : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat (fun x => W x - W' x) k
      = Work.BoseFixR.chat W k - Work.BoseFixR.chat W' k := by
  -- complexify the two kernels; integrability is preserved by `ofReal`
  have hg : MeasureTheory.Integrable (fun y => (W y : ℂ)) := hW.ofReal
  have hh : MeasureTheory.Integrable (fun y => (W' y : ℂ)) := hW'.ofReal
  -- the phase-weighted integrals are linear in the complexified kernel
  have key :
      (∫ y, Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))
            * (((fun x => W x - W' x) y : ℝ) : ℂ))
        = (∫ y, Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * (W y : ℂ))
          - (∫ y, Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * (W' y : ℂ)) := by
    rw [show (fun y => Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))
            * (((fun x => W x - W' x) y : ℝ) : ℂ))
        = (fun y => Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * (W y : ℂ)
            - (1 : ℂ)
              * (Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * (W' y : ℂ))) from by
      funext y
      push_cast
      ring]
    rw [MeasureTheory.integral_sub (integrable_chat_integrand hg k)
      ((integrable_chat_integrand hh k).const_mul (1 : ℂ)),
      MeasureTheory.integral_const_mul, one_mul]
  simp only [Work.BoseFixR.chat, Submission.BoseGases.kinFT]
  rw [key, Complex.sub_re]

end Work.BoseRowsFS
