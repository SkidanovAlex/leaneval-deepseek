import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `kinFT` is complex-linear in its argument

`kinFT u p = ∫_y e^{−i⟪p,y⟫} u(y) dy` is the `p`-convention Fourier transform of
`Submission.Work.SmallBoxBridge.Defs`.  As a plain Bochner integral with a bounded
(the modulus-one) kernel `e^{−i⟪p,y⟫}`, it is complex-linear on the integrable functions:

`kinFT (g − c • h) p = kinFT g p − c · kinFT h p`.

The proof is the pointwise identity `e^{−i⟪p,y⟫}(g(y) − c·h(y))
= e^{−i⟪p,y⟫}g(y) − c·(e^{−i⟪p,y⟫}h(y))` followed by `integral_sub` /
`integral_const_mul`; the integrability hypotheses are exactly what is needed for
those two lemmas, the kernel factors being integrable-multipliers by
`Integrable.bdd_mul` (`‖e^{−i⟪p,y⟫}‖ = 1`).
-/

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

/-- The phase `e^{−i⟪p,y⟫}` has modulus one. -/
lemma norm_kinFT_phase (p y : ℝ³) :
    ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re]

/-- Multiplication by the phase `e^{−i⟪p,y⟫}` preserves integrability. -/
lemma integrable_kinFT_integrand {u : ℝ³ → ℂ} (hu : MeasureTheory.Integrable u) (p : ℝ³) :
    MeasureTheory.Integrable (fun y => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * u y) := by
  refine hu.bdd_mul (c := 1) (Continuous.aestronglyMeasurable ?_)
    (Filter.Eventually.of_forall (fun y => ?_))
  · fun_prop
  · rw [norm_kinFT_phase]

theorem kinFT_sub_smul {g h : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : MeasureTheory.Integrable g) (hh : MeasureTheory.Integrable h) (c : ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (g - c • h) p
      = Submission.BoseGases.kinFT g p - c * Submission.BoseGases.kinFT h p := by
  unfold Submission.BoseGases.kinFT
  rw [show (fun y => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g - c • h) y)
      = (fun y => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * g y
          - c * (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * h y)) from
    funext (fun y => by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]; ring)]
  rw [MeasureTheory.integral_sub (integrable_kinFT_integrand hg p)
    ((integrable_kinFT_integrand hh p).const_mul c)]
  rw [MeasureTheory.integral_const_mul]

end Work.OneBodyKin
