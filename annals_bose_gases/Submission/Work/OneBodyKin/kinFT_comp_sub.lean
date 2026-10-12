import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `kinFT` converts right-translation into a phase factor

`kinFT u p = ∫_y e^{−i⟪p,y⟫} u(y) dy` is the `p`-convention Fourier transform of
`Submission.Work.SmallBoxBridge.Defs`.  Translating the argument of the function by a vector `a`
(left translation `u ↦ u(· − a)`) multiplies the transform by the constant phase
`e^{−i⟪p,a⟫}`:

`kinFT (fun z => g (z - a)) p = e^{−i⟪p,a⟫} · kinFT g p`.

This is the `kinFT`-version of Mathlib's `VectorFourier.fourierIntegral_comp_add_right`; the proof
is the same one-line argument: expand the inner product `⟪p, z⟫ = ⟪p, z−a⟫ + ⟪p, a⟫`, factor the
`a`-dependent phase out of the integral and use the translation invariance of Lebesgue measure
(`MeasureTheory.integral_sub_right_eq_self`).  No integrability hypothesis is needed: both sides
vanish simultaneously (the translation of an integrable function is integrable, and the
translation-invariance identity holds for arbitrary functions).
-/

namespace Work.OneBodyKin

theorem kinFT_comp_sub (g : EuclideanSpace ℝ (Fin 3) → ℂ) (a p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => g (z - a)) p
      = Complex.exp (-(Complex.I * ((inner ℝ p a : ℝ) : ℂ))) * Submission.BoseGases.kinFT g p := by
  unfold Submission.BoseGases.kinFT
  -- pointwise: pull the constant phase `e^{−i⟪p,a⟫}` out of the integrand
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * g (z - a)
        = Complex.exp (-(Complex.I * ((inner ℝ p a : ℝ) : ℂ))) *
          (Complex.exp (-(Complex.I * (inner ℝ p (z - a) : ℂ))) * g (z - a)) := by
    intro z
    have hinner : (inner ℝ p z : ℂ)
        = ((inner ℝ p a : ℝ) : ℂ) + ((inner ℝ p (z - a) : ℝ) : ℂ) := by
      have h : inner ℝ p z = inner ℝ p (z - a) + inner ℝ p a := by
        rw [← inner_add_right, sub_add_cancel]
      rw [h, Complex.ofReal_add, add_comm]
    have hexp : Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        = Complex.exp (-(Complex.I * ((inner ℝ p a : ℝ) : ℂ))) *
          Complex.exp (-(Complex.I * ((inner ℝ p (z - a) : ℝ) : ℂ))) := by
      rw [hinner, mul_add, neg_add, Complex.exp_add]
    rw [hexp, mul_assoc]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self
      (fun y : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * g y) a]

end Work.OneBodyKin
