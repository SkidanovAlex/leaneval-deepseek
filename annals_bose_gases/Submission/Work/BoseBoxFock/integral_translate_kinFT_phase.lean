import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.continuous_bsOneBody
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integral_translate_kinFT_phase`

Translation covariance of the corpus's `p`-convention Fourier transform
`Submission.BoseGases.kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy`, in the phase form used by the
lattice-Poisson chapter: for every `z, p : ℝ³` and every `W : ℝ³ → ℂ`,

    ∫_x W(x + z)·e^{−i⟪p,x⟫} dx = (kinFT W p)·e^{i⟪p,z⟫} .

The statement is *unconditional* (no integrability, continuity or support hypothesis on `W`):
`kinFT_comp_add` is proved from the measure-preserving change of variables
`y ↦ y + z` together with `integral_const_mul`, both of which hold for the Bochner integral
in the degenerate, non-integrable case as well (where both sides are `0`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `kinFT` with the two factors of its integrand commuted — the corpus writes
`exp · u`, while the target writes `u · exp`. -/
private lemma integral_mul_exp_eq_kinFT (g : E3 → ℂ) (p : E3) :
    (∫ x : E3, g x * Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))))
      = Submission.BoseGases.kinFT g p := by
  rw [Submission.BoseGases.kinFT]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))

/-- **Phase form of the translation covariance of `kinFT`.** -/
theorem integral_translate_kinFT_phase {W : EuclideanSpace ℝ (Fin 3) → ℂ}
    (z p : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), W (x + z)
        * Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))))
      = Submission.BoseGases.kinFT W p
        * Complex.exp (Complex.I * (inner ℝ p z : ℂ)) := by
  have h1 : (∫ x : E3, W (x + z) * Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))))
      = Submission.BoseGases.kinFT (fun x : E3 => W (x + z)) p :=
    integral_mul_exp_eq_kinFT (fun x : E3 => W (x + z)) p
  rw [h1]
  exact (Work.BSKinetic.Decomp.kinFT_comp_add W z p).trans (mul_comm _ _)

end Work.BoseBoxFock
