import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.ShiftDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic.Decomp

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

set_option autoImplicit false

/-!
# Continuity of the `p`-space transform `bsPsi`

For a smooth, compactly supported `h`, the `p`-convention Fourier transform
`bsPsi h p = ∫_y e^{−i⟪p,y⟫} h(y) dy` is continuous in `p`.  This is the dominated-convergence
statement for the parameter integral: the phase has modulus one, so `‖h‖` is an integrable
dominator, and for each `y` the phase `p ↦ e^{−i⟪p,y⟫}` is continuous.
-/

/-- The modulus-one phase factor `e^{−i⟪p,y⟫}`. -/
lemma norm_exp_neg_I_inner (p y : ℝ³) :
    ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

theorem continuous_bsPsi {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hd : ContDiff ℝ (⊤ : ENat) h) (hc : HasCompactSupport h) :
    Continuous (fun p : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.Decomp.bsPsi h p) := by
  have hint : Integrable (fun y : ℝ³ => (h y : ℂ)) :=
    (Complex.continuous_ofReal.comp hd.continuous).integrable_of_hasCompactSupport
      (hc.comp_left (by simp : ((0 : ℝ) : ℂ) = 0))
  show Continuous (fun p : ℝ³ =>
    ∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (h y : ℂ))
  refine continuous_of_dominated
    (F := fun (p y : ℝ³) => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (h y : ℂ))
    (bound := fun y : ℝ³ => ‖h y‖) ?_ ?_ ?_ ?_
  · intro p
    exact (by fun_prop : Continuous fun y : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (h y : ℂ)).aestronglyMeasurable
  · intro p
    filter_upwards with y
    rw [norm_mul, norm_exp_neg_I_inner p y, one_mul]
    simp
  · simpa using hint.norm
  · filter_upwards with y
    fun_prop

end Work.BSKinetic.Decomp
