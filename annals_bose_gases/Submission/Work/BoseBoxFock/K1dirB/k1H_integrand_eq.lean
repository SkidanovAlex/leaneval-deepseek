import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.K1dirBDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB.k1H_integrand_eq` — the pointwise `χχ`-row factorisation

The `χχ`-weighted test kernel `k1H ℓ G w y = ℓ⁻³ χ(w) χ(y) G w y` is, as a function of `w`, the
complex multiple `ℓ⁻³ χ(y)` of the function `w ↦ χ(w) G w y`.  Consequently the Dirichlet integrand
of the `χχ`-row factorises:

    Σ_j ‖∂_j (k1H ℓ G · y)(w)‖² = (ℓ³)⁻² · χ_ℓ(y)² · Σ_j ‖∂_j (χ_ℓ(·) G · y)(w)‖² .

This is the pointwise identity behind `dirichlet_k1H_le`: it reduces the Dirichlet energy of the
`ℓ⁻³ χχ G` kernel to the Dirichlet energy of the *unweighted* kernel `χ G`, with the weight carried
by the single factor `(ℓ³)⁻² χ_ℓ(y)²`, which integrates to `ℓ⁻⁶ · ∫χ² ≤ ℓ⁻⁶ · k1Chi`.

Nothing here uses smoothness: the `fderiv` of a constant complex multiple of an arbitrary function
is the multiple of the `fderiv`, because multiplication by a fixed complex constant is `ℝ`-linear
(`fderiv_const_smul_field` needs no differentiability hypothesis: the scalar `ℂ` is a
`DivisionSemiring`).  The hypotheses `0 < ℓ` and `hG` are kept because the statement is the
interface the requester fixed.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

set_option linter.unusedVariables false

namespace Work.BoseBoxFock.K1dirB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The squared norm of a real number seen as a complex number. -/
theorem k1HIntegrand_norm_sq_ofReal (x : ℝ) : ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The squared norm of the complexified window `χ_ℓ`. -/
theorem k1HIntegrand_norm_sq_chiB (ℓ : ℝ) (y : E3) :
    ‖chiB ℓ y‖ ^ 2 = (Submission.BoseGases.chiScale ℓ y) ^ 2 := by
  simp [chiB]

/-- `fderiv` of a constant complex multiple of a function: no differentiability hypothesis is
needed, complex scalars forming a division semiring. -/
theorem k1HIntegrand_fderiv_const_mul (A : ℂ) (F : E3 → ℂ) (w : E3) :
    fderiv ℝ (fun w' => A * F w') w = A • fderiv ℝ F w := by
  have h : (fun w' => A * F w') = A • F := by
    funext w'; simp [Pi.smul_apply, smul_eq_mul]
  rw [h, fderiv_const_smul_field]
  rfl

/-- The Dirichlet integrand of a constant complex multiple of a function is the constant
`‖A‖²` times the Dirichlet integrand of the function. -/
theorem k1HIntegrand_sum_norm_sq_fderiv_const_mul (A : ℂ) (F : E3 → ℂ) (w : E3) :
    (∑ j : Fin 3, ‖(fderiv ℝ (fun w' => A * F w') w) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = ‖A‖ ^ 2
        * (∑ j : Fin 3, ‖(fderiv ℝ F w) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
  simp only [k1HIntegrand_fderiv_const_mul, smul_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, norm_mul, mul_pow]

theorem k1H_integrand_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (w y : EuclideanSpace ℝ (Fin 3)) :
    (∑ j : Fin 3, ‖fderiv ℝ (fun w' => Work.BoseBoxFock.K1dirB.k1H ℓ G w' y) w
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = ((ℓ ^ 3)⁻¹) ^ 2 * (Submission.BoseGases.chiScale ℓ y) ^ 2 *
        (∑ j : Fin 3, ‖fderiv ℝ (fun w' => Work.BoseBoxFock.K1dirB.chiB ℓ w' * G w' y) w
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
  -- as a function of `w`, the `χχ`-kernel is the *constant* `ℓ⁻³ χ(y)` times `χ(w) G w y`
  have hfun : (fun w' => k1H ℓ G w' y)
      = fun w' => ((((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * chiB ℓ y) * (chiB ℓ w' * G w' y) := by
    funext w'
    simp only [k1H]
    ring
  rw [hfun, k1HIntegrand_sum_norm_sq_fderiv_const_mul]
  rw [norm_mul, mul_pow, k1HIntegrand_norm_sq_ofReal, k1HIntegrand_norm_sq_chiB]

end Work.BoseBoxFock.K1dirB
