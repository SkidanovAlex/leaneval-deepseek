import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Analysis.HoleVoidCost.integralFderivNormSqLeSum`

For a `C¹` function `f` on `EuclideanSpace ℝ (Fin 3)` with compact support, the integral of the
squared operator norm of the Fréchet derivative is bounded by the integral of the sum of the
squares of the directional derivatives along the standard basis.

The pointwise statement is in fact an *equality*: a continuous linear functional `A` on a
Euclidean space is represented (Fréchet–Riesz) by a vector `y` with `A = ⟪y, ·⟫`; the operator
norm of `A` is `‖y‖`, and `‖y‖ ^ 2` is the sum of the squares of the coordinates
`y k = A (EuclideanSpace.single k 1)`.  The stated inequality then follows by congruence of
integrals; no integrability hypothesis is needed (in particular the integrability that the
hypotheses `hcd`, `hcs` would provide is not used).
-/

namespace Work.Analysis.HoleVoidCost

open MeasureTheory

/-- For a continuous linear functional `A` on `EuclideanSpace ℝ (Fin 3)`, the square of the
operator norm of `A` equals the sum of the squares of its values on the standard basis vectors
`EuclideanSpace.single k 1` — the Euclidean norm of the Riesz representative of `A`. -/
lemma opNorm_sq_eq_sum_sq (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    ‖A‖ ^ 2 = ∑ k : Fin 3, (A (EuclideanSpace.single k 1)) ^ 2 := by
  -- Fréchet–Riesz: `A = ⟪y, ·⟫` for `y := (toDual ℝ E).symm A`, and `‖A‖ = ‖y‖`.
  set y : EuclideanSpace ℝ (Fin 3) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm A with hy
  have hA : ∀ x : EuclideanSpace ℝ (Fin 3), inner ℝ y x = A x := by
    intro x
    rw [hy, InnerProductSpace.toDual_symm_apply]
  have hnorm : ‖A‖ = ‖y‖ := by
    rw [hy, LinearIsometryEquiv.norm_map]
  rw [hnorm, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : y k = A (EuclideanSpace.single k 1) := by
    rw [← hA (EuclideanSpace.single k 1)]
    simp [PiLp.inner_apply]
  rw [Real.norm_eq_abs, sq_abs, hk]

set_option linter.unusedVariables false in
theorem integralFderivNormSqLeSum (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hcd : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) :
    ∫ z : EuclideanSpace ℝ (Fin 3), ‖fderiv ℝ f z‖ ^ 2
      ≤ ∫ z : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
          ((fderiv ℝ f z) (EuclideanSpace.single k 1)) ^ 2 := by
  have h : ∀ z : EuclideanSpace ℝ (Fin 3), ‖fderiv ℝ f z‖ ^ 2
      = ∑ k : Fin 3, ((fderiv ℝ f z) (EuclideanSpace.single k 1)) ^ 2 :=
    fun z => opNorm_sq_eq_sum_sq (fderiv ℝ f z)
  exact le_of_eq (integral_congr_ae (Filter.Eventually.of_forall h))

end Work.Analysis.HoleVoidCost
