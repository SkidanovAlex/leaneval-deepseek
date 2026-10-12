import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Submission.Work.BoseKinLoc.Momentum.cubFT_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Momentum

open scoped BigOperators

/-- **Cauchy–Schwarz in the standard basis of `ℝ³`.** For any linear functional
`T = fderiv ℝ f z` and any `v`, the square of `T v` is bounded by `‖v‖²` times the sum of the
squares of the three coordinate evaluations `T (kcStdBasis i)`.

The proof expands `v = ∑ i, (v i) • kcStdBasis i` in the standard orthonormal basis
(`EuclideanSpace.basisFun (Fin 3) ℝ`), applies `T` termwise
(`T v = ∑ i, (v i) * T (kcStdBasis i)`), rewrites `‖v‖² = ∑ i, (v i)²`, and concludes with the
finite Cauchy–Schwarz inequality `Finset.sum_mul_sq_le_sq_mul_sq`. -/
theorem fderiv_basis_sq_le (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (z v : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ f z v) ^ 2 ≤
      ‖v‖ ^ 2 * ∑ i : Fin 3, (fderiv ℝ f z (Submission.BoseGases.kcStdBasis i)) ^ 2 := by
  set T : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := fderiv ℝ f z with hT
  set b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
    EuclideanSpace.basisFun (Fin 3) ℝ with hb
  -- the standard orthonormal basis vectors are `kcStdBasis`
  have hb_apply : ∀ i, b i = Submission.BoseGases.kcStdBasis i := by
    intro i; rw [hb, EuclideanSpace.basisFun_apply]; rfl
  -- and the coordinates in that basis are the coordinates of `v`
  have hrepr : ∀ i, (b.repr v).ofLp i = v i := by
    intro i; rw [hb]; exact EuclideanSpace.basisFun_repr (Fin 3) ℝ v i
  -- `T v` expanded in the standard basis
  have hTv : T v = ∑ i : Fin 3, v i * T (Submission.BoseGases.kcStdBasis i) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, smul_eq_mul, hrepr, hb_apply]
  -- `‖v‖²` is the sum of squares of the coordinates
  have hnorm : ‖v‖ ^ 2 = ∑ i : Fin 3, (v i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  rw [hTv, hnorm]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin 3 => v i) (fun i : Fin 3 => T (Submission.BoseGases.kcStdBasis i))

end Work.BoseKinLoc.Momentum
