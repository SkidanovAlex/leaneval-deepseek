/-
# The bridge between the coordinate model `s2` of `σ₂` and the challenge's `σ₂`

`Submission.s2 T` is the quadratic (coordinate) model of `σ₂` used throughout the `Savin` layer:
`∑_{i<j}(T_{ii}T_{jj} - T_{ij}²)` in the standard basis.  For a symmetric operator it agrees with
`HessianEstimates.σ₂ T` (the sum of products of the eigenvalues), which is the definition used in
the statement of the challenge theorem.  This file proves that identity, by comparing both
quantities with the coordinate minor sum in an arbitrary orthonormal basis
(`Commons.Analysis.Sigma2.sigma2_sum_eq_coord_minor_sum`).
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Operator
import Submission.Commons.Analysis.Sigma2.sigma2_sum_eq_coord_minor_sum
import Submission.Commons.Algebra.BigOperators.sum_finCongr_ite_four
import Submission.Commons.Algebra.BigOperators.sum_Iio_eq_sum_ite

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- `s2` agrees with the eigenvalue definition of `σ₂` from `ChallengeDeps`. -/
theorem s2_eq_sigma2 (T : ℝ⁴ →L[ℝ] ℝ⁴) (hT : T.IsSymmetric) :
    s2 T = HessianEstimates.σ₂ T := by
  have hfr : Module.finrank ℝ ℝ⁴ = 4 := by simp
  set b : OrthonormalBasis (Fin (Module.finrank ℝ ℝ⁴)) ℝ ℝ⁴ :=
    (EuclideanSpace.basisFun (Fin 4) ℝ).reindex (finCongr hfr).symm with hb
  have hbapp : ∀ i : Fin (Module.finrank ℝ ℝ⁴), b i = stdB4 (Fin.cast hfr i) := by
    intro i
    simp only [hb, OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    rfl
  have h2 := Commons.Analysis.Sigma2.sigma2_sum_eq_coord_minor_sum (E := ℝ⁴) hT b
  have hσ : HessianEstimates.σ₂ T = ∑ j : Fin (Module.finrank ℝ ℝ⁴),
      ∑ i : Fin (Module.finrank ℝ ℝ⁴),
        (if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) := by
    unfold HessianEstimates.σ₂
    rw [dif_pos hT]
    exact Finset.sum_congr rfl fun j _ => Commons.Algebra.BigOperators.sum_Iio_eq_sum_ite _ j
  have hb' : (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i : Fin (Module.finrank ℝ ℝ⁴),
        (if i < j then (⟪T (b i), b i⟫ * ⟪T (b j), b j⟫ - ⟪T (b i), b j⟫ ^ 2) else 0))
      = (∑ j : Fin 4, ∑ i : Fin 4,
        (if i < j then (⟪T (stdB4 i), stdB4 i⟫ * ⟪T (stdB4 j), stdB4 j⟫ - ⟪T (stdB4 i), stdB4 j⟫ ^ 2)
          else 0)) := by
    rw [← Commons.Algebra.BigOperators.sum_finCongr_ite_four hfr
      (fun i j : Fin 4 =>
        (⟪T (stdB4 i), stdB4 i⟫ * ⟪T (stdB4 j), stdB4 j⟫ - ⟪T (stdB4 i), stdB4 j⟫ ^ 2))]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hbapp i, hbapp j]
  rw [hσ, h2, hb']
  rfl

end Submission
