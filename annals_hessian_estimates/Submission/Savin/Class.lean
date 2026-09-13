import Submission.Savin.Bridge
import Submission.Savin.Diag
import Submission.Commons.Analysis.Sigma2.cofactor_quad_ge_min
import Submission.Commons.Analysis.Sigma2.cofactor_quad_le_three_halves
import Submission.Commons.Analysis.Sigma2.sum_sq_eq_sigma1_sq_sub_two
import Submission.Commons.Analysis.Sigma2.sigma2_eig_add_expansion
import Submission.Commons.Algebra.BigOperators.sum_Iio_eq_sum_ite

open Metric MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- The eigen-sum form of `s2 = 1` for a symmetric operator on `ℝ⁴`. -/
theorem eigen_pairSum_eq_one {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (h1 : s2 A = 1) :
    (∑ j : Fin 4, ∑ i : Fin 4,
        if i < j then hA.eigenvalues (by simp : Module.finrank ℝ ℝ⁴ = 4) i
          * hA.eigenvalues (by simp : Module.finrank ℝ ℝ⁴ = 4) j else 0) = 1 := by
  have hn : Module.finrank ℝ ℝ⁴ = 4 := by simp
  have hgen :=
    Commons.Analysis.Sigma2.sigma2_eigen_eq_trace_invariants_gen (T := A.toLinearMap) hA hn
  have hmain : ((LinearMap.trace ℝ ℝ⁴ (A : ℝ⁴ →ₗ[ℝ] ℝ⁴) ^ 2
      - LinearMap.trace ℝ ℝ⁴ ((A : ℝ⁴ →ₗ[ℝ] ℝ⁴) ∘ₗ (A : ℝ⁴ →ₗ[ℝ] ℝ⁴))) / 2) = 1 := by
    rw [← h1, s2_eq_trace_invariants hA]
    congr 1
  rw [hmain] at hgen
  have hconv : (∑ j : Fin 4, ∑ i : Fin 4,
      (if i < j then hA.eigenvalues hn i * hA.eigenvalues hn j else 0))
      = ∑ j : Fin 4, ∑ i < j, hA.eigenvalues hn i * hA.eigenvalues hn j :=
    Finset.sum_congr rfl fun j _ =>
      (Commons.Algebra.BigOperators.sum_Iio_eq_sum_ite
        (fun i => hA.eigenvalues hn i * hA.eigenvalues hn j) j).symm
  rw [hconv, hgen]

/-- The trace is the sum of the eigenvalues. -/
theorem trOp_eq_sum_eigen {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) :
    trOp A = ∑ i : Fin 4, hA.eigenvalues (by simp : Module.finrank ℝ ℝ⁴ = 4) i := by
  have hn : Module.finrank ℝ ℝ⁴ = 4 := by simp
  have h := Commons.Analysis.Sigma2.trace_eq_sum_eigenvalues_gen (T := A.toLinearMap) hA hn
  simpa only [trOp] using h

/-- **The ellipticity class of the cofactor of a `σ₂ = 1` operator on the positive branch.**
For a symmetric `A` with `s2 A = 1` and `trOp A > 0` the cofactor `cofOp A = trOp A • 1 - A` is
positive definite, and there are explicit constants `c > 0`, `c'` with
`c ‖v‖² ≤ ⟪cofOp A v, v⟫ ≤ c' ‖v‖²`. -/
theorem cofOp_class_bounds {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (h1 : s2 A = 1)
    (htr : 0 < trOp A) :
    ∃ c c' : ℝ, 0 < c ∧
      (∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫) ∧
      (∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2) := by
  have hn : Module.finrank ℝ ℝ⁴ = 4 := by simp
  have hσ2 := eigen_pairSum_eq_one hA h1
  have htr' := trOp_eq_sum_eigen hA
  have hσ1 : 0 < ∑ i : Fin 4, hA.eigenvalues hn i := by
    rw [← htr']; exact htr
  have hcof : ((∑ i : Fin 4, hA.eigenvalues hn i) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - A) = cofOp A := by
    rw [← htr']; rfl
  have hge := Commons.Analysis.Sigma2.cofactor_quad_ge_min hA hn hσ2 hσ1
  have hle := Commons.Analysis.Sigma2.cofactor_quad_le_three_halves hA hn hσ2 hσ1
  refine ⟨(∑ i : Fin 4, hA.eigenvalues hn i) - hA.eigenvalues hn 0,
    (3 / 2) * (∑ i : Fin 4, hA.eigenvalues hn i), ?_, ?_, ?_⟩
  · have hsq := Commons.Analysis.Sigma2.sum_sq_eq_sigma1_sq_sub_two (hA.eigenvalues hn) hσ2
    have hle0 : (hA.eigenvalues hn 0) ^ 2 ≤ ∑ i : Fin 4, (hA.eigenvalues hn i) ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ 0)
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [hsq, hle0, hσ1, hcon]
  · intro v
    have h := hge v
    rwa [hcof] at h
  · intro v
    have h := hle v
    rwa [hcof] at h

end
end Submission
