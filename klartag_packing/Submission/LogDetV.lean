import Mathlib
import Submission.MatSpace
import Submission.MatBridge
import Submission.Rescale
import Submission.LogDet

/-!
# The log-determinant bound in the `MatV` model

`Submission.LogDet.log_det_add_smul_one_le` is the global second-order Taylor bound for
`log det` in the matrix world.  This file transports it to `MatV d = EuclideanSpace ℝ (Fin d ×
Fin d)`, and converts the hypothesis about eigenvalues into the hypothesis actually available in
the exploration process: a bound on the quadratic form of `A - a₀·Id` on the unit sphere.
-/

namespace Submission.LogDetV

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.MatBridge
open Submission.GenProc

noncomputable section

variable {d : ℕ}

lemma isHermitian_matOf (M : MatV d) (hM : (matOf d M).IsSymm) : (matOf d M).IsHermitian :=
  isHermitian_iff_isSymm.mpr hM

/-- The dot product on `EuclideanSpace ℝ (Fin d)` is the inner product. -/
lemma dotProduct_eq_inner (x y : EuclideanSpace ℝ (Fin d)) : x ⬝ᵥ y = inner ℝ x y := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma norm_sq_eq_sum_sq (x : MatV d) : ‖x‖ ^ 2 = ∑ p : Fin d × Fin d, x p ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **The eigenvalues of a symmetric matrix are bounded by its quadratic form on the unit
sphere.** -/
lemma abs_eigenvalues_le_of_quadFormV {M : MatV d} (hMsym : (matOf d M).IsSymm) {r : ℝ}
    (h : ∀ x : EuclideanSpace ℝ (Fin d), |quadFormV M x| ≤ r * ‖x‖ ^ 2) (i : Fin d) :
    |(isHermitian_matOf M hMsym).eigenvalues i| ≤ r := by
  have key : ∀ (hH : (matOf d M).IsHermitian) (i : Fin d),
      quadFormV M (hH.eigenvectorBasis i) = hH.eigenvalues i := by
    intro hH i
    have hmv := hH.mulVec_eigenvectorBasis i
    have hq := quadFormV_eq_dotProduct M (hH.eigenvectorBasis i)
    rw [hq, hmv, dotProduct_smul]
    have hself : (⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i)) = 1 := by
      rw [dotProduct_eq_inner (hH.eigenvectorBasis i) (hH.eigenvectorBasis i),
        real_inner_self_eq_norm_sq, hH.eigenvectorBasis.orthonormal.1 i]
      norm_num
    rw [hself, smul_eq_mul, mul_one]
  have hn : ‖((isHermitian_matOf M hMsym).eigenvectorBasis i :
      EuclideanSpace ℝ (Fin d))‖ = 1 :=
    (isHermitian_matOf M hMsym).eigenvectorBasis.orthonormal.1 i
  have h1 := h ((isHermitian_matOf M hMsym).eigenvectorBasis i)
  rw [key (isHermitian_matOf M hMsym) i] at h1
  rw [hn] at h1
  simpa using h1

/-- **Global second-order Taylor bound in the `MatV` model**. -/
theorem log_det_matOf_add_le (M : MatV d) (hMsym : (matOf d M).IsSymm) {a₀ r : ℝ}
    (ha₀ : 0 < a₀) (hr : 0 ≤ r) (har : r < a₀)
    (hspec : ∀ x : EuclideanSpace ℝ (Fin d), |quadFormV M x| ≤ r * ‖x‖ ^ 2) :
    Real.log (matOf d (a₀ • oneV d + M)).det ≤ (d : ℝ) * Real.log a₀
      + (matOf d M).trace / a₀ - (1 / 2) * (a₀ + r)⁻¹ ^ 2 * ‖M‖ ^ 2 := by
  have hH := isHermitian_matOf M hMsym
  have h1 := Submission.LogDet.log_det_add_smul_one_le (matOf d M) hH ha₀ hr har
    (fun i => abs_eigenvalues_le_of_quadFormV hMsym hspec i)
  have hmap : matOf d (a₀ • oneV d + M) = a₀ • 1 + matOf d M := by
    rw [map_add, map_smul, matOf_oneV]
  have htr : (matOf d M * matOf d M).trace = ‖M‖ ^ 2 := by
    rw [norm_sq_eq_sum_sq, Fintype.sum_prod_type,
      show (matOf d M * matOf d M) = (matOf d M) * (matOf d M)ᵀ from by rw [hMsym.eq],
      trace_mul_transpose_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [matOf_apply]
    ring
  simpa only [hmap, htr] using h1

end

end Submission.LogDetV
