import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.lindDefs
import Submission.Work.KT.FP.laurent_coeff_trunc_eval
import Submission.Work.KT.Fund.Laurent

/-!
# `Work.KT.FP.coeffSeq_sum_isUnit`

If a Laurent polynomial matrix `Q` over `C(X, ℂ)` has all its coefficients in degrees `[-m, m]`
and its image under `Work.KT.laurentMap X` is a unit of `Mₙ(C(X × S¹, ℂ))`, then for every point
`z` of the unit circle the polynomial matrix `∑_j z^j • (coeff j)` built from the coefficient
sequence of `Q` is a unit of `Mₙ(C(X, ℂ))`.

The proof evaluates the unit pointwise on the slice `X × {z}`: the coefficient sum is `z^m` times
the evaluation of `Q` along that slice, and both factors are units.
-/

namespace Work.KT.FP

open Matrix

open scoped BigOperators

theorem coeffSeq_sum_isUnit (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m : ℕ) (Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (Q i j).coeff k = 0)
    (hunit : IsUnit (Q.map (Work.KT.laurentMap X))) {z : ℂ} (hz : ‖z‖ = 1) :
    IsUnit (∑ j : Fin (2 * m + 1), z ^ (j : ℕ) • coeffSeq X n m Q j) := by
  rw [show (∑ j : Fin (2 * m + 1), z ^ (j : ℕ) • coeffSeq X n m Q j)
      = penQ X n (2 * m) (coeffSeq X n m Q) z from rfl]
  rw [isUnit_matrix_iff_forall_eval]
  intro x
  have hzne : z ≠ 0 := by rintro rfl; norm_num at hz
  have hzmem : z ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hz
  obtain ⟨w, hw⟩ : ∃ w : Work.KT.Sph ℂ, (w : ℂ) = z := ⟨⟨z, hzmem⟩, rfl⟩
  -- The pointwise evaluation of the unit on the slice `X × {z}`.
  have hT : IsUnit ((Q.map (Work.KT.laurentMap X)).map (fun f => f (x, w))) := by
    have h := hunit.map (RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ (x, w)).toRingHom)
    rw [RingHom.mapMatrix_apply] at h
    exact h
  -- The coefficient sum is `z^m` times that evaluation.
  have hEq : (penQ X n (2 * m) (coeffSeq X n m Q) z).map (fun f => f x)
      = (z ^ m : ℂ) • ((Q.map (Work.KT.laurentMap X)).map (fun f => f (x, w))) := by
    ext a b
    rw [penQ_map_eval]
    simp only [coeffSeq, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [laurentMap_apply_eq_sum]
    have h := laurent_coeff_trunc_eval X (Q a b) m z hzne x (hb a b)
    rw [hw]
    exact h
  rw [hEq, Algebra.smul_def]
  exact (IsUnit.map (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ))
    (isUnit_iff_ne_zero.mpr (pow_ne_zero m hzne))).mul hT

end Work.KT.FP
