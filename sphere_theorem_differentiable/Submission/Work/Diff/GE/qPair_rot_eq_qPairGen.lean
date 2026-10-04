import Mathlib
import Submission.Work.Diff.GE.CFQDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {n : ℕ}

/-!
# `Work.Diff.GE.qPair_rot_eq_qPairGen`

`qPair` computed in the orthonormal-frame decomposition (`rqA1 + 2 rqA2 - 2 rqA3`) is
invariant under the natural `GL(n)`-action `rot M` *up to* the correct general-basis
prefactor: if the Gram matrix `Γ` of the frame satisfies `M * Γ * Mᵀ = 1`, then

  `qPair (rot M C) = qPairGen Γ C`.

The key algebraic observation is that for `K := rqKr M` (the `A ⊗ A` action on a pair of
indices) and `Ki := Kᵀ * K = rqKr (Γ⁻¹)` (using `Γ⁻¹ = Mᵀ * M`, which is what `M Γ Mᵀ = 1`
gives), each of the three contraction patterns transforms as a trace identity

  `tr ((K X Kᵀ)ᵀ (K X Kᵀ) (K X Kᵀ)ᵀ) = tr (Xᵀ Ki X Ki Xᵀ Ki)`,

i.e. the "rotation" is not orthogonal but the discrepancy is exactly the insertion of the
Gram-inverse `Ki`, which is what `qPairGen` was built to encode. The degenerate / general
case is `trace_conj_triple` below.
-/

/-- Trace cyclic trick: `tr (K W Kᵀ) = tr ((Kᵀ K) W)`. -/
lemma rq_trace_sandwich (K W : rqMat n) : (K * W * Kᵀ).trace = ((Kᵀ * K) * W).trace := by
  rw [Matrix.trace_mul_comm (K * W) Kᵀ]
  rw [← Matrix.mul_assoc]

/-- The general-basis trace identity underlying `qPairGen`: conjugating the `(i,j)|(k,l)`
grouping `A` and the grouping `B` by `K ⊗ K` inserts `Kᵀ K` in every internal slot. -/
lemma rq_trace_conj_triple (K A B : rqMat n) :
    ((K * A * Kᵀ)ᵀ * (K * B * Kᵀ) * (K * B * Kᵀ)ᵀ).trace
      = (Aᵀ * (Kᵀ * K) * B * (Kᵀ * K) * Bᵀ * (Kᵀ * K)).trace := by
  rw [rq_conj_transpose, rq_conj_transpose]
  have hprod : (K * Aᵀ * Kᵀ) * (K * B * Kᵀ) * (K * Bᵀ * Kᵀ)
      = K * (Aᵀ * (Kᵀ * K) * B * (Kᵀ * K) * Bᵀ) * Kᵀ := by
    simp only [Matrix.mul_assoc]
  rw [hprod, rq_trace_sandwich]
  rw [Matrix.trace_mul_comm]

/-- Frobenius form of `rq_trace_conj_triple`, matching the shape in which `rqA1_eq` /
`rqA2_eq` / `rqA3_eq` write the three contraction patterns. -/
lemma rqDot_conj_triple (K A B : rqMat n) :
    rqDot (K * A * Kᵀ) ((K * B * Kᵀ) * (K * B * Kᵀ)ᵀ)
      = (Aᵀ * (Kᵀ * K) * B * (Kᵀ * K) * Bᵀ * (Kᵀ * K)).trace := by
  rw [rqDot]
  rw [← Matrix.mul_assoc]
  rw [rq_trace_conj_triple]

theorem qPair_rot_eq_qPairGen
    {n : ℕ} (Γ M : Matrix (Fin n) (Fin n) ℝ) (C : Curv4 n)
    (hM : M * Γ * Mᵀ = 1) :
    qPair (rot M C) = qPairGen Γ C := by
  -- `M * (Γ * Mᵀ) = 1` gives `(Γ * Mᵀ) * M = 1`, hence `Γ * (Mᵀ * M) = 1`,
  -- hence `Γ⁻¹ = Mᵀ * M`.
  have h1 : M * (Γ * Mᵀ) = 1 := by rwa [Matrix.mul_assoc] at hM
  have h2 : Γ * Mᵀ * M = 1 := (mul_eq_one_comm (a := M) (b := Γ * Mᵀ)).mp h1
  have h2' : Γ * (Mᵀ * M) = 1 := by rwa [Matrix.mul_assoc] at h2
  have hGam : Γ⁻¹ = Mᵀ * M := Matrix.inv_eq_right_inv h2'
  have hKi : rqKr (Γ⁻¹) = (rqKr M)ᵀ * rqKr M := by
    rw [hGam, rqKr_transpose, ← rqKr_mul]
  rw [qPairGen, rq_qPair_eq (rot M C), rqA1_eq, rqA2_eq, rqA3_eq,
    rqM_rot, rqN_rot, rqP_rot, hKi]
  rw [rqDot_conj_triple, rqDot_conj_triple, rqDot_conj_triple]

end Work.Diff.GE
