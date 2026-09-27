import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kl_defs
import Submission.Work.KT.Fund.isUnit_matrix_forall

/-!
# `Work.KT.Fund.klW_unit` — the "outside" factor `klW` is a unit

The matrix `klW X n b E = E + z (1 - E) + (1 - E) b` over `C(X × S¹, ℂ)` is invertible as soon as
its pointwise evaluations are: for `t = 1` the hypothesis `hout` says exactly that the evaluation
`(z (1 - E) + (1 - E) b + E)(x)` is invertible for every `x : X` and every `z ∈ S¹`.  By
`Work.KT.Fund.isUnit_matrix_forall` invertibility of a matrix over `C(Y, ℂ)` (`Y` compact
Hausdorff) is a pointwise condition, so it suffices to identify the evaluation of `klW` at a point
of `X × S¹` with that matrix; this is the auxiliary lemma `klW_eval` below.
-/

namespace Work.KT.Fund

open Matrix

/-- **Pointwise evaluation of `klW`.**  At `(x, z) ∈ X × S¹` the matrix `klW X n b E` evaluates to
`z (1 - E) + (1 - E) b + E` evaluated at `x`. -/
lemma klW_eval (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (x : X) (z : Sph ℂ) :
    (klW X n b E).map (fun f => f (x, z))
      = ((z : ℂ) • (1 - E) + (1 - E) * b + E).map (fun f => f x) := by
  ext i j
  simp only [klW, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, klP_apply, klz_apply, ContinuousMap.coe_sum,
    ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, ContinuousMap.smul_apply,
    Finset.sum_apply, ContinuousMap.zero_apply, DFunLike.ite_apply, smul_eq_mul]
  ring

theorem klW_unit (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E) (hc : E * b = b * E)
    (hout : ∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
      IsUnit ((((t : ℂ) * z) • (1 - E) + (1 - E) * b + E).map (fun f => f x))) :
    IsUnit (Work.KT.Fund.klW X n b E) := by
  rw [isUnit_matrix_forall]
  rintro ⟨x, z⟩
  have hz : ‖(z : ℂ)‖ = 1 := by
    simpa [dist_eq_norm, sub_zero] using z.2
  have h := hout x 1 (z : ℂ) zero_le_one le_rfl hz
  rw [klW_eval]
  simpa using h

end Work.KT.Fund
