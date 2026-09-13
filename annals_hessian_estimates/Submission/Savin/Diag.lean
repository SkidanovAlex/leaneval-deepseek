/-
# `σ₂` of rank-one perturbations of the identity

Building blocks for the growth lemma: the radial cutoff function `χ = ψ ∘ ‖·‖` has, at a point
`ξ ≠ 0` with `u = ξ/‖ξ‖` and `ρ = ‖ξ‖`,

  `D²χ(ξ) = ψ''(ρ) • P_u + (ψ'(ρ)/ρ) • (1 - P_u)`,  `P_u v = ⟪v,u⟫ • u`,

so the relevant combination appearing in `Fop C ε (a (D²χ(ξ) - 1))` is
`α • P_u + β • (1 - P_u)`.  This file computes `trOp` and `s2` of such an operator.

* `s2_eq_trace_invariants`: for symmetric `T`, `s2 T = ((trOp T)² - trOp (T ∘ T))/2`
  (basis-free form of `σ₂`), via `coord_minor_sum_eq_trace_invariants`.
* `trOp_smulRight_self`, `trOp_one_sub_smulRight_self`: traces of the two projections.
* `s2_smulRight_combination`: `s2 (α • P + β • (1 - P)) = 3αβ + 3β²`.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Operator
import Submission.Commons.Analysis.Sigma2.coord_minor_sum_eq_trace_invariants

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- Basis-free form of the quadratic model of `σ₂`: for a symmetric operator `T`,
`s2 T = ((trOp T)² - trOp (T ∘ T))/2`. -/
theorem s2_eq_trace_invariants {T : ℝ⁴ →L[ℝ] ℝ⁴} (hT : T.IsSymmetric) :
    s2 T = ((trOp T) ^ 2 - trOp (T * T)) / 2 := by
  have h1 := Commons.Analysis.Sigma2.coord_minor_sum_eq_trace_invariants hT stdB4
  have h2 : s2 T = ∑ j : Fin 4, ∑ i : Fin 4, if i < j then
      (⟪T (stdB4 i), stdB4 i⟫ * ⟪T (stdB4 j), stdB4 j⟫ - ⟪T (stdB4 i), stdB4 j⟫ ^ 2) else 0 := rfl
  rw [h2, h1]
  rfl

/-- The rank-one orthogonal projection onto the line spanned by a unit vector `u`. -/
noncomputable def projOne (u : ℝ⁴) : ℝ⁴ →L[ℝ] ℝ⁴ :=
  ContinuousLinearMap.smulRight (innerSL ℝ u) u

theorem projOne_apply (u v : ℝ⁴) : projOne u v = ⟪v, u⟫ • u := by
  simp only [projOne, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_comm]

theorem projOne_isSymmetric (u : ℝ⁴) : (projOne u).IsSymmetric := by
  intro v w
  show ⟪projOne u v, w⟫ = ⟪v, projOne u w⟫
  rw [projOne_apply, projOne_apply, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm u w, mul_comm]

theorem projOne_mul_self {u : ℝ⁴} (hu : ‖u‖ = 1) : projOne u * projOne u = projOne u := by
  refine ContinuousLinearMap.ext fun v => ?_
  show (projOne u) ((projOne u) v) = (projOne u) v
  simp only [projOne_apply]
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]

theorem trOp_add (S T : ℝ⁴ →L[ℝ] ℝ⁴) : trOp (S + T) = trOp S + trOp T := by
  unfold trOp
  rw [show ((S + T : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴)
      = (S : ℝ⁴ →ₗ[ℝ] ℝ⁴) + (T : ℝ⁴ →ₗ[ℝ] ℝ⁴) from rfl, map_add]

theorem trOp_sub (S T : ℝ⁴ →L[ℝ] ℝ⁴) : trOp (S - T) = trOp S - trOp T := by
  unfold trOp
  rw [show ((S - T : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴)
      = (S : ℝ⁴ →ₗ[ℝ] ℝ⁴) - (T : ℝ⁴ →ₗ[ℝ] ℝ⁴) from rfl, map_sub]

theorem trOp_smul (a : ℝ) (S : ℝ⁴ →L[ℝ] ℝ⁴) : trOp (a • S) = a * trOp S := by
  unfold trOp
  rw [show ((a • S : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴) = a • (S : ℝ⁴ →ₗ[ℝ] ℝ⁴) from rfl,
    map_smul, smul_eq_mul]

theorem trOp_projOne {u : ℝ⁴} : trOp (projOne u) = ‖u‖ ^ 2 := by
  rw [trOp_eq_sum]
  have h1 : ∀ i : Fin 4, ⟪projOne u (stdB4 i), stdB4 i⟫ = (⟪u, stdB4 i⟫) ^ 2 := by
    intro i
    simp only [projOne_apply, real_inner_smul_left]
    rw [real_inner_comm (stdB4 i) u]
    ring
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  exact stdB4.sum_sq_inner_left u

/-- Pointwise form of `α • P_u + β • (1 - P_u)`. -/
theorem projOneCombination_apply {u : ℝ⁴} (hu : ‖u‖ = 1) (α β : ℝ) (v : ℝ⁴) :
    (α • projOne u + β • (1 - projOne u)) v = β • v + (α - β) • (⟪v, u⟫ • u) := by
  simp only [add_apply, sub_apply, smul_apply, one_apply_eq_self, projOne_apply]
  module

/-- `s2` of `α • P + β • (1 - P)` for a rank-one orthogonal projection `P` with unit vector. -/
theorem s2_projOne_combination {u : ℝ⁴} (hu : ‖u‖ = 1) (α β : ℝ) :
    s2 (α • projOne u + β • (1 - projOne u)) = 3 * α * β + 3 * β ^ 2 := by
  have hsym : (α • projOne u + β • (1 - projOne u)).IsSymmetric :=
    LinearMap.IsSymmetric.add
      (LinearMap.IsSymmetric.smul (c := α) (by simp) (projOne_isSymmetric u))
      (LinearMap.IsSymmetric.smul (c := β) (by simp)
        (LinearMap.IsSymmetric.sub LinearMap.IsSymmetric.one (projOne_isSymmetric u)))
  rw [s2_eq_trace_invariants hsym]
  set M : ℝ⁴ →L[ℝ] ℝ⁴ := α • projOne u + β • (1 - projOne u) with hM
  have hMv : ∀ v : ℝ⁴, M v = β • v + (α - β) • (⟪v, u⟫ • u) := fun v => projOneCombination_apply hu α β v
  have hMu : M u = α • u := by
    rw [hMv u, real_inner_self_eq_norm_sq, hu]
    module
  have hdiag : ∀ i : Fin 4, ⟪M (stdB4 i), stdB4 i⟫
      = β * ‖stdB4 i‖ ^ 2 + (α - β) * (⟪stdB4 i, u⟫) ^ 2 := by
    intro i
    rw [hMv (stdB4 i), inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_comm u (stdB4 i)]
    ring
  have htM : trOp M = α + 3 * β := by
    rw [trOp_eq_sum, Finset.sum_congr rfl fun i _ => hdiag i]
    rw [Finset.sum_add_distrib]
    have hs1 : (∑ i : Fin 4, β * ‖stdB4 i‖ ^ 2) = 4 * β := by
      rw [← Finset.mul_sum]
      have h : (∑ i : Fin 4, ‖stdB4 i‖ ^ 2) = 4 := by
        simp [stdB4.orthonormal.1]
      rw [h]; ring
    have hs2 : (∑ i : Fin 4, (α - β) * (⟪stdB4 i, u⟫) ^ 2) = (α - β) * ‖u‖ ^ 2 := by
      rw [← Finset.mul_sum]
      have h : (∑ i : Fin 4, (⟪stdB4 i, u⟫) ^ 2) = ‖u‖ ^ 2 := by
        rw [show (∑ i : Fin 4, (⟪stdB4 i, u⟫) ^ 2) = ∑ i : Fin 4, (⟪u, stdB4 i⟫) ^ 2 from by
          apply Finset.sum_congr rfl; intro i _; rw [real_inner_comm (stdB4 i) u]]
        exact stdB4.sum_sq_inner_left u
      rw [h]
    rw [hs1, hs2, hu]
    ring
  have hsq : M * M = β ^ 2 • (1 : ℝ⁴ →L[ℝ] ℝ⁴) + (α ^ 2 - β ^ 2) • projOne u := by
    refine ContinuousLinearMap.ext fun v => ?_
    show M (M v) = (β ^ 2 • (1 : ℝ⁴ →L[ℝ] ℝ⁴) + (α ^ 2 - β ^ 2) • projOne u) v
    simp only [hMv, map_add, map_smul, add_apply, smul_apply, one_apply_eq_self, projOne_apply,
      real_inner_smul_left, real_inner_self_eq_norm_sq, inner_add_left, real_inner_comm u v]
    rw [hu]
    module
  have htM2 : trOp (M * M) = α ^ 2 + 3 * β ^ 2 := by
    rw [hsq, trOp_add, trOp_smul, trOp_smul, trOp_one, trOp_projOne, hu]
    norm_num
    ring
  rw [htM, htM2]
  ring

end

end Submission
