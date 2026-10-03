/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The dimension function on projections of `N(G)`

The trace `τ a = ⟪δ₁, a δ₁⟫` (`Submission.Work.ORVonNeumann.Rep.Trace`) restricts on
projections of `N(G)` to the *dimension function*: `τ(p) ∈ [0,1]`, with
`τ(p) = 0 ↔ p = 0` and `τ(p) = 1 ↔ p = 1`.  This is the numerical input from which the
extended rank function `rk_G` of Jaikin-Zapirain–López-Álvarez (arXiv:1810.12135, §3.2) is
built.

## Main results

* `Work.ORVonNeumann.Rep.tau_projection` — `τ p = ‖p δ₁‖²` for a projection `p`;
* `Work.ORVonNeumann.Rep.tau_projection_re_nonneg`, `…tau_projection_re_le_one` —
  `0 ≤ τ p ≤ 1`;
* `Work.ORVonNeumann.Rep.tau_projection_eq_zero_iff` — `τ p = 0 ↔ p = 0`;
* `Work.ORVonNeumann.Rep.tau_projection_eq_one_iff` — `τ p = 1 ↔ p = 1`;
* `Work.ORVonNeumann.Rep.isStarProjection_one_sub` — `1 - p` is a projection when `p` is.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.Trace

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORVonNeumann.Rep

open MeasureTheory

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- `⟪δ₁, δ₁⟫ = 1`. -/
theorem inner_delta1_self : inner ℂ (delta1 G) (delta1 G) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_delta1]
  norm_num

/-- The trace of `0` is `0`. -/
@[simp]
theorem tau_zero : tau (0 : ↥(groupVonNeumann G)) = 0 := by
  rw [tau, show ((0 : ↥(groupVonNeumann G)) : boundedEnd G) = 0 from rfl, zero_apply,
    inner_zero_right]

/-- The complement of a projection is a projection. -/
theorem isStarProjection_one_sub (p : ↥(groupVonNeumann G)) (hp : IsStarProjection p) :
    IsStarProjection (1 - p) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, sub_mul, one_mul, mul_sub, mul_one, hp.isIdempotentElem]
    abel
  · rw [IsSelfAdjoint, (star_sub (1 : ↥(groupVonNeumann G)) p), star_one, hp.isSelfAdjoint]

/-- The trace of a projection is the squared norm of `p δ₁`. -/
theorem tau_projection (p : ↥(groupVonNeumann G)) (hp : IsStarProjection p) :
    tau p = inner ℂ ((p : boundedEnd G) (delta1 G)) ((p : boundedEnd G) (delta1 G)) := by
  rw [← tau_star_mul_self p,
    show star p * p = p from by rw [hp.isSelfAdjoint]; exact hp.isIdempotentElem]

/-- The trace of a projection is non-negative. -/
theorem tau_projection_re_nonneg (p : ↥(groupVonNeumann G)) (hp : IsStarProjection p) :
    0 ≤ (tau p).re := by
  have h := inner_self_nonneg (𝕜 := ℂ) (x := (p : boundedEnd G) (delta1 G))
  rw [tau_projection p hp]
  exact h

/-- The trace of a projection is at most one: `1 - τ p = ‖(1 - p) δ₁‖²`. -/
theorem tau_projection_re_le_one (p : ↥(groupVonNeumann G)) (hp : IsStarProjection p) :
    (tau p).re ≤ 1 := by
  have hself : (p : boundedEnd G) ((p : boundedEnd G) (delta1 G))
      = (p : boundedEnd G) (delta1 G) := by
    show ((p * p : ↥(groupVonNeumann G)) : boundedEnd G) (delta1 G)
      = (p : boundedEnd G) (delta1 G)
    rw [hp.isIdempotentElem]
  have h2 : inner ℂ ((p : boundedEnd G) (delta1 G)) ((p : boundedEnd G) (delta1 G))
      = inner ℂ (delta1 G) ((p : boundedEnd G) (delta1 G)) := by
    rw [← ContinuousLinearMap.adjoint_inner_right (A := (p : boundedEnd G))
        (x := delta1 G) (y := (p : boundedEnd G) (delta1 G)),
      ← ContinuousLinearMap.star_eq_adjoint, ← StarMemClass.coe_star, hp.isSelfAdjoint, hself]
  have hq : IsStarProjection (1 - p) := isStarProjection_one_sub p hp
  have hcoe : (((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G)
      = delta1 G - (p : boundedEnd G) (delta1 G) := by
    rw [Subalgebra.coe_sub, Subalgebra.coe_one, sub_apply, one_apply_eq_self]
  have hcoe' : (p : boundedEnd G) (delta1 G)
      = delta1 G - ((((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G)) := by
    rw [hcoe]
    abel
  have hqid : (((1 - p : ↥(groupVonNeumann G))) : boundedEnd G)
      ((((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G))
      = (((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G) := by
    show (((1 - p) * (1 - p) : ↥(groupVonNeumann G)) : boundedEnd G) (delta1 G)
      = (((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G)
    rw [hq.isIdempotentElem]
  have hqinner : inner ℂ (delta1 G) ((((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G))
      = inner ℂ ((((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G))
                ((((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G)) := by
    rw [← ContinuousLinearMap.adjoint_inner_right
        (A := (((1 - p : ↥(groupVonNeumann G))) : boundedEnd G)) (x := delta1 G)
        (y := (((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G)),
      ← ContinuousLinearMap.star_eq_adjoint, ← StarMemClass.coe_star, hq.isSelfAdjoint, hqid]
  have key : (tau p : ℂ) = 1 - inner ℂ
      ((((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G))
      ((((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G)) := by
    rw [tau_projection p hp, h2, hcoe', inner_sub_right, hqinner, inner_delta1_self]
  rw [key, Complex.sub_re, Complex.one_re]
  have hnn : 0 ≤ (inner ℂ ((((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G))
      ((((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G))).re :=
    inner_self_nonneg (𝕜 := ℂ)
      (x := ((((1 - p : ↥(groupVonNeumann G))) : boundedEnd G) (delta1 G)))
  linarith

/-- Faithfulness of the dimension function: `τ p = 0` iff `p = 0`. -/
theorem tau_projection_eq_zero_iff (p : ↥(groupVonNeumann G)) (hp : IsStarProjection p) :
    tau p = 0 ↔ p = 0 := by
  have hz : tau (0 : ↥(groupVonNeumann G)) = 0 := tau_zero
  refine ⟨fun h => ?_, fun h => by rw [h]; exact hz⟩
  have h1 : inner ℂ ((p : boundedEnd G) (delta1 G)) ((p : boundedEnd G) (delta1 G)) = 0 := by
    rw [← tau_projection p hp]; exact h
  exact delta1_separating p (inner_self_eq_zero.mp h1)

/-- The dimension function detects the identity: `τ p = 1` iff `p = 1`. -/
theorem tau_projection_eq_one_iff (p : ↥(groupVonNeumann G)) (hp : IsStarProjection p) :
    tau p = 1 ↔ p = 1 := by
  have hone : tau (1 : ↥(groupVonNeumann G)) = 1 := tau_one
  refine ⟨fun h => ?_, fun h => by rw [h]; exact hone⟩
  have h1p : IsStarProjection (1 - p) := isStarProjection_one_sub p hp
  have hsub : tau ((1 : ↥(groupVonNeumann G)) - p)
      = tau (1 : ↥(groupVonNeumann G)) - tau p := by
    have hone' : (1 : ↥(groupVonNeumann G)) = (1 - p) + p := by abel
    rw [hone', tau_add]
    abel
  have htau : tau (1 - p) = 0 := by
    rw [hsub, h, hone]
    simp
  have hzero : (1 - p : ↥(groupVonNeumann G)) = 0 :=
    (tau_projection_eq_zero_iff (1 - p) h1p).mp htau
  exact (sub_eq_zero.mp hzero).symm

end Work.ORVonNeumann.Rep
