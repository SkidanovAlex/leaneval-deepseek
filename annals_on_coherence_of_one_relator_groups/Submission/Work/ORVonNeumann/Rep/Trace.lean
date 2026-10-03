/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The trace `τ a = ⟪δ₁, a δ₁⟫` on the group von Neumann algebra

This file packages the vector state of `N(G) = ρ(G)'` (`Work.ORVonNeumann.groupVonNeumann`)
as a function, a `ℂ`-linear functional, and proves the elementary part of its API:

* `Work.ORVonNeumann.Rep.tau` — `τ a = ⟪δ₁, a δ₁⟫`;
* `Work.ORVonNeumann.Rep.tauLin` — `τ` as an element of `↥(groupVonNeumann G) →ₗ[ℂ] ℂ`;
* `Work.ORVonNeumann.Rep.tau_one` — `τ 1 = 1`;
* `Work.ORVonNeumann.Rep.tau_star` — `τ` is `*`-preserving (`⋆ (τ a) = τ a⋆`);
* `Work.ORVonNeumann.Rep.tau_star_mul_self` — `τ (a⋆ a) = ⟪a δ₁, a δ₁⟫`, hence
  `Work.ORVonNeumann.Rep.tau_re_nonneg` (positivity) and
  `Work.ORVonNeumann.Rep.tau_star_mul_self_eq_zero_iff` (faithfulness, from
  `Work.ORVonNeumann.Rep.delta1_separating`);
* `Work.ORVonNeumann.Rep.leftRegOp_delta1` — `λ g δ₁ = δ_g`, hence the trace of an element of
  the left regular representation: `Work.ORVonNeumann.Rep.tau_leftRegOp_one` and
  `Work.ORVonNeumann.Rep.tau_leftRegOp_of_ne`.

Traciality of `τ` (`τ (a b) = τ (b a)`) is a separate theorem,
`Work.Rep.tau_tracial`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann
import Submission.Work.ORVonNeumann.Rep.Orthonormal
import Submission.Work.ORVonNeumann.Rep.exists_leftRegular

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORVonNeumann.Rep

open MeasureTheory

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The left regular representation sends `δ₁` to `δ_g`: `λ g δ₁ = δ_g`. -/
theorem leftRegOp_delta1 (g : G) : leftRegOp g (delta1 G) = deltaG g := by
  classical
  refine MeasureTheory.Lp.ext ?_
  rw [Filter.EventuallyEq, MeasureTheory.Measure.ae_count_iff]
  intro x
  rw [leftRegOp_apply]
  have hA : (MeasureTheory.Lp.compMeasurePreserving (fun h : G => g⁻¹ * h)
      (MeasureTheory.measurePreserving_mul_left (MeasureTheory.Measure.count : Measure G) g⁻¹)
      (delta1 G) : G → ℂ) x = (delta1 G : G → ℂ) (g⁻¹ * x) :=
    MeasureTheory.Measure.ae_count_iff.mp (MeasureTheory.Lp.coeFn_compMeasurePreserving
      (μ := (Measure.count : Measure G)) (μb := (Measure.count : Measure G))
      (f := (fun h : G => g⁻¹ * h)) (delta1 G)
      (MeasureTheory.measurePreserving_mul_left (Measure.count : Measure G) g⁻¹)) x
  rw [hA]
  have hB := MeasureTheory.Measure.ae_count_iff.mp (delta1_coeFn (G := G)) (g⁻¹ * x)
  have hC := MeasureTheory.Measure.ae_count_iff.mp (deltaG_coeFn (G := G) g) x
  rw [hB, hC, Set.indicator_apply, Set.indicator_apply]
  by_cases hx : x = g
  · subst hx
    simp
  · have h1 : g⁻¹ * x ∉ ({1} : Set G) := by
      simp only [Set.mem_singleton_iff]
      intro hh
      exact hx (by rw [← mul_inv_cancel_left g x, hh, mul_one])
    have h2 : x ∉ ({g} : Set G) := by simpa [Set.mem_singleton_iff] using hx
    rw [if_neg h1, if_neg h2]

/-- **The trace of the group von Neumann algebra**: `τ a = ⟪δ₁, a δ₁⟫`. -/
noncomputable def tau (a : ↥(groupVonNeumann G)) : ℂ :=
  inner ℂ (delta1 G) ((a : boundedEnd G) (delta1 G))

@[simp]
theorem tau_apply (a : ↥(groupVonNeumann G)) :
    tau a = inner ℂ (delta1 G) ((a : boundedEnd G) (delta1 G)) := rfl

theorem tau_add (a b : ↥(groupVonNeumann G)) : tau (a + b) = tau a + tau b := by
  rw [tau, tau, tau, Subalgebra.coe_add, add_apply, inner_add_right]

theorem tau_smul (c : ℂ) (a : ↥(groupVonNeumann G)) : tau (c • a) = c * tau a := by
  rw [tau, tau,
    show ((c • a : ↥(groupVonNeumann G)) : boundedEnd G) = c • (a : boundedEnd G) from rfl,
    smul_apply, inner_smul_right]

/-- The trace as a `ℂ`-linear functional on `N(G)`. -/
noncomputable def tauLin : ↥(groupVonNeumann G) →ₗ[ℂ] ℂ where
  toFun := tau
  map_add' := tau_add
  map_smul' := fun c a => by rw [tau_smul, smul_eq_mul, RingHom.id_apply]

@[simp]
theorem tauLin_apply (a : ↥(groupVonNeumann G)) : tauLin a = tau a := rfl

theorem tau_one : tau (1 : ↥(groupVonNeumann G)) = 1 := by
  rw [tau, show ((1 : ↥(groupVonNeumann G)) : boundedEnd G) = 1 from rfl, one_apply_eq_self,
    inner_self_eq_norm_sq_to_K, norm_delta1]
  norm_num

/-- The trace is `*`-preserving: `⋆ (τ a) = τ a⋆`. -/
theorem tau_star (a : ↥(groupVonNeumann G)) : star (tau a) = tau (star a) := by
  rw [tau, tau, StarMemClass.coe_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rw [← inner_conj_symm]
  simp

/-- `τ (a⋆ a) = ⟪a δ₁, a δ₁⟫`. -/
theorem tau_star_mul_self (a : ↥(groupVonNeumann G)) :
    tau (star a * a) = inner ℂ ((a : boundedEnd G) (delta1 G)) ((a : boundedEnd G) (delta1 G)) := by
  rw [tau, Subalgebra.coe_mul, StarMemClass.coe_star, ContinuousLinearMap.star_eq_adjoint,
    mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]

/-- Positivity: `τ (a⋆ a)` is a non-negative real number. -/
theorem tau_re_nonneg (a : ↥(groupVonNeumann G)) : 0 ≤ (tau (star a * a)).re := by
  rw [tau_star_mul_self]
  simpa using inner_self_nonneg (𝕜 := ℂ) (x := (a : boundedEnd G) (delta1 G))

set_option synthInstance.maxHeartbeats 200000 in
/-- Faithfulness: `τ (a⋆ a) = 0` iff `a = 0`. -/
theorem tau_star_mul_self_eq_zero_iff (a : ↥(groupVonNeumann G)) :
    tau (star a * a) = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; simp [tau]⟩
  rw [tau_star_mul_self] at h
  exact delta1_separating a (inner_self_eq_zero.mp h)

/-- The trace of `1` in the left regular representation. -/
theorem tau_leftRegOp_one :
    tau (⟨leftRegOp (1 : G), leftRegOp_mem_groupVonNeumann (1 : G)⟩ : ↥(groupVonNeumann G)) = 1 := by
  rw [tau, leftRegOp_delta1]
  exact inner_deltaG_self (G := G) 1

/-- The trace of an element of the left regular representation: `τ (λ g) = 0` for `g ≠ 1`. -/
theorem tau_leftRegOp_of_ne (g : G) (hg : g ≠ 1) :
    tau (⟨leftRegOp g, leftRegOp_mem_groupVonNeumann g⟩ : ↥(groupVonNeumann G)) = 0 := by
  rw [tau, leftRegOp_delta1]
  exact inner_deltaG_of_ne (G := G) (Ne.symm hg)

end Work.ORVonNeumann.Rep
