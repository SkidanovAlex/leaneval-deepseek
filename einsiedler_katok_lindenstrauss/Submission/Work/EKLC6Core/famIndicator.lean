import Mathlib

/-!
# `Work.EKLC6Core.famIndicator`

The finite rational combinations of indicators of a countable family `S : ℕ → Set X` of sets,

`famIndicator S c = ∑ n ∈ c.support, (c n : ℝ) • 1_{S n}`  (`c : ℕ →₀ ℚ`).

These functions form a *countable* family (indexed by the countable type `ℕ →₀ ℚ`) which is
`L²`-dense whenever `σ(S)` is the whole σ-algebra (see
`Work.EKLC6Core.exists_famIndicator_approx`), and each of them is bounded and measurable, so that
the (von Neumann) mean ergodic theorem applies to them.  The rationality of the coefficients is
what makes the family countable; density of the rational span is deduced from density of the real
span.

This file only contains definitions and elementary lemmas about them, so that it can be imported by
several independent proofs.
-/

open MeasureTheory

namespace Work.EKLC6Core

/-- `famIndicator S c` is the finite rational combination `∑ n ∈ c.support, (c n : ℝ) • 1_{S n}` of
the indicator functions of the family `S`. -/
noncomputable def famIndicator {X : Type*} (S : ℕ → Set X) (c : ℕ →₀ ℚ) : X → ℝ :=
  fun x => ∑ n ∈ c.support, ((c n : ℚ) : ℝ) * (S n).indicator (fun _ => (1 : ℝ)) x

@[simp] theorem famIndicator_apply {X : Type*} (S : ℕ → Set X) (c : ℕ →₀ ℚ) (x : X) :
    famIndicator S c x = ∑ n ∈ c.support, ((c n : ℚ) : ℝ) * (S n).indicator (fun _ => (1 : ℝ)) x :=
  rfl

theorem measurable_famIndicator {X : Type*} [MeasurableSpace X] (S : ℕ → Set X)
    (hS : ∀ n, MeasurableSet (S n)) (c : ℕ →₀ ℚ) : Measurable (famIndicator S c) := by
  refine Finset.measurable_sum _ fun n _ => ?_
  exact measurable_const.mul (Measurable.indicator measurable_const (hS n))

theorem aestronglyMeasurable_famIndicator {X : Type*} [MeasurableSpace X] (S : ℕ → Set X)
    (hS : ∀ n, MeasurableSet (S n)) (c : ℕ →₀ ℚ) (ν : Measure X) :
    AEStronglyMeasurable (famIndicator S c) ν :=
  (measurable_famIndicator S hS c).aestronglyMeasurable

/-- `famIndicator S c` is bounded by the `ℓ¹`-norm of its coefficient vector. -/
theorem abs_famIndicator_le {X : Type*} (S : ℕ → Set X) (c : ℕ →₀ ℚ) (x : X) :
    |famIndicator S c x| ≤ ∑ n ∈ c.support, |((c n : ℚ) : ℝ)| := by
  rw [famIndicator_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun n _ => ?_
  rw [abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  by_cases h : x ∈ S n
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- The bounded version of `abs_famIndicator_le`: `‖famIndicator S c‖ ≤ ∑ |c n|`. -/
theorem norm_famIndicator_le {X : Type*} (S : ℕ → Set X) (c : ℕ →₀ ℚ) (x : X) :
    ‖famIndicator S c x‖ ≤ ∑ n ∈ c.support, |((c n : ℚ) : ℝ)| := by
  rw [Real.norm_eq_abs]
  exact abs_famIndicator_le S c x

theorem memLp_famIndicator {X : Type*} [MeasurableSpace X] (S : ℕ → Set X)
    (hS : ∀ n, MeasurableSet (S n)) (c : ℕ →₀ ℚ) (ν : Measure X) [IsFiniteMeasure ν] :
    MemLp (famIndicator S c) 2 ν :=
  MemLp.of_bound (aestronglyMeasurable_famIndicator S hS c ν) _
    (Filter.Eventually.of_forall fun x => norm_famIndicator_le S c x)

/-- The indicator of `S n` itself is `famIndicator S (Finsupp.single n 1)`. -/
theorem famIndicator_single_one {X : Type*} (S : ℕ → Set X) (n : ℕ) :
    famIndicator S (Finsupp.single n (1 : ℚ)) = (S n).indicator (fun _ => (1 : ℝ)) := by
  funext x
  rw [famIndicator_apply]
  have hsupp : (Finsupp.single n (1 : ℚ)).support = {n} := Finsupp.support_single _ one_ne_zero
  rw [hsupp, Finset.sum_singleton]
  simp

end Work.EKLC6Core
