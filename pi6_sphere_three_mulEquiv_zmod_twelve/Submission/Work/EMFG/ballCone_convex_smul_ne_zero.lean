import Mathlib
import Submission.Work.EMFG.sphereBallDefs

/-!
# The cone over an intersection of small balls is convex and is a genuine cone

Let `a : α → Metric.sphere (0 : E) 1` be a family of unit vectors of a real inner product space and
let `ε > 0` be a radius.  The `ballCone` of `sphereBallDefs.lean` is

`ballCone S a ε = {x | ∀ i ∈ S, (1 - ε²/2) * ‖x‖ < ⟪x, a i⟫}`,

the cone over `⋂ i ∈ S, Metric.ball (a i) ε ⊆ Metric.sphere 0 1`.

This file proves that, as soon as `ε < 1` (so that `0 ≤ 1 - ε²/2`) and `S` is non-empty, this set

* is convex (`Convex ℝ (ballCone S a ε)`),
* is a genuine cone: it is stable under multiplication by positive scalars,
* does not contain the origin.

The three assertions are consequences of the elementary inequality
`(1 - ε²/2) * ‖p • x + q • y‖ ≤ p * ((1 - ε²/2) * ‖x‖) + q * ((1 - ε²/2) * ‖y‖)`,
which follows from the triangle inequality and `0 ≤ 1 - ε²/2`.
-/

namespace Work.EMFG

open Set Metric

/-- The set `{x : E | ∀ i ∈ s, c * ‖x‖ < ⟪x, v i⟫}` is convex whenever `0 ≤ c`.

Indeed `f i x = c * ‖x‖ - ⟪x, v i⟫` is a sum of a convex (the norm, scaled by the non-negative
constant `c`) and a linear function, hence convex; and `{x | f i x < 0}` is convex for each `i`.
The family of inequalities is preserved by convex combinations because for `p, q > 0` the strict
inequalities `c * ‖x‖ < ⟪x, v i⟫` and `c * ‖y‖ < ⟪y, v i⟫` combine to

`c * ‖p • x + q • y‖ ≤ c * (p * ‖x‖ + q * ‖y‖) < p * ⟪x, v i⟫ + q * ⟪y, v i⟫`. -/
lemma convex_setOf_mul_norm_lt_inner_forall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} (s : Set ι) {c : ℝ} (hc : 0 ≤ c) (v : ι → E) :
    Convex ℝ {x : E | ∀ i ∈ s, c * ‖x‖ < inner ℝ x (v i)} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy p q hp hq _
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  intro i hi
  have hx' := hx i hi
  have hy' := hy i hi
  -- triangle inequality, scaled by the non-negative constant `c`
  have hnorm : ‖p • x + q • y‖ ≤ p * ‖x‖ + q * ‖y‖ := by
    calc ‖p • x + q • y‖ ≤ ‖p • x‖ + ‖q • y‖ := norm_add_le _ _
      _ = p * ‖x‖ + q * ‖y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hp.le, Real.norm_of_nonneg hq.le]
  have h1 : c * ‖p • x + q • y‖ ≤ c * (p * ‖x‖ + q * ‖y‖) :=
    mul_le_mul_of_nonneg_left hnorm hc
  -- the two strict inequalities are combined with the positive weights `p`, `q`
  have h2 : c * (p * ‖x‖ + q * ‖y‖) < p * inner ℝ x (v i) + q * inner ℝ y (v i) := by
    have he : c * (p * ‖x‖ + q * ‖y‖) = p * (c * ‖x‖) + q * (c * ‖y‖) := by ring
    rw [he]
    have hp' : p * (c * ‖x‖) < p * inner ℝ x (v i) := mul_lt_mul_of_pos_left hx' hp
    have hq' : q * (c * ‖y‖) < q * inner ℝ y (v i) := mul_lt_mul_of_pos_left hy' hq
    linarith
  have h3 : inner ℝ (p • x + q • y) (v i) = p * inner ℝ x (v i) + q * inner ℝ y (v i) := by
    rw [inner_add_left, inner_smul_left, inner_smul_left]; simp
  linarith

/-- Pointwise form of the cone property: scaling a point satisfying `c * ‖x‖ < ⟪x, v⟫` by a
positive real `r` preserves the inequality, `c * ‖r • x‖ < ⟪r • x, v⟫`. -/
lemma mul_norm_smul_lt_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {c : ℝ} {v x : E} (hx : c * ‖x‖ < inner ℝ x v) {r : ℝ} (hr : 0 < r) :
    c * ‖r • x‖ < inner ℝ (r • x) v := by
  rw [norm_smul, Real.norm_of_nonneg hr.le]
  have h : inner ℝ (r • x) v = r * inner ℝ x v := by
    rw [inner_smul_left]; simp
  rw [h]
  calc c * (r * ‖x‖) = r * (c * ‖x‖) := by ring
    _ < r * inner ℝ x v := mul_lt_mul_of_pos_left hx hr

theorem ballCone_convex_smul_ne_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {α : Type*} (S : Finset α) (hS : S.Nonempty) (a : α → Metric.sphere (0 : E) 1) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    Convex ℝ (ballCone S a ε) ∧
      (∀ x ∈ ballCone S a ε, ∀ r : ℝ, 0 < r → r • x ∈ ballCone S a ε) ∧
      (0 : E) ∉ ballCone S a ε := by
  have hε2 : ε ^ 2 < 1 := by nlinarith
  have hc0 : 0 ≤ 1 - ε ^ 2 / 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · -- convexity, from the general lemma for the family `v i = a i` over `s = S`
    have h := convex_setOf_mul_norm_lt_inner_forall (s := (S : Set α)) hc0 (fun i : α => (a i : E))
    simpa [ballCone] using h
  · -- stability under positive scalars
    intro x hx r hr
    simp only [ballCone, Set.mem_ofPred_eq] at hx ⊢
    intro i hi
    exact mul_norm_smul_lt_inner (hx i hi) hr
  · -- the origin satisfies `0 < 0`
    intro h
    simp only [ballCone, Set.mem_ofPred_eq] at h
    obtain ⟨i, hi⟩ := hS
    have hh := h i hi
    simp at hh

end Work.EMFG
