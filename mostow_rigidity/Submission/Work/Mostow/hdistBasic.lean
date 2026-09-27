import Mathlib
import Submission.Work.Mostow.Hyper

/-!
# Basic metric properties of the hyperbolic distance `hdist`

`hdist u v = arcosh (tpart u * tpart v - ⟪u,v⟫) = arcosh (cc u v)` in the hyperboloid chart
`E n = ℝⁿ`. This file proves the three metric axioms for it:

* `0 ≤ hdist u v`;
* `hdist u v = hdist v u`;
* `hdist u v = 0 ↔ u = v`.

The analytic input is the elementary inequality `1 + ‖u‖‖v‖ ≤ tpart u * tpart v`, which is
the statement that the chart map `u ↦ (u, √(1+‖u‖²))` is `1`-Lipschitz along the time
coordinate; it also characterises the case where `cc u v = 1`, which is exactly `u = v`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- The elementary inequality `1 + ‖u‖‖v‖ ≤ tpart u * tpart v`, i.e.
`(1 + ab)² ≤ (1 + a²)(1 + b²)` with `a = ‖u‖`, `b = ‖v‖`. -/
lemma one_add_norm_mul_norm_le_tpart_mul {n : ℕ} (u v : E n) :
    1 + ‖u‖ * ‖v‖ ≤ tpart u * tpart v := by
  have h1 : (1 + ‖u‖ * ‖v‖) ^ 2 ≤ (tpart u * tpart v) ^ 2 := by
    rw [mul_pow, Hyper.sq_tpart, Hyper.sq_tpart]
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  have h2 : (0 : ℝ) ≤ 1 + ‖u‖ * ‖v‖ := by positivity
  have h3 : (0 : ℝ) ≤ tpart u * tpart v :=
    mul_nonneg (le_of_lt (Hyper.tpart_pos u)) (le_of_lt (Hyper.tpart_pos v))
  have h4 := sq_le_sq.mp h1
  rwa [abs_of_nonneg h2, abs_of_nonneg h3] at h4

/-- Consequently `1 ≤ cc u v`: the cosh-kernel takes values in the domain of `arcosh`. -/
lemma one_le_cc {n : ℕ} (u v : E n) : (1 : ℝ) ≤ Hyper.cc u v := by
  rw [Hyper.cc]
  have hb := one_add_norm_mul_norm_le_tpart_mul u v
  have hle := real_inner_le_norm u v
  linarith

/-- Equality in `1 + ‖u‖‖v‖ ≤ tpart u * tpart v` forces `‖u‖ = ‖v‖`. -/
lemma norm_eq_of_tpart_mul_eq {n : ℕ} (u v : E n)
    (h : tpart u * tpart v = 1 + ‖u‖ * ‖v‖) : ‖u‖ = ‖v‖ := by
  have h1 : (tpart u * tpart v) ^ 2 = (1 + ‖u‖ * ‖v‖) ^ 2 := by rw [h]
  rw [mul_pow, Hyper.sq_tpart, Hyper.sq_tpart] at h1
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- The cosh-kernel equals `1` exactly on the diagonal. -/
lemma cc_eq_one_iff {n : ℕ} (u v : E n) : Hyper.cc u v = 1 ↔ u = v := by
  constructor
  · intro h
    change tpart u * tpart v - inner ℝ u v = 1 at h
    have hle : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
    have hb : 1 + ‖u‖ * ‖v‖ ≤ tpart u * tpart v := one_add_norm_mul_norm_le_tpart_mul u v
    have hinner : inner ℝ u v = ‖u‖ * ‖v‖ := by linarith
    have htpart : tpart u * tpart v = 1 + ‖u‖ * ‖v‖ := by linarith
    have hnorm : ‖u‖ = ‖v‖ := norm_eq_of_tpart_mul_eq u v htpart
    have hzero : ‖u - v‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hinner]
      nlinarith
    have hz : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro h
    subst h
    change tpart u * tpart u - inner ℝ u u = 1
    rw [← sq, real_inner_self_eq_norm_sq, Hyper.sq_tpart]
    ring

theorem hdistBasic (n : ℕ) :
    (∀ u v : E n, 0 ≤ hdist u v) ∧ (∀ u v : E n, hdist u v = hdist v u) ∧
      (∀ u v : E n, hdist u v = 0 ↔ u = v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    rw [Hyper.hdist_eq_cc]
    exact Real.arcosh_nonneg (one_le_cc u v)
  · intro u v
    rw [Hyper.hdist_eq_cc, Hyper.hdist_eq_cc, Hyper.cc_comm]
  · intro u v
    rw [Hyper.hdist_eq_cc, Real.arcosh_eq_zero_iff (one_le_cc u v), cc_eq_one_iff]

end Work.Mostow
