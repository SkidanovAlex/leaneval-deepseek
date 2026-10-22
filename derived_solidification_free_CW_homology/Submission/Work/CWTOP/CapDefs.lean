/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.CWTOP.Closed

/-!
# The cap `-1 < y 0` of the model sphere: definitions and elementary facts

The model sphere `modelSphere n` is the unit sphere of `Fin (n + 1) → ℝ` for the *sup* norm
(`Pi.norm_def`), i.e. the boundary of the unit cube.  The cap

`capGt n = {y : modelSphere n // -1 < y.1 0}`

is the complement of the single point `-pole n`, where `pole n = (1, 0, …, 0)` is the "north
pole".  This file collects the definitions used to contract it: the pole, the underlying vector
of a point of the cap, and the straight line interpolation `interpVec t y = (1 - t) • y + t • pole`
towards the pole.
-/

open Set Metric Topology
open scoped unitInterval

noncomputable section

namespace Work.CWTOP

/-! ## The north pole -/

/-- The "north pole" `(1, 0, …, 0)` of the model sphere. -/
def pole (n : ℕ) : Fin (n + 1) → ℝ := Pi.single 0 1

@[simp] lemma pole_zero (n : ℕ) : pole n 0 = 1 := Pi.single_eq_same 0 1

lemma pole_eq_zero (n : ℕ) {i : Fin (n + 1)} (hi : i ≠ 0) : pole n i = 0 :=
  Pi.single_eq_of_ne hi 1

lemma norm_pole (n : ℕ) : ‖pole n‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    intro i
    by_cases hi : i = 0
    · subst hi
      simp
    · rw [pole_eq_zero n hi]
      simp
  · have h := norm_le_pi_norm (pole n) 0
    simpa using h

lemma pole_mem_modelSphere (n : ℕ) : pole n ∈ modelSphere n := by
  rw [modelSphere, Metric.mem_sphere, dist_eq_norm, sub_zero]
  exact norm_pole n

/-! ## The cap -/

/-- Membership in the model sphere, in terms of the norm. -/
lemma mem_modelSphere {n : ℕ} {v : Fin (n + 1) → ℝ} :
    v ∈ modelSphere n ↔ ‖v‖ = 1 := by
  rw [modelSphere, Metric.mem_sphere, dist_eq_norm, sub_zero]

/-- The cap `-1 < y 0` of the model sphere. -/
abbrev capGt (n : ℕ) : Type := {y : modelSphere n // -1 < y.1 0}

/-- The underlying vector of a point of the cap. -/
def capVec {n : ℕ} (y : capGt n) : Fin (n + 1) → ℝ := (y.1 : Fin (n + 1) → ℝ)

lemma capVec_norm {n : ℕ} (y : capGt n) : ‖capVec y‖ = 1 := by
  have h := Metric.mem_sphere.mp
    (y.1.2 : (y.1 : Fin (n + 1) → ℝ) ∈ Metric.sphere (0 : Fin (n + 1) → ℝ) 1)
  simpa [capVec, dist_eq_norm, sub_zero] using h

lemma capVec_coord {n : ℕ} (y : capGt n) : -1 < capVec y 0 := y.2

/-! ## The straight line from a point of the cap to the pole -/

/-- The straight line interpolation between a vector and the pole. -/
def interpVec {n : ℕ} (t : ℝ) (y : capGt n) : Fin (n + 1) → ℝ :=
  (1 - t) • capVec y + t • pole n

/-- The straight line interpolation, as a function of a point of a homotopy. -/
def interpFun (n : ℕ) (q : unitInterval × capGt n) : Fin (n + 1) → ℝ :=
  interpVec (q.1 : ℝ) q.2

@[simp] lemma interpFun_apply (n : ℕ) (q : unitInterval × capGt n) :
    interpFun n q = interpVec (q.1 : ℝ) q.2 := rfl

@[simp] lemma interpVec_apply_zero {n : ℕ} (t : ℝ) (y : capGt n) :
    interpVec t y 0 = (1 - t) * capVec y 0 + t := by
  simp [interpVec]

lemma interpVec_apply_of_ne_zero {n : ℕ} (t : ℝ) (y : capGt n) {i : Fin (n + 1)} (hi : i ≠ 0) :
    interpVec t y i = (1 - t) * capVec y i := by
  simp [interpVec, pole_eq_zero n hi]

@[simp] lemma interpVec_zero {n : ℕ} (y : capGt n) : interpVec 0 y = capVec y := by
  simp [interpVec]

@[simp] lemma interpVec_one {n : ℕ} (y : capGt n) : interpVec 1 y = pole n := by
  simp [interpVec]

end Work.CWTOP
