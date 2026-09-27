/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The unit circle, Hermitian pairings on `ℂ^n`, and the two null-homotopy predicates

Shared vocabulary for the proof of `Work.KT.Dim2.loop_GL_nullhomotopic_of_det_log`.
-/
import Mathlib

namespace Work.KT.Dim2

open Matrix

noncomputable section

/-- The unit circle `S¹ = {z : ℂ // ‖z‖ = 1}`. -/
abbrev C1 : Type := Metric.sphere (0 : ℂ) 1

/-- The Hermitian pairing `∑ j, conj (u j) * v j` on `ℂ^n` (conjugate-linear in the first
variable). -/
def cip {n : ℕ} (u v : Fin n → ℂ) : ℂ := ∑ j, star (u j) * v j

/-- The squared Euclidean norm `∑ j, ‖u j‖ ^ 2` on `ℂ^n`. -/
def cnrm2 {n : ℕ} (u : Fin n → ℂ) : ℝ := ∑ j, ‖u j‖ ^ 2

/-- The rank-one matrix `a * bᴴ`, with entries `a i * conj (b j)`. -/
def outer {n : ℕ} (a b : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => a i * star (b j)

/-- The vector with a `1` in the first coordinate and `0` elsewhere (the empty vector for `n = 0`).
This is `Pi.single 0 1` whenever `n ≥ 1`, but avoids the `NeZero` instance. -/
def e0 (n : ℕ) : Fin n → ℂ := fun j => if (j : ℕ) = 0 then 1 else 0

/-- Two continuous loops `S¹ → ℂ` are **homotopic through non-vanishing loops**. -/
def LoopHom (f g : C(C1, ℂ)) : Prop :=
  ∃ H : ContinuousMap.Homotopy f g, ∀ p : unitInterval × C1, H p ≠ 0

/-- A continuous loop `S¹ → ℂ` which is null-homotopic through non-vanishing loops.  This is the
free null-homotopy condition for a loop in `ℂ*`; it is implied by the existence of a continuous
logarithm (which is the hypothesis of the main theorem), and only that implication is used. -/
abbrev NullLoop (f : C(C1, ℂ)) : Prop := LoopHom f 1

/-- The determinant loop `z ↦ det (g z)` of a continuous matrix-valued loop. -/
def detLoop {n : ℕ} (g : C(C1, Matrix (Fin n) (Fin n) ℂ)) : C(C1, ℂ) :=
  ⟨fun z => (g z).det, g.continuous.matrix_det⟩

/-- Two matrix-valued loops are **homotopic through invertible matrices**. -/
def HomU {n : ℕ} (f g : C(C1, Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  ∃ H : ContinuousMap.Homotopy f g, ∀ p : unitInterval × C1, IsUnit (H p)

/-- A matrix-valued loop is **nullhomotopic through invertible matrices** if it is homotopic to
the constant loop `1` by a homotopy whose values are all units. -/
abbrev NullH {n : ℕ} (f : C(C1, Matrix (Fin n) (Fin n) ℂ)) : Prop := HomU f 1

lemma cnrm2_nonneg {n : ℕ} (u : Fin n → ℂ) : 0 ≤ cnrm2 u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma cnrm2_zero_iff {n : ℕ} (u : Fin n → ℂ) : cnrm2 u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext j
    have hsum : ∑ i, ‖u i‖ ^ 2 = 0 := h
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖u i‖)).mp hsum j
      (Finset.mem_univ j)
    have hnorm : ‖u j‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hterm
    simpa using hnorm
  · rintro rfl
    simp [cnrm2]

lemma cnrm2_pos {n : ℕ} {u : Fin n → ℂ} (h : u ≠ 0) : 0 < cnrm2 u :=
  lt_of_le_of_ne (cnrm2_nonneg u) (fun hc => h ((cnrm2_zero_iff u).mp hc.symm))

lemma e0_ne_zero (n : ℕ) : e0 (n + 1) ≠ 0 := by
  intro h
  have := congrFun h 0
  simpa [e0] using this

end

end Work.KT.Dim2
