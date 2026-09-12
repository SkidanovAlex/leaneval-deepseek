import Mathlib

/-!
# Analyticity of Fedja's auxiliary function on the unit disk

`f_a(w) = a · ∏_j (1 + w·conj z_j)^{p_j}` (complex powers with real
exponents) is complex-differentiable on the open unit disk whenever all
`z_j` lie in the closed unit disk (in fact `‖z_j‖ ≤ 1` suffices: for
`‖w‖ < 1` the base `1 + w·conj z_j` has real part `≥ 1 - ‖w‖ > 0`, hence
lies in the slit plane where the complex power `w ↦ w^p` is holomorphic).

Mathlib API hints: `Complex.norm_cpow_real` for the modulus; analyticity/
differentiability of `cpow` as a function of the base is available through
`AnalyticOn.cpow` / `AnalyticAt.cpow` / `DifferentiableAt.cpow` /
`Differentiable.const_cpow` (see e.g.
Mathlib/Analysis/SpecialFunctions/Complex/Analytic.lean and
Mathlib/Analysis/Complex/Hadamard.lean); `Complex.mem_slitPlane_iff`,
`mem_slitPlane_of_norm_lt_one`.  For products use `Finset` differentiableOn
lemmas (`DifferentiableOn.mul` etc. or `DifferentiableOn.prod`).

Prove the theorem below; you may add helper lemmas.  Do NOT change its
statement.  No sorries may remain in this file.
-/

noncomputable section

open scoped Real Complex
open Complex

namespace Submission.Core

/-- Complex power with a real exponent (principal branch via `cpow`). -/
noncomputable def cPow (w : ℂ) (p : ℝ) : ℂ := w ^ (p : ℂ)

/-- Fedja's auxiliary function `f_a(w) = a · ∏_j (1 + w·conj z_j)^{p_j}`. -/
noncomputable def fa (n : ℕ) (a : ℝ) (z : Fin n → ℂ) (p : Fin n → ℝ) (w : ℂ) : ℂ :=
  (a : ℂ) * ∏ j : Fin n, cPow (1 + w * starRingEnd ℂ (z j)) (p j)

/-- For `‖z‖ ≤ 1` and `w` in the open unit disk, `1 + w · conj z` belongs to
the (right half of the) slit plane: indeed `‖w * conj z‖ ≤ ‖w‖ < 1`. -/
private lemma slitPlane_mem_of_mem_ball {z : ℂ} (hz : ‖z‖ ≤ 1) {w : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) 1) : 1 + w * starRingEnd ℂ z ∈ slitPlane := by
  apply Complex.mem_slitPlane_of_norm_lt_one
  have hw' : ‖w‖ < 1 := by simpa using hw
  calc
    ‖w * starRingEnd ℂ z‖ = ‖w‖ * ‖starRingEnd ℂ z‖ := by rw [norm_mul]
    _ = ‖w‖ * ‖z‖ := by rw [Complex.norm_conj]
    _ ≤ ‖w‖ * 1 := by
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg w)
    _ = ‖w‖ := by rw [mul_one]
    _ < 1 := hw'

/-- Each factor `w ↦ (1 + w · conj z) ^ p` (fixed complex exponent `p`) is
complex-differentiable on the open unit disk for `‖z‖ ≤ 1`. -/
private lemma factor_differentiableOn (z : ℂ) (hz : ‖z‖ ≤ 1) (p : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ => (1 + w * starRingEnd ℂ z) ^ (p : ℂ))
      (Metric.ball (0 : ℂ) 1) := by
  refine DifferentiableOn.cpow_const ?_ ?_
  · exact (differentiableOn_const (1 : ℂ)).add
      (differentiableOn_id.mul_const (starRingEnd ℂ z))
  · intro w hw
    exact slitPlane_mem_of_mem_ball hz hw

/-- A pointwise product of finitely many complex-differentiable functions is
complex-differentiable. -/
private lemma differentiableOn_fintype_prod (ι : Type*) [Fintype ι] {s : Set ℂ}
    (F : ι → ℂ → ℂ) (hF : ∀ i, DifferentiableOn ℂ (F i) s) :
    DifferentiableOn ℂ (fun w : ℂ => ∏ i : ι, F i w) s := by
  classical
  let p : (ℂ → ℂ) → Prop := fun g => DifferentiableOn ℂ g s
  have h1 : p 1 := by
    dsimp [p]
    exact differentiableOn_const (1 : ℂ)
  have hmul : ∀ (a b : ℂ → ℂ), p a → p b → p (a * b) := by
    intro a b ha hb
    dsimp [p] at ha hb ⊢
    exact ha.mul hb
  have hbase : ∀ i ∈ (Finset.univ : Finset ι), p (F i) := by
    intro i hi
    exact hF i
  have h := Finset.prod_induction F p hmul h1 hbase
  have hEq : (fun w : ℂ => ∏ i : ι, F i w) = (∏ i : ι, F i) := by
    funext w
    rw [Finset.prod_apply]
  rw [hEq]
  exact h

/-- **`f_a` is holomorphic on the open unit disk** (for circle points
`z_j`, i.e. `‖z_j‖ ≤ 1`). -/
theorem fa_differentiableOn (n : ℕ) (a : ℝ) (z : Fin n → ℂ) (p : Fin n → ℝ)
    (hz : ∀ j : Fin n, ‖z j‖ ≤ 1) :
    DifferentiableOn ℂ (fa n a z p) (Metric.ball (0 : ℂ) 1) := by
  change DifferentiableOn ℂ
    (fun w : ℂ => (a : ℂ) * ∏ j : Fin n, cPow (1 + w * starRingEnd ℂ (z j)) (p j))
    (Metric.ball (0 : ℂ) 1)
  let F : Fin n → ℂ → ℂ := fun j w => cPow (1 + w * starRingEnd ℂ (z j)) (p j)
  have hF : ∀ j : Fin n, DifferentiableOn ℂ (F j) (Metric.ball (0 : ℂ) 1) := by
    intro j
    dsimp [F]
    simpa [cPow] using factor_differentiableOn (z j) (hz j) (p j)
  have hprod : DifferentiableOn ℂ (fun w : ℂ => ∏ j : Fin n, F j w)
      (Metric.ball (0 : ℂ) 1) := by
    exact differentiableOn_fintype_prod (ι := Fin n) F hF
  exact (differentiableOn_const (a : ℂ)).mul hprod

end Submission.Core

end
