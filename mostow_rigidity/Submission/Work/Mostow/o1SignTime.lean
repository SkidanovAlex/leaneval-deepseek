import Mathlib
import Submission.Work.Mostow.Hyper

/-!
# `tsign A` times the time coordinate of `mat A *ᵥ (u, 1)`

For `A ∈ O(n,1)` let `E = tsign A • mat A` be the representative of ``±A`` that preserves the
upper sheet of the hyperboloid (this is the substance of `Hyper.tsign_mul_time_mulVec_pos`).
The point `(u, 1)` of `ℝ^{n+1}` lies in the closed future light cone as soon as `‖u‖ ≤ 1`
(its Minkowski square is `‖u‖² - 1 ≤ 0` and its time coordinate is `1 > 0`), and a
sheet-preserving `J`-orthogonal matrix maps the future light cone into itself.  Hence

`0 < tsign A * (mat A *ᵥ (u,1)) (inr 0)`  for `‖u‖ ≤ 1`,

which is the content of `o1SignTime`.  This is the "causal" companion of
`Hyper.tsign_mul_time_mulVec_pos` (there `(u, tpart u)` — a timelike vector — is used).

The proof is the explicit estimate

`tsign A * (d + ⟪p,u⟫) ≥ |d| - |⟪p,u⟫| ≥ |d| - √(d²-1)‖u‖ ≥ |d| - √(d²-1) > 0`,

where `d = mat A (inr 0) (inr 0)`, `p` is the bottom row of `mat A`, `‖p‖ = √(d²-1)`
(`Hyper.row_norm_sq`) and `|⟪p,u⟫| ≤ ‖p‖ ‖u‖` (Cauchy–Schwarz, `Hyper.abs_inner_row_le`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open Matrix

noncomputable section

variable {n : ℕ}

/-- `tsign A` is `±1`, so multiplying by it cannot push a real number below `-|·|`. -/
lemma tsign_mul_ge_neg_abs (A : O1 n) (y : ℝ) : -|y| ≤ tsign A * y := by
  rcases Submission.Mostow.Hyper.tsign_eq_one_or A with h | h <;> rw [h]
  · simpa using neg_abs_le y
  · rw [neg_mul, one_mul]
    exact neg_le_neg (le_abs_self y)

/-- `tsign A * d = |d|` for `d = mat A (inr 0) (inr 0)`, phrased with the entry of `mat A`. -/
lemma tsign_mul_self_entry (A : O1 n) :
    tsign A * (mat A) (Sum.inr 0) (Sum.inr 0) = |(mat A) (Sum.inr 0) (Sum.inr 0)| :=
  Submission.Mostow.Hyper.tsign_abs A

theorem o1SignTime {n : ℕ} (A : Submission.Mostow.O1 n) (u : Submission.Mostow.E n)
    (hu : ‖u‖ ≤ 1) :
    0 < Submission.Mostow.tsign A *
      ((Submission.Mostow.mat A).mulVec (Sum.elim (fun i : Fin n => u i) (fun _ => (1 : ℝ))))
        (Sum.inr 0) := by
  set D : ℝ := (mat A) (Sum.inr 0) (Sum.inr 0) with hD
  set I : ℝ := inner ℝ (WithLp.toLp 2 (fun i => (mat A) (Sum.inr 0) (Sum.inl i))) u with hI
  have htime : ((mat A).mulVec (Sum.elim (fun i : Fin n => u i) (fun _ => (1 : ℝ)))) (Sum.inr 0)
      = D + I := by
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_one, Sum.elim_inl,
      Sum.elim_inr, mul_one, hD, hI,
      Submission.Mostow.Hyper.inner_eq_sum
        (WithLp.toLp 2 (fun i => (mat A) (Sum.inr 0) (Sum.inl i))) u]
    ring
  rw [htime]
  -- Cauchy–Schwarz for the bottom row, together with `‖u‖ ≤ 1`.
  have hcs : |I| ≤ Real.sqrt (D ^ 2 - 1) := by
    have h1 := Submission.Mostow.Hyper.abs_inner_row_le A u
    rw [← hI, ← hD] at h1
    have h2 : Real.sqrt (D ^ 2 - 1) * ‖u‖ ≤ Real.sqrt (D ^ 2 - 1) := by
      simpa using mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg (D ^ 2 - 1))
    linarith
  -- `√(d²-1) < |d|` as soon as `1 ≤ d²`, which holds for the time–time entry.
  have hlt : Real.sqrt (D ^ 2 - 1) < |D| := by
    have h1 := Submission.Mostow.Hyper.row_norm_sq A
    rw [← hD] at h1
    have h2 : (0 : ℝ) ≤
        ‖(WithLp.toLp 2 fun i => (mat A) (Sum.inr 0) (Sum.inl i) : E n)‖ ^ 2 := sq_nonneg _
    have h3 : 1 ≤ D ^ 2 := by linarith
    have h4 : Real.sqrt (D ^ 2 - 1) < Real.sqrt (D ^ 2) :=
      Real.sqrt_lt_sqrt (by linarith) (by linarith)
    rwa [Real.sqrt_sq_eq_abs] at h4
  have htg : -|I| ≤ tsign A * I := tsign_mul_ge_neg_abs A I
  have hsa := Submission.Mostow.Hyper.tsign_abs A
  rw [← hD] at hsa
  nlinarith [htg, hcs, hlt]

end

end Work.Mostow
