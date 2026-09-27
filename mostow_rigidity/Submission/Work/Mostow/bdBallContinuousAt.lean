import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.poBdReg
import Submission.Work.Mostow.Hyper

/-!
# Continuity of the boundary action on the closed unit ball

The boundary action is `bd g = bdO (rep g)`, and

`bdO A z = WithLp.toLp 2 (fun i => (mat A *ᵥ theta z) (inl i) / (mat A *ᵥ theta z) (inr 0))`,

a quotient of continuous functions of `z`.  It is therefore continuous at every point at which
the denominator `d z = (mat A *ᵥ theta z) (inr 0)` does not vanish.  The point of the closed ball
is that for `‖z‖ ≤ 1` this denominator *cannot* vanish: writing `c = A₀₀` and
`r = (A_{0,inl i})_i` for the time row of `mat A`, one has `d z = c + ⟪r, z⟫` and, from
`A J Aᵀ = J`, `‖r‖² = c² − 1`.  Hence if `d z = 0` then
`|c| = |⟪r,z⟫| ≤ √(c²−1)‖z‖ ≤ √(c²−1) < |c|`, a contradiction.

This is exactly the tool needed to restrict the (algebraic) boundary formula for `bd g` to the
closed Poincaré ball: on the open ball plus the sphere, `bd g` is a locally continuous function.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- The time coordinate of `mat A *ᵥ theta z` is an affine function of `z`: the constant
`A₀₀` plus the pairing of `z` with the time row `(A_{0, inl i})_i` of `mat A`. -/
lemma time_theta_form (A : O1 n) (z : E n) :
    ((mat A).mulVec (theta z)) (Sum.inr 0) =
      (mat A) (Sum.inr 0) (Sum.inr 0) +
        inner ℝ (WithLp.toLp 2 (fun i => (mat A) (Sum.inr 0) (Sum.inl i))) z := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, inner_eq_sum]
  simp only [theta, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one]
  ring

/-- On the closed unit ball the time coordinate of `mat A *ᵥ theta z` never vanishes. -/
lemma mat_mulVec_theta_time_ne_zero_of_norm_le_one (A : O1 n) {z : E n}
    (hz : ‖z‖ ≤ 1) :
    (mat A *ᵥ theta z) (Sum.inr 0) ≠ 0 := by
  intro h0
  have hform := time_theta_form A z
  have h0' : (mat A *ᵥ theta z) (Sum.inr 0) = 0 := h0
  have hrel : inner ℝ (WithLp.toLp 2 (fun i => (mat A) (Sum.inr 0) (Sum.inl i))) z =
      -((mat A) (Sum.inr 0) (Sum.inr 0)) := by linarith
  have hle : 0 ≤ (mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1 := by
    rw [← Hyper.row_norm_sq A]; positivity
  have hlt : Real.sqrt ((mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) <
      |(mat A) (Sum.inr 0) (Sum.inr 0)| := by
    have h1 : Real.sqrt ((mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) <
        Real.sqrt ((mat A) (Sum.inr 0) (Sum.inr 0) ^ 2) := by
      apply Real.sqrt_lt_sqrt hle
      linarith
    rwa [Real.sqrt_sq_eq_abs] at h1
  have hcs := Hyper.abs_inner_row_le A z
  rw [hrel, abs_neg] at hcs
  have hstep : Real.sqrt ((mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) * ‖z‖ ≤
      Real.sqrt ((mat A) (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) * 1 :=
    mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg _)
  linarith

/-- `bdO A` is continuous at every point of the closed unit ball. -/
lemma continuousAt_bdO_of_norm_le_one (A : O1 n) {z : E n} (hz : ‖z‖ ≤ 1) :
    ContinuousAt (bdO A) z := by
  have hden : (mat A *ᵥ theta z) (Sum.inr 0) ≠ 0 :=
    mat_mulVec_theta_time_ne_zero_of_norm_le_one A hz
  have hcont : Continuous (fun ξ : E n => mat A *ᵥ theta ξ) :=
    poBdReg_continuous_mulVec_theta n A
  have hpi : ContinuousAt (fun ξ : E n => fun i : Fin n =>
      (mat A *ᵥ theta ξ) (Sum.inl i) / (mat A *ᵥ theta ξ) (Sum.inr 0)) z := by
    rw [continuousAt_pi]
    intro i
    exact (((continuous_apply (Sum.inl i)).comp hcont).continuousAt).div
      (((continuous_apply (Sum.inr 0)).comp hcont).continuousAt) hden
  have htlp : ContinuousAt (fun ξ : E n => WithLp.toLp 2 (fun i : Fin n =>
      (mat A *ᵥ theta ξ) (Sum.inl i) / (mat A *ᵥ theta ξ) (Sum.inr 0))) z := by
    exact ContinuousAt.comp (f := fun ξ : E n => fun i : Fin n =>
        (mat A *ᵥ theta ξ) (Sum.inl i) / (mat A *ᵥ theta ξ) (Sum.inr 0))
      (g := WithLp.toLp 2)
      (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n => ℝ)).continuousAt hpi
  rwa [poBdReg_bdO_form n A]

theorem bdBallContinuousAt (n : ℕ) (g : LeanEval.Geometry.MostowRigidity.PO n 1) :
    ∀ z : Submission.Mostow.E n, ‖z‖ ≤ 1 → ContinuousAt (Submission.Mostow.bd g) z :=
  fun z hz => continuousAt_bdO_of_norm_le_one (rep g) (z := z) hz

end

end Work.Mostow
