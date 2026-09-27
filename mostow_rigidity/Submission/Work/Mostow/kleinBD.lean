import Mathlib
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.poAux

/-!
# The Klein projection commutes with the projective action

For `u : E n` the point `kp u := (tpart u)⁻¹ • u` is the Klein-model coordinate of the
hyperboloid point `hlift u` (in the Klein ball `‖·‖ < 1`).  The lemma `kleinBD` says that the
projective/boundary action `bdO` of a matrix `A ∈ O(n,1)` on this ball is the same formula as the
hyperboloid action `actO` followed by the Klein projection:

`bdO A (kp u) = kp (actO A u)`.

Written for `g : PO n 1` this is
`bd g ((tpart u)⁻¹ • u) = (tpart (g • u))⁻¹ • (g • u)`.

Proof sketch: with `ξ = (tpart u)⁻¹ • u` and `w = mat A *ᵥ θ ξ` (where `θ ξ = (ξ,1)`),
* `hlift u = tpart u • θ ξ`, hence `hlift (actO A u) = (tsign A * tpart u) • w`
  (`Hyper.hlift_actO` + linearity of `mulVec`);
* reading the time coordinate (which is positive) shows `w (inr 0) ≠ 0` and
  `(tsign A * tpart u) * w (inr 0) = tpart (actO A u)`;
* `smul_theta_of_time_ne_zero` then gives `w = w (inr 0) • θ (bdO A ξ)`, so by the same time
  coordinate `hlift (actO A u) = tpart (actO A u) • θ (bdO A ξ)`;
* comparing spatial coordinates yields `actO A u = tpart (actO A u) • bdO A ξ`, and multiplying by
  the inverse of the (nonzero) scalar concludes.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Matrix

noncomputable section

variable {n : ℕ}

/-- The Klein projection `u ↦ (tpart u)⁻¹ • u` commutes with the `O(n,1)`-action. -/
theorem bdO_klein_smul (A : Submission.Mostow.O1 n) (u : Submission.Mostow.E n) :
    Submission.Mostow.bdO A ((Submission.Mostow.tpart u)⁻¹ • u)
      = (Submission.Mostow.tpart (Submission.Mostow.actO A u))⁻¹ • Submission.Mostow.actO A u := by
  set ξ : Submission.Mostow.E n := (Submission.Mostow.tpart u)⁻¹ • u with hξdef
  set w : Fin n ⊕ Fin 1 → ℝ := (Submission.Mostow.mat A) *ᵥ theta ξ with hwdef
  have h1 : Submission.Mostow.hlift u = Submission.Mostow.tpart u • theta ξ := by
    rw [hξdef]
    funext j
    rcases j with i | k
    · rw [hlift_inl, Pi.smul_apply, theta_inl, PiLp.smul_apply]
      rw [smul_inv_smul₀ (Submission.Mostow.Hyper.tpart_ne_zero u)]
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [hlift_inr, Pi.smul_apply, theta_inr, smul_eq_mul, mul_one]
  have h3 : (Submission.Mostow.mat A) *ᵥ Submission.Mostow.hlift u =
      Submission.Mostow.tpart u • w := by
    rw [h1, Matrix.mulVec_smul, hwdef]
  have h4 : Submission.Mostow.hlift (Submission.Mostow.actO A u) =
      (Submission.Mostow.tsign A * Submission.Mostow.tpart u) • w := by
    rw [Submission.Mostow.Hyper.hlift_actO A u, h3, smul_smul]
  have h4' := congrArg (fun v : Fin n ⊕ Fin 1 → ℝ => v (Sum.inr 0)) h4
  rw [hlift_inr, Pi.smul_apply, smul_eq_mul] at h4'
  have htime : (Submission.Mostow.tsign A * Submission.Mostow.tpart u) * w (Sum.inr 0)
      = Submission.Mostow.tpart (Submission.Mostow.actO A u) := h4'.symm
  have hwt : w (Sum.inr 0) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at htime
    exact absurd htime.symm
      (ne_of_gt (Submission.Mostow.Hyper.tpart_pos (Submission.Mostow.actO A u)))
  have h5 : w = w (Sum.inr 0) • theta (Submission.Mostow.bdO A ξ) :=
    smul_theta_of_time_ne_zero w hwt
  have h6 : Submission.Mostow.hlift (Submission.Mostow.actO A u) =
      Submission.Mostow.tpart (Submission.Mostow.actO A u) •
        theta (Submission.Mostow.bdO A ξ) := by
    rw [h4, h5, smul_smul, htime]
  have hcoef : ∀ i : Fin n, (Submission.Mostow.actO A u).ofLp i
      = Submission.Mostow.tpart (Submission.Mostow.actO A u) *
        (Submission.Mostow.bdO A ξ).ofLp i := by
    intro i
    have h := congrArg (fun v : Fin n ⊕ Fin 1 → ℝ => v (Sum.inl i)) h6
    simpa only [hlift_inl, theta_inl, Pi.smul_apply, smul_eq_mul] using h
  refine PiLp.ext fun i => ?_
  rw [PiLp.smul_apply, hcoef i, smul_eq_mul]
  rw [inv_mul_cancel_left₀ (Submission.Mostow.Hyper.tpart_ne_zero _)]

theorem kleinBD (n : ℕ) (g : LeanEval.Geometry.MostowRigidity.PO n 1) (u : Submission.Mostow.E n) :
    Submission.Mostow.bd g ((Submission.Mostow.tpart u)⁻¹ • u)
      = (Submission.Mostow.tpart (g • u))⁻¹ • (g • u) :=
  bdO_klein_smul (Submission.Mostow.rep g) u

end

end Work.Mostow
