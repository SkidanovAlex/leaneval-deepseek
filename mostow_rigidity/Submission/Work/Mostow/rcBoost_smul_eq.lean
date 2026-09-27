import Mathlib
import Submission.Work.Mostow.poAction_ge1
import Submission.Work.Mostow.HaarBoost
import Submission.Work.Mostow.poAction_hypIso_zero

/-!
# The boost acts by the Lorentz boost formula

`Work.Mostow.boost q` is the `O(n,1)`-matrix of the hyperbolic boost sending `hlift 0` to `hlift q`.
This file computes its action on a chart point `v`:

`(boost q) • v = v + ((1 + tpart q)⁻¹ * ⟪q, v⟫) • q + tpart v • q`,

which is exactly the image of `hlift v` under the boost matrix in the hyperboloid model
(the `n`-component of `(bmat q) *ᵥ hlift v`), pulled back to the chart.

The only non-definitional ingredient is that the `PO n 1`-action is given by `actO` on any
matrix representative, i.e. clause 2 of `POActionProp`; that Prop is available in every
dimension (`Work.Mostow.poAction_ge1` for `n ≥ 1` and `Work.Mostow.poAction_zero` for `n = 0`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-- `POActionProp` holds in every dimension: the two area lemmas `poAction_zero` (`n = 0`) and
`poAction_ge1` (`n ≥ 1`) cover all cases. -/
theorem poActionProp_all (n : ℕ) : POActionProp n := by
  rcases n with _ | k
  · exact poAction_zero
  · exact poAction_ge1 (k + 1) (Nat.succ_le_succ (Nat.zero_le k))

/-- The `n`-spatial component of the boost matrix applied to `hlift v`. -/
lemma bmat_mulVec_hlift_inl (q v : E n) (i : Fin n) :
    ((bmat q).mulVec (hlift v)) (Sum.inl i)
      = v i + (1 + tpart q)⁻¹ * (inner ℝ q v) * q i + tpart v * q i := by
  rw [bmat_mulVec_inl]
  simp only [hlift_inl, hlift_inr]
  rw [inner_eq_sum]
  ring

theorem rcBoost_smul_eq {n : ℕ} (q v : Submission.Mostow.E n) :
    ((Work.Mostow.boost q : Submission.Mostow.O1 n) : LeanEval.Geometry.MostowRigidity.PO n 1) • v
      = v + ((1 + Submission.Mostow.tpart q)⁻¹ * inner ℝ q v) • q + Submission.Mostow.tpart v • q := by
  obtain ⟨-, hA2, -⟩ := poActionProp_all n
  rw [hA2]
  simp only [actO, mat_boost, tsign_boost, one_mul]
  ext i
  rw [WithLp.ofLp_toLp]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [bmat_mulVec_hlift_inl]

end Work.Mostow
