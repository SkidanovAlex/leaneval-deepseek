import Mathlib
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.poAction

/-!
# `emat` is multiplicative, invertible and detects orientation

The *effective matrix* `emat g = tsign (rep g) • mat (rep g)` of `g : PO(n,1)` is the linear
representation of `g` on the hyperboloid lift of `ℍⁿ` (`Work.Mostow.ematSpec`).  Here we record
its compatibility with the group structure of `PO(n,1)`:

* `emat (g * h) = emat g * emat h`, `emat 1 = 1`, `emat g⁻¹ = (emat g)⁻¹`;
* `(emat g).det = (mat (rep g)).det` (for `n = 3` the matrices are `4 × 4`, so multiplying by
  the scalar `tsign (rep g) = ±1` does not change the determinant);
* consequently `IsOriented g ↔ 0 < (emat g).det`.

The matrices are compared through their action on the hyperboloid lifts `hlift u`, which span
`ℝ^{n+1}`; this is the content of `eq_of_mulVec_hlift_eq` below.  The action law
`(g * h) • u = g • (h • u)` is the only geometric input and is taken from `POActionProp`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity Matrix

noncomputable section

variable {n : ℕ}

/-- The lifts `hlift u` of chart points span `ℝ^{n+1}`: indeed `hlift 0 = Pi.single (inr 0) 1`
and `hlift (single i 1) - √2 • hlift 0 = Pi.single (inl i) 1`.  Hence a matrix is determined by
its action on the set `{hlift u}`. -/
lemma eq_of_mulVec_hlift_eq {M N : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ}
    (h : ∀ u : E n, M *ᵥ hlift u = N *ᵥ hlift u) : M = N := by
  have hcol : ∀ b : Fin n ⊕ Fin 1,
      M *ᵥ Pi.single b (1 : ℝ) = N *ᵥ Pi.single b (1 : ℝ) := by
    intro b
    rcases b with i | k
    · have h1 := h (EuclideanSpace.single i (1 : ℝ))
      have h0 := h (0 : E n)
      rw [← Work.Mostow.hlift_single_sub i, Matrix.mulVec_sub, Matrix.mulVec_sub,
        Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h0]
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [← Work.Mostow.hlift_zero]
      exact h 0
  ext a b
  have h2 := congrFun (hcol b) a
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using h2

theorem ematMulDet :
    (∀ g h : LeanEval.Geometry.MostowRigidity.PO 3 1,
        Work.Mostow.emat (g * h) = Work.Mostow.emat g * Work.Mostow.emat h) ∧
      Work.Mostow.emat (1 : LeanEval.Geometry.MostowRigidity.PO 3 1) = 1 ∧
      (∀ g : LeanEval.Geometry.MostowRigidity.PO 3 1,
        Work.Mostow.emat g⁻¹ = (Work.Mostow.emat g)⁻¹) ∧
      (∀ g : LeanEval.Geometry.MostowRigidity.PO 3 1,
        (Work.Mostow.emat g).det = (Submission.Mostow.mat (Submission.Mostow.rep g)).det) ∧
      (∀ g : LeanEval.Geometry.MostowRigidity.PO 3 1,
        Work.Mostow.IsOriented g ↔ 0 < (Work.Mostow.emat g).det) := by
  have hP := Work.Mostow.poAction 3 (by norm_num)
  have hmulAct : ∀ (g h : PO 3 1) (u : E 3), (g * h) • u = g • (h • u) := hP.2.2.2.2.1
  have honeAct : ∀ u : E 3, (1 : PO 3 1) • u = u := hP.2.2.2.1
  have h1 : ∀ g h : PO 3 1, emat (g * h) = emat g * emat h := by
    intro g h
    refine eq_of_mulVec_hlift_eq fun u => ?_
    calc emat (g * h) *ᵥ hlift u = hlift ((g * h) • u) := (Work.Mostow.ematSpec (g * h)).1 u
      _ = hlift (g • (h • u)) := by rw [hmulAct g h u]
      _ = emat g *ᵥ hlift (h • u) := ((Work.Mostow.ematSpec g).1 (h • u)).symm
      _ = emat g *ᵥ (emat h *ᵥ hlift u) := by rw [(Work.Mostow.ematSpec h).1 u]
      _ = (emat g * emat h) *ᵥ hlift u := Matrix.mulVec_mulVec (hlift u) (emat g) (emat h)
  have h2 : emat (1 : PO 3 1) = 1 := by
    refine eq_of_mulVec_hlift_eq fun u => ?_
    rw [(Work.Mostow.ematSpec (1 : PO 3 1)).1 u, honeAct u, Matrix.one_mulVec]
  have h3 : ∀ g : PO 3 1, emat g⁻¹ = (emat g)⁻¹ := by
    intro g
    have hg : emat g * emat g⁻¹ = 1 := by rw [← h1 g g⁻¹, mul_inv_cancel, h2]
    exact (Matrix.inv_eq_right_inv hg).symm
  have h4 : ∀ g : PO 3 1, (emat g).det = (mat (rep g)).det := by
    intro g
    rcases tsign_eq_one_or (rep g) with ht | ht
    · rw [Work.Mostow.emat, ht, one_smul]
    · rw [Work.Mostow.emat, ht, neg_one_smul, Matrix.det_neg, Fintype.card_sum,
        Fintype.card_fin]
      norm_num
  refine ⟨h1, h2, h3, h4, ?_⟩
  · intro g
    unfold Work.Mostow.IsOriented
    rw [h4 g]

end

end Work.Mostow.gapA
