import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.StabHoroForm

/-!
# The lift of `PO(n,1)` to `O(n,1)`

Every `g : PO n 1` has a representative matrix `LambdaMat g = tsign (out g) • mat (out g)`
that preserves the upper sheet of the hyperboloid, so that
`hlift (g • u) = LambdaMat g *ᵥ hlift u`.  The lift is multiplicative.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- `A *ᵥ ·` as a linear map. -/
def mulVecLin (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :
    (Fin n ⊕ Fin 1 → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin 1 → ℝ) where
  toFun v := A *ᵥ v
  map_add' v w := Matrix.mulVec_add A v w
  map_smul' c v := Matrix.mulVec_smul A c v

@[simp] lemma mulVecLin_apply (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (v : Fin n ⊕ Fin 1 → ℝ) : mulVecLin A v = A *ᵥ v := rfl

/-- Two matrices acting the same way on all chart points are equal. -/
lemma Matrix.ext_of_hlift {A B : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ}
    (h : ∀ u : E n, A *ᵥ hlift u = B *ᵥ hlift u) : A = B := by
  have hall : ∀ x : Fin n ⊕ Fin 1 → ℝ, A *ᵥ x = B *ᵥ x := by
    let S : Submodule ℝ (Fin n ⊕ Fin 1 → ℝ) :=
      { carrier := {x | A *ᵥ x = B *ᵥ x}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq, Matrix.mulVec_add]
          rw [hx, hy]
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_setOf_eq, Matrix.mulVec_smul]
          rw [hx] }
    have hsub : Submodule.span ℝ (Set.range (hlift : E n → Fin n ⊕ Fin 1 → ℝ)) ≤ S := by
      rw [Submodule.span_le]
      rintro y ⟨u, rfl⟩
      exact h u
    intro x
    exact hsub (by rw [hlift_span_top]; trivial)
  ext i j
  have h2 := hall (Pi.single j (1 : ℝ))
  have h3 : (A *ᵥ (Pi.single j (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)) i
      = (B *ᵥ (Pi.single j (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)) i := by rw [h2]
  simpa [Matrix.mulVec_single_one] using h3

/-- The representative matrix of `g ∈ PO(n,1)` preserving the upper sheet. -/
def LambdaMat (g : PO n 1) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  tsign (Quotient.out g) • mat (Quotient.out g)

lemma LambdaMat_isJOrth (g : PO n 1) : IsJOrth (LambdaMat g) := by
  rw [IsJOrth, LambdaMat, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, tsign_sq, one_smul]
  exact O1_form_col (Quotient.out g)

lemma LambdaMat_isJOrth_row (g : PO n 1) :
    (LambdaMat g) * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * (LambdaMat g)ᵀ
      = pmOneMat := by
  rw [LambdaMat, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, tsign_sq, one_smul]
  exact O1_form_row (Quotient.out g)

/-- The action of `g` on the hyperboloid is given by the matrix `LambdaMat g`. -/
lemma hlift_LambdaMat (hA : POActionProp n) (g : PO n 1) (u : E n) :
    hlift (g • u) = LambdaMat g *ᵥ hlift u := by
  obtain ⟨-, hact, -⟩ := hA
  have hg : ((Quotient.out g : O1 n) : PO n 1) = g := Quotient.out_eq g
  have h := hact (Quotient.out g) u
  rw [hg] at h
  rw [h, Submission.Mostow.Hyper.hlift_actO (Quotient.out g) u, LambdaMat,
    Matrix.smul_mulVec]

/-- The lift is multiplicative. -/
lemma LambdaMat_mul (hA : POActionProp n) (g h : PO n 1) :
    LambdaMat (g * h) = LambdaMat g * LambdaMat h := by
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  apply Matrix.ext_of_hlift
  intro u
  rw [← hlift_LambdaMat hA (g * h) u, hmul g h u]
  rw [hlift_LambdaMat hA g (h • u), hlift_LambdaMat hA h u, ← Matrix.mulVec_mulVec]

/-- The lift of the identity is the identity. -/
lemma LambdaMat_one (hA : POActionProp n) : LambdaMat (1 : PO n 1) = 1 := by
  have hmem : (Quotient.out (1 : PO n 1) : O1 n) ∈ Subgroup.center (O1 n) := by
    rw [← QuotientGroup.eq_one_iff]
    exact Quotient.out_eq (1 : PO n 1)
  have hc : (Quotient.out (1 : PO n 1) : O1 n) = 1 ∨ (Quotient.out (1 : PO n 1) : O1 n) = -1 :=
    (hA.1 (Quotient.out (1 : PO n 1))).mp hmem
  rcases hc with h | h
  · rw [LambdaMat, h, mat_one]
    have ht : tsign (1 : O1 n) = 1 := by rw [tsign_eq_one_iff]; simp [mat_one]
    rw [ht, one_smul]
  · rw [LambdaMat, h, mat_neg, mat_one]
    have ht : tsign (-1 : O1 n) = -1 := by rw [tsign_eq_neg_one_iff]; simp
    rw [ht]
    simp

lemma LambdaMat_inv (hA : POActionProp n) (g : PO n 1) :
    LambdaMat g * LambdaMat g⁻¹ = 1 := by
  rw [← LambdaMat_mul hA, mul_inv_cancel, LambdaMat_one hA]

end
end Work.Mostow
