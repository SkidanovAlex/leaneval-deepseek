import Mathlib
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.bmat_mem

/-!
# The hyperbolic boost (area B, `haarBridge`)

`bmat v` is the `O(n,1)`-matrix of the hyperbolic boost sending `e₀ = hlift 0` to `hlift v`,
and `boost v` is the corresponding element of `PO n 1`.  The fibre of the orbit map
`g ↦ g • 0` over `v` is `(boost v) • Ksub`, which is what makes that map proper.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Topology
open Matrix

noncomputable section

variable {n : ℕ}

/-- The column block `v i` of the boost matrix. -/
def colb (v : E n) : Matrix (Fin n) (Fin 1) ℝ := vecMulVec v (fun _ : Fin 1 => 1)

/-- The row block `v j` of the boost matrix. -/
def rowb (v : E n) : Matrix (Fin 1) (Fin n) ℝ := vecMulVec (fun _ : Fin 1 => 1) v

lemma bmat_eq_blocks' (v : E n) :
    bmat v = fromBlocks
      (1 + (1 + tpart v)⁻¹ • vecMulVec v v) (colb v) (rowb v)
      (tpart v • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  rw [bmat, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
      Matrix.vecMulVec_apply, Fin.sum_univ_one]
    ring
  · ext i j
    simp [colb, Matrix.replicateCol_apply, Matrix.vecMulVec_apply]
  · ext i j
    simp [rowb, Matrix.replicateRow_apply, Matrix.vecMulVec_apply]
  · rfl

/-! ## Entries of `mulVec` by the blocks -/

lemma vecMulVec_mulVec_apply (v : E n) (y : Fin n → ℝ) (i : Fin n) :
    ((vecMulVec v v).mulVec y) i = v i * ∑ j, v j * y j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.vecMulVec_apply]
  ring

lemma add_smul_mat_mulVec_apply (c : ℝ) (v : E n) (y : Fin n → ℝ) (i : Fin n) :
    (((1 : Matrix (Fin n) (Fin n) ℝ) + c • vecMulVec v v).mulVec y) i =
      y i + c * (v i * ∑ j, v j * y j) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [vecMulVec_mulVec_apply]

lemma colb_mulVec_apply (v : E n) (w : Fin 1 → ℝ) (i : Fin n) :
    ((colb v).mulVec w) i = v i * w 0 := by
  simp only [colb, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.vecMulVec_apply]
  ring

lemma rowb_mulVec_apply (v : E n) (y : Fin n → ℝ) :
    ((rowb v).mulVec y) 0 = ∑ j, v j * y j := by
  simp only [rowb, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [Matrix.vecMulVec_apply]; ring

lemma smul_one_mulVec_apply (t : ℝ) (w : Fin 1 → ℝ) :
    ((t • (1 : Matrix (Fin 1) (Fin 1) ℝ)).mulVec w) 0 = t * w 0 := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]

/-! ## The vector form of the boost -/

lemma bmat_mulVec_inl (v : E n) (x : Fin n ⊕ Fin 1 → ℝ) (i : Fin n) :
    ((bmat v).mulVec x) (Sum.inl i) =
      x (Sum.inl i) + (1 + tpart v)⁻¹ * (v i * (∑ j, v j * x (Sum.inl j)))
        + v i * x (Sum.inr 0) := by
  rw [bmat_eq_blocks', Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inl, Pi.add_apply]
  rw [add_smul_mat_mulVec_apply, colb_mulVec_apply]
  simp only [Function.comp_apply]

lemma bmat_mulVec_inr (v : E n) (x : Fin n ⊕ Fin 1 → ℝ) :
    ((bmat v).mulVec x) (Sum.inr 0) = (∑ j, v j * x (Sum.inl j)) + tpart v * x (Sum.inr 0) := by
  rw [bmat_eq_blocks', Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inr, Pi.add_apply]
  rw [rowb_mulVec_apply, smul_one_mulVec_apply]
  simp only [Function.comp_apply]

lemma bmat_mulVec_hlift_zero (v : E n) : (bmat v).mulVec (hlift (0 : E n)) = hlift v := by
  ext a
  rcases a with i | j
  · rw [bmat_mulVec_inl, hlift_zero]
    simp only [Pi.single_eq_of_ne Sum.inl_ne_inr, mul_zero, Finset.sum_const_zero, add_zero,
      Pi.single_eq_same, mul_one, hlift_inl, zero_add]
  · obtain rfl : j = 0 := Subsingleton.elim j 0
    rw [bmat_mulVec_inr, hlift_zero]
    simp only [Pi.single_eq_of_ne Sum.inl_ne_inr, mul_zero, Finset.sum_const_zero, zero_add,
      Pi.single_eq_same, mul_one, hlift_inr]

/-! ## The boost preserves the Minkowski form -/

lemma dotProduct_self (v : E n) : v ⬝ᵥ v = ‖v‖ ^ 2 := by
  rw [dotProduct, norm_sq_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma vecMulVec_symm (v : E n) : (vecMulVec v v)ᵀ = vecMulVec v v := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.vecMulVec_apply]
  ring

lemma vecMulVec_sq (v : E n) : vecMulVec v v * vecMulVec v v = (‖v‖ ^ 2) • vecMulVec v v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  trans ∑ k, v i * v j * (v k * v k)
  · exact Finset.sum_congr rfl fun k _ => by ring
  · rw [← Finset.mul_sum, show (∑ k, v k * v k) = ∑ k, v k ^ 2 from
      Finset.sum_congr rfl fun k _ => by ring, ← norm_sq_eq_sum]
    ring

lemma rowb_eq_colb_transpose (v : E n) : rowb v = (colb v)ᵀ := by
  ext i j
  simp only [Matrix.transpose_apply, colb, rowb, Matrix.vecMulVec_apply, mul_one, one_mul]

lemma colb_mul_rowb (v : E n) : colb v * rowb v = vecMulVec v v := by
  ext i j
  simp only [Matrix.mul_apply, colb, rowb, Matrix.vecMulVec_apply, Fin.sum_univ_one, mul_one,
    one_mul]

lemma rowb_mul_colb (v : E n) :
    rowb v * colb v = (‖v‖ ^ 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  simp only [Matrix.mul_apply, rowb, colb, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, mul_one, one_mul]
  rw [show (∑ k, v k * v k) = ‖v‖ ^ 2 from dotProduct_self v,
    if_pos (Subsingleton.elim i j), mul_one]

lemma vecMulVec_v_colb (v : E n) : vecMulVec v v * colb v = (‖v‖ ^ 2) • colb v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, colb, Matrix.smul_apply, smul_eq_mul,
    Fin.sum_univ_one, mul_one]
  trans v i * ∑ k, v k * v k
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [show (∑ k, v k * v k) = ‖v‖ ^ 2 from dotProduct_self v]
    ring

lemma rowb_mul_vecMulVec (v : E n) : rowb v * vecMulVec v v = (‖v‖ ^ 2) • rowb v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, rowb, Matrix.smul_apply, smul_eq_mul,
    Fin.sum_univ_one, mul_one]
  trans ∑ k, (v k * v k) * v j
  · exact Finset.sum_congr rfl fun k _ => by ring
  · rw [← Finset.sum_mul, show (∑ k, v k * v k) = ‖v‖ ^ 2 from dotProduct_self v]
    ring

private lemma inv_mul_norm_sq (v : E n) : (1 + tpart v)⁻¹ * ‖v‖ ^ 2 = tpart v - 1 := by
  have h1 : (1 + tpart v) ≠ 0 := by have := tpart_pos v; positivity
  have hN : ‖v‖ ^ 2 = (tpart v) ^ 2 - 1 := by rw [tpart_sq]; ring
  rw [hN]; field_simp; ring

private lemma one_add_inv_mul_norm_sq (v : E n) : 1 + (1 + tpart v)⁻¹ * ‖v‖ ^ 2 = tpart v := by
  rw [inv_mul_norm_sq]; ring

private lemma two_inv_add_inv_sq (v : E n) :
    2 * (1 + tpart v)⁻¹ + (1 + tpart v)⁻¹ ^ 2 * ‖v‖ ^ 2 = 1 := by
  have h1 : (1 + tpart v) ≠ 0 := by have := tpart_pos v; positivity
  have hN : ‖v‖ ^ 2 = (tpart v) ^ 2 - 1 := by rw [tpart_sq]; ring
  rw [hN]; field_simp; ring

/-! ## The four block identities -/

/-- The hyperbolic boost as an element of `O(n,1)`. -/
def boost (v : E n) : O1 n := ⟨bmat v, bmat_mem n v⟩

@[simp] theorem mat_boost (v : E n) : mat (boost v) = bmat v := rfl

theorem tsign_boost (v : E n) : tsign (boost v) = 1 := by
  rw [tsign_eq_one_iff, mat_boost, bmat_eq_blocks', Matrix.fromBlocks_apply₂₂]
  simpa using tpart_pos v

/-- The boost moves `0` to `v`. -/
theorem boost_smul_zero (hA : POActionProp n) (v : E n) :
    ((boost v : O1 n) : PO n 1) • (0 : E n) = v := by
  obtain ⟨-, hA2, -⟩ := hA
  rw [hA2, actO, mat_boost, tsign_boost, bmat_mulVec_hlift_zero]
  ext i
  simp [hlift_inl]

/-- Continuity of the boost matrix. -/
theorem continuous_bmat (n : ℕ) : Continuous (fun v : E n => bmat v) := by
  have ht : Continuous (tpart : E n → ℝ) := continuous_tpart
  apply continuous_matrix
  intro i j
  rcases i with a | i' <;> rcases j with b | j'
  · rw [show (fun v : E n => bmat v (Sum.inl a) (Sum.inl b)) = fun v =>
        (if a = b then (1 : ℝ) else 0) + (1 + tpart v)⁻¹ * (v a * v b) from by
      funext v; rw [bmat_eq_blocks']; simp [Matrix.fromBlocks_apply₁₁, Matrix.one_apply,
        Matrix.vecMulVec_apply]]
    refine Continuous.add continuous_const ?_
    have hinv : Continuous fun v : E n => (1 + tpart v)⁻¹ :=
      (((continuous_const : Continuous fun _ : E n => (1 : ℝ))).add ht).inv₀
        fun w => by
          have h := tpart_pos w
          simp only [Pi.add_apply]
          exact ne_of_gt (by linarith)
    refine Continuous.mul hinv ?_
    exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) a).mul
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) b)
  · rw [show (fun v : E n => bmat v (Sum.inl a) (Sum.inr j')) = fun v => v a from by
      funext v; rw [bmat_eq_blocks']; simp [Matrix.fromBlocks_apply₁₂, colb,
        Matrix.vecMulVec_apply]]
    exact PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) a
  · rw [show (fun v : E n => bmat v (Sum.inr i') (Sum.inl b)) = fun v => v b from by
      funext v; rw [bmat_eq_blocks']; simp [Matrix.fromBlocks_apply₂₁, rowb,
        Matrix.vecMulVec_apply]]
    exact PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) b
  · rw [show (fun v : E n => bmat v (Sum.inr i') (Sum.inr j')) = fun v => tpart v from by
      funext v; rw [bmat_eq_blocks']
      simp [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Subsingleton.elim i' j']]
    exact ht

/-- Continuity of the boost. -/
theorem continuous_boost (n : ℕ) : Continuous (fun v : E n => ((boost v : O1 n) : PO n 1)) :=
  continuous_quotient_mk'.comp ((continuous_bmat n).subtype_mk fun v => bmat_mem n v)

end

end Work.Mostow
