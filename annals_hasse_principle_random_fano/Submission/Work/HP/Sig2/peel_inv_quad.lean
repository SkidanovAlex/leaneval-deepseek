import Mathlib
import Submission.Work.HP.Sig2.GaussPoissonDefs
import Submission.Work.HP.Sig2.PeelDefs
import Submission.Work.HP.Sig2.peel_tail_schur

noncomputable section

open Matrix

namespace Work.HP.Sig2

/-! ## Symmetry helpers -/

/-- Entries of a positive definite real matrix are symmetric. -/
theorem PosDef_apply_symm {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef)
    (i j : Fin (R + 1)) : G i j = G j i := by
  simpa using hG.isHermitian.apply j i

/-- The tail block is symmetric. -/
theorem pTail_symm {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef)
    (i j : Fin R) : pTail G i j = pTail G j i :=
  PosDef_apply_symm hG i.succ j.succ

/-- The tail block is a symmetric matrix. -/
theorem pTail_transpose {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef) :
    (pTail G)ᵀ = pTail G := by
  ext i j
  simp only [transpose_apply]
  exact (pTail_symm hG i j).symm

/-- The inverse of the tail block is symmetric. -/
theorem pTail_inv_symm {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef)
    (i j : Fin R) : (pTail G)⁻¹ i j = (pTail G)⁻¹ j i := by
  have h1 : ((pTail G)⁻¹)ᵀ = (pTail G)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, pTail_transpose hG]
  have h := congrFun (congrFun h1 i) j
  rw [Matrix.transpose_apply] at h
  exact h.symm

/-- The tail block has a unit determinant. -/
theorem pTail_det_isUnit {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef) :
    IsUnit (pTail G).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (pTail_posDef G hG).isUnit

/-- Componentwise form of `pWind G = (pTail G)⁻¹ *ᵥ pVec G`. -/
theorem pWind_apply {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (l : Fin R) :
    pWind G l = ∑ m : Fin R, (pTail G)⁻¹ l m * pVec G m := by
  simp [pWind, Matrix.mulVec_apply, dotProduct]

/-- `∑ m, pVec G m * (pTail G)⁻¹ m l = pWind G l`. -/
theorem sum_pVec_invTail {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef)
    (l : Fin R) : ∑ m : Fin R, pVec G m * (pTail G)⁻¹ m l = pWind G l := by
  rw [pWind_apply G l]
  apply Finset.sum_congr rfl
  intro m _
  rw [pTail_inv_symm hG m l]
  ring

/-- `∑ m, pTail G k m * pWind G m = pVec G k`. -/
theorem sum_tail_pWind {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef)
    (k : Fin R) : ∑ m : Fin R, pTail G k m * pWind G m = pVec G k := by
  have h := congrFun (mulVec_pTail_pWind G hG) k
  simpa [Matrix.mulVec_apply, dotProduct] using h

/-- `∑ m, pTail G k m * (pTail G)⁻¹ m l = 1 k l`. -/
theorem sum_tail_invTail {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef)
    (k l : Fin R) : ∑ m : Fin R, pTail G k m * (pTail G)⁻¹ m l = (1 : Matrix (Fin R) (Fin R) ℝ) k l := by
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv (pTail G) (pTail_det_isUnit hG)) k) l
  simpa [Matrix.mul_apply] using h

/-- `∑ i, pVec G i * pWind G i = pHead G - pSchur G`. -/
theorem sum_pVec_pWind {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef) :
    ∑ i : Fin R, pVec G i * pWind G i = pHead G - pSchur G := by
  rw [pSchur]; ring

/-! ## The candidate inverse -/

/-- Candidate for the inverse `G⁻¹` in block form
`[[1/s, -wᵀ/s], [-w/s, C⁻¹ + w wᵀ/s]]` with `C = pTail G`, `w = pWind G`, `s = pSchur G`. -/
def pInvCand {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) :
    Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ :=
  fun i j =>
    Fin.cases
      (Fin.cases (1 / pSchur G) (fun k => (-(pWind G k)) / pSchur G) j)
      (fun k => Fin.cases ((-(pWind G k)) / pSchur G)
        (fun l => (pTail G)⁻¹ k l + (pWind G k * pWind G l) / pSchur G) j)
      i

@[simp] lemma pInvCand_zero_zero {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) :
    pInvCand G 0 0 = 1 / pSchur G := by simp [pInvCand]

@[simp] lemma pInvCand_zero_succ {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ)
    (j : Fin R) : pInvCand G 0 j.succ = (-(pWind G j)) / pSchur G := by simp [pInvCand]

@[simp] lemma pInvCand_succ_zero {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ)
    (i : Fin R) : pInvCand G i.succ 0 = (-(pWind G i)) / pSchur G := by simp [pInvCand]

@[simp] lemma pInvCand_succ_succ {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ)
    (i j : Fin R) :
    pInvCand G i.succ j.succ = (pTail G)⁻¹ i j + (pWind G i * pWind G j) / pSchur G := by
  simp [pInvCand]

/-! ## The candidate really is the inverse -/

theorem mul_pInvCand_00 {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef) :
    (G * pInvCand G) 0 0 = 1 := by
  have hD : (∑ k : Fin R, G 0 k.succ * pWind G k) = G 0 0 - pSchur G := by
    simpa only [pVec, pHead] using sum_pVec_pWind (G := G) hG
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [pInvCand_zero_zero, pInvCand_succ_zero]
  have hsum : (∑ k : Fin R, G 0 k.succ * ((-(pWind G k)) / pSchur G))
      = -((∑ k : Fin R, G 0 k.succ * pWind G k) / pSchur G) := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [hsum, hD]
  have hs : pSchur G ≠ 0 := ne_of_gt (peel_tail_schur G hG).2
  field_simp
  ring

theorem mul_pInvCand_01 {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef)
    (l : Fin R) : (G * pInvCand G) 0 l.succ = 0 := by
  have hA : (∑ k : Fin R, G 0 k.succ * (pTail G)⁻¹ k l) = pWind G l := by
    simpa only [pVec] using sum_pVec_invTail (G := G) hG l
  have hD : (∑ k : Fin R, G 0 k.succ * pWind G k) = G 0 0 - pSchur G := by
    simpa only [pVec, pHead] using sum_pVec_pWind (G := G) hG
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [pInvCand_zero_succ, pInvCand_succ_succ, mul_add, Finset.sum_add_distrib]
  have hs2 : (∑ k : Fin R, G 0 k.succ * ((pWind G k * pWind G l) / pSchur G))
      = (∑ k : Fin R, G 0 k.succ * pWind G k) * pWind G l / pSchur G := by
    rw [Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [hA, hs2, hD]
  have hs : pSchur G ≠ 0 := ne_of_gt (peel_tail_schur G hG).2
  field_simp
  ring

theorem mul_pInvCand_10 {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef)
    (k : Fin R) : (G * pInvCand G) k.succ 0 = 0 := by
  have hB : (∑ m : Fin R, G k.succ m.succ * pWind G m) = G 0 k.succ := by
    simpa only [pTail, pVec] using sum_tail_pWind (G := G) hG k
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  rw [PosDef_apply_symm (G := G) hG k.succ 0]
  simp only [pInvCand_zero_zero, pInvCand_succ_zero]
  have hsum : (∑ m : Fin R, G k.succ m.succ * ((-(pWind G m)) / pSchur G))
      = -((∑ m : Fin R, G k.succ m.succ * pWind G m) / pSchur G) := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro m _; ring
  rw [hsum, hB]
  have hs : pSchur G ≠ 0 := ne_of_gt (peel_tail_schur G hG).2
  field_simp
  ring

theorem mul_pInvCand_11 {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef)
    (k l : Fin R) : (G * pInvCand G) k.succ l.succ = (1 : Matrix (Fin R) (Fin R) ℝ) k l := by
  have hC : (∑ m : Fin R, G k.succ m.succ * (pTail G)⁻¹ m l) = (1 : Matrix (Fin R) (Fin R) ℝ) k l := by
    simpa only [pTail] using sum_tail_invTail (G := G) hG k l
  have hB : (∑ m : Fin R, G k.succ m.succ * pWind G m) = G 0 k.succ := by
    simpa only [pTail, pVec] using sum_tail_pWind (G := G) hG k
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  rw [PosDef_apply_symm (G := G) hG k.succ 0]
  simp only [pInvCand_zero_succ, pInvCand_succ_succ, mul_add, Finset.sum_add_distrib]
  have hs2 : (∑ m : Fin R, G k.succ m.succ * ((pWind G m * pWind G l) / pSchur G))
      = (∑ m : Fin R, G k.succ m.succ * pWind G m) * pWind G l / pSchur G := by
    rw [Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl; intro m _; ring
  rw [hC, hs2, hB]
  have hs : pSchur G ≠ 0 := ne_of_gt (peel_tail_schur G hG).2
  field_simp
  ring

theorem mul_pInvCand {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef) :
    G * pInvCand G = 1 := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · refine Fin.cases ?_ (fun l => ?_) j
    · simpa [Matrix.one_apply, mul_pInvCand_00 hG]
    · simp only [mul_pInvCand_01 hG l,
        Matrix.one_apply_ne (show (0 : Fin (R + 1)) ≠ l.succ from fun h => Fin.succ_ne_zero l h.symm)]
  · refine Fin.cases ?_ (fun l => ?_) j
    · simpa [Matrix.one_apply, Fin.succ_ne_zero, mul_pInvCand_10 hG k]
    · simpa [Matrix.one_apply, Fin.succ_inj, mul_pInvCand_11 hG k l]

theorem inv_eq_pInvCand {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef) :
    G⁻¹ = pInvCand G :=
  Matrix.inv_eq_right_inv (mul_pInvCand hG)

/-! ## The quadratic form of the inverse -/

theorem qForm_pInvCand {R : ℕ} {G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ} (hG : G.PosDef)
    (v : Fin (R + 1) → ℝ) :
    qForm (pInvCand G) v = ((v 0 - ∑ i, pWind G i * v i.succ) ^ 2) / pSchur G
      + qForm (pTail G)⁻¹ (fun i => v i.succ) := by
  have hs : pSchur G ≠ 0 := ne_of_gt (peel_tail_schur G hG).2
  set T : ℝ := ∑ i : Fin R, pWind G i * v i.succ with hT
  simp only [qForm]
  set Q : ℝ := ∑ i : Fin R, ∑ j : Fin R, v i.succ * (pTail G)⁻¹ i j * v j.succ with hQ
  -- factorizations
  have h2 : (∑ l : Fin R, v 0 * ((-(pWind G l)) / pSchur G) * v l.succ)
      = -((v 0 * T) / pSchur G) := by
    rw [hT, Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro l _; ring
  have h3 : (∑ k : Fin R, v k.succ * ((-(pWind G k)) / pSchur G) * v 0)
      = -((v 0 * T) / pSchur G) := by
    rw [hT, Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have h5 : (∑ k : Fin R, ∑ l : Fin R, v k.succ * ((pWind G k * pWind G l) / pSchur G) * v l.succ)
      = T * T / pSchur G := by
    rw [hT, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro l _
    ring
  simp only [Fin.sum_univ_succ]
  simp only [pInvCand_zero_zero, pInvCand_zero_succ, pInvCand_succ_zero, pInvCand_succ_succ]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  rw [← hQ]
  rw [h2, h3, h5]
  field_simp
  ring

/-! ## The peel identity for the inverse -/

theorem peel_inv_quad {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (hG : G.PosDef)
    (v : Fin (R + 1) → ℝ) :
    qForm G⁻¹ v = ((v 0 - ∑ i, pWind G i * v i.succ) ^ 2) / pSchur G
      + qForm (pTail G)⁻¹ (fun i => v i.succ) := by
  rw [inv_eq_pInvCand hG]
  exact qForm_pInvCand hG v

end Work.HP.Sig2
