import Mathlib
import Submission.Work.HP.Sig2.GaussPoissonDefs

/-!
# Peeling the Gaussian Poisson setup: the tail block and the Schur complement

For a positive definite real matrix `G` indexed by `Fin (R+1)` we show that the bottom-right block
`pTail G` is again positive definite and that the scalar Schur complement
`pSchur G = pHead G - ∑ i, pVec G i * pWind G i` is strictly positive.

The key point is that the completion of squares
`pSchur G = qForm G (Fin.cons 1 (fun i => - pWind G i))`
expresses the Schur complement as the value of the quadratic form of `G` at the non-zero vector
`(1, -pWind G)`, hence it is positive.
-/

noncomputable section

open Matrix

namespace Work.HP.Sig2

/-- The bottom-right block of a positive definite matrix is positive definite. -/
theorem pTail_posDef {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (hG : G.PosDef) :
    (pTail G).PosDef :=
  hG.submatrix (Fin.succ_injective R)

/-- `pWind G` really is the solution of `pTail G *ᵥ w = pVec G`. -/
theorem mulVec_pTail_pWind {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (hG : G.PosDef) :
    pTail G *ᵥ pWind G = pVec G := by
  have hdet : IsUnit (pTail G).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (pTail_posDef G hG).isUnit
  rw [pWind, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- The `0`-th component of `G *ᵥ (1, -pWind G)` is the Schur complement. -/
theorem mulVec_pWind_cons_zero {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ)
    (_hG : G.PosDef) :
    (G *ᵥ (Fin.cons (1:ℝ) (fun i => - pWind G i))) 0 = pSchur G := by
  rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_one]
  simp only [pSchur, pHead, pVec]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-- Every other component of `G *ᵥ (1, -pWind G)` vanishes, using symmetry of `G`. -/
theorem mulVec_pWind_cons_succ {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ)
    (hG : G.PosDef) (i : Fin R) :
    (G *ᵥ (Fin.cons (1:ℝ) (fun i => - pWind G i))) i.succ = 0 := by
  rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_one]
  have hsum : ∑ k, G i.succ k.succ * (- pWind G k) = - (pVec G) i := by
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [← mulVec_pTail_pWind G hG]
    rfl
  rw [hsum]
  have hsym : G i.succ 0 = G 0 i.succ := by
    simpa using (hG.isHermitian.apply i.succ 0).symm
  rw [hsym, pVec]
  ring

/-- Completion of squares: the Schur complement is the value of the quadratic form of `G`
at the non-zero vector `(1, -pWind G)`. -/
theorem qForm_pWind_cons {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (hG : G.PosDef) :
    qForm G (Fin.cons (1:ℝ) (fun i => - pWind G i)) = pSchur G := by
  rw [qForm_eq_dotProduct, dotProduct, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [mulVec_pWind_cons_zero G hG]
  have hsum0 : ∑ i : Fin R,
      (- pWind G i) * (G *ᵥ (Fin.cons (1:ℝ) (fun i => - pWind G i))) i.succ = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [mulVec_pWind_cons_succ G hG i, mul_zero]
  rw [hsum0, add_zero, one_mul]

theorem peel_tail_schur {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (hG : G.PosDef) :
    (pTail G).PosDef ∧ 0 < pSchur G := by
  refine ⟨pTail_posDef G hG, ?_⟩
  have hv : (Fin.cons (1:ℝ) (fun i => - pWind G i) : Fin (R + 1) → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hpos : 0 < qForm G (Fin.cons (1:ℝ) (fun i => - pWind G i)) := by
    rw [qForm_eq_dotProduct]
    simpa using hG.dotProduct_mulVec_pos hv
  rwa [qForm_pWind_cons G hG] at hpos

end Work.HP.Sig2
