import Mathlib
import Submission.Work.HP.Sig2.GaussPoissonDefs

/-!
# Completing the square for the peeled quadratic form

For a positive-definite real matrix `G` indexed by `Fin (R+1)`, write it in the block form
`[[a, bᵀ], [b, C]]` with `a = pHead G`, `b = pVec G`, `C = pTail G`. Then the quadratic form
`qForm G x = xᵀ G x` can be completed into the square of the "winding" vector
`pWind G = C⁻¹ b`:

`qForm G x = qForm (pTail G) (fun i => x i.succ + x 0 * pWind G i) + pSchur G * (x 0)^2`

where `pSchur G = a - bᵀ C⁻¹ b` is the Schur complement. This is the identity used in the
`elaborating the Poisson summation recursion for the 0-phase Gaussian.

The proof splits the quadratic form at the index `0` (`qForm_head_tail`) and then linearises
the shifted tail (`qForm_tail_schur`), using `pTail G *ᵥ pWind G = pVec G` and the symmetry of
`pTail G`.
-/

open Matrix
open scoped Matrix

namespace Work.HP.Sig2

/-- Splitting the quadratic form `qForm G x` into its `0`-component and its tail. -/
lemma qForm_head_tail {R : ℕ} (G : Matrix (Fin (R+1)) (Fin (R+1)) ℝ) (hG : G.PosDef)
    (x : Fin (R+1) → ℝ) :
    qForm G x = pHead G * (x 0)^2 + 2 * (x 0) * (pVec G ⬝ᵥ fun i => x i.succ)
      + qForm (pTail G) (fun i => x i.succ) := by
  set u : Fin R → ℝ := fun i => x i.succ with hu
  have hsymm : ∀ i j, G i j = G j i := by
    have hsymT : Gᵀ = G := by simpa using hG.isHermitian.eq
    intro i j
    have h := congrFun (congrFun hsymT j) i
    simpa [Matrix.transpose_apply] using h
  have hsplit : x ⬝ᵥ (G *ᵥ x)
      = x 0 * (G *ᵥ x) 0 + ∑ i : Fin R, x i.succ * (G *ᵥ x) i.succ := by
    rw [dotProduct, Fin.sum_univ_succ]
  have h0 : (G *ᵥ x) 0 = pHead G * x 0 + pVec G ⬝ᵥ u := by
    simp only [hu, Matrix.mulVec_apply_eq_sum, dotProduct, pHead, pVec, Fin.sum_univ_succ]
  have hsucc : ∀ i : Fin R, (G *ᵥ x) i.succ = pVec G i * x 0 + (pTail G *ᵥ u) i := by
    intro i
    simp only [hu, Matrix.mulVec_apply_eq_sum, pVec, pTail, Fin.sum_univ_succ]
    rw [hsymm i.succ 0]
  have hsum : (∑ i : Fin R, x i.succ * (pVec G i * x 0 + (pTail G *ᵥ u) i))
      = x 0 * (pVec G ⬝ᵥ u) + u ⬝ᵥ (pTail G *ᵥ u) := by
    simp only [dotProduct, hu]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [qForm_eq_dotProduct]
  rw [hsplit, h0]
  simp_rw [hsucc]
  rw [hsum]
  ring

/-- Linearising the shifted tail of the quadratic form, using `pTail G *ᵥ pWind G = pVec G`. -/
lemma qForm_tail_schur {R : ℕ} (G : Matrix (Fin (R+1)) (Fin (R+1)) ℝ) (hG : G.PosDef)
    (x : Fin (R+1) → ℝ) :
    qForm (pTail G) (fun i => x i.succ + x 0 * pWind G i)
      = qForm (pTail G) (fun i => x i.succ) + 2 * (x 0) * (pVec G ⬝ᵥ fun i => x i.succ)
        + (x 0)^2 * (pVec G ⬝ᵥ pWind G) := by
  set u : Fin R → ℝ := fun i => x i.succ with hu
  have hsymm : ∀ i j, G i j = G j i := by
    have hsymT : Gᵀ = G := by simpa using hG.isHermitian.eq
    intro i j
    have h := congrFun (congrFun hsymT j) i
    simpa [Matrix.transpose_apply] using h
  have hCpd : (pTail G).PosDef := hG.submatrix (e := Fin.succ) (Fin.succ_injective R)
  have hdet : IsUnit (pTail G).det := isUnit_iff_ne_zero.mpr (ne_of_gt hCpd.det_pos)
  have hCsym : (pTail G).IsSymm := Matrix.IsSymm.ext fun i j => hsymm j.succ i.succ
  have hCw : pTail G *ᵥ pWind G = pVec G := by
    rw [pWind, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (pTail G) hdet, Matrix.one_mulVec]
  have hy : (fun i => x i.succ + x 0 * pWind G i) = u + x 0 • pWind G := by
    rw [hu]
    funext i
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hwA : pWind G ⬝ᵥ (pTail G *ᵥ u) = pVec G ⬝ᵥ u := by
    rw [hCsym.dotProduct_mulVec_comm, hCw]
    exact dotProduct_comm u (pVec G)
  rw [hy]
  simp only [qForm_eq_dotProduct]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hCw]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hwA, dotProduct_comm u (pVec G), dotProduct_comm (pWind G) (pVec G)]
  ring

theorem peel_quad {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (hG : G.PosDef)
    (x : Fin (R + 1) → ℝ) :
    qForm G x = qForm (pTail G) (fun i => x i.succ + x 0 * pWind G i) + pSchur G * (x 0) ^ 2 := by
  have hA := qForm_head_tail G hG x
  have hB := qForm_tail_schur G hG x
  have hs : pSchur G = pHead G - pVec G ⬝ᵥ pWind G := by
    rw [pSchur, dotProduct]
  rw [hA, hB, hs]
  ring

end Work.HP.Sig2
