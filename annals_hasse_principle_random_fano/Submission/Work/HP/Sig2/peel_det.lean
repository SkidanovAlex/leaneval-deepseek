import Mathlib
import Submission.Work.HP.Sig2.GaussPoissonDefs
import Submission.Work.HP.Sig2.PeelDefs
import Submission.Work.HP.Sig2.peel_tail_schur
import Submission.Work.HP.Sig2.submatrix_peel

/-!
# Peeling one head row/column off a positive definite matrix: the determinant

For a positive definite real matrix `G` indexed by `Fin (R+1)` we prove the Schur-complement
determinant formula

`G.det = pSchur G * (pTail G).det`,

where `pTail G` is the bottom-right `R × R` block, `pHead G` is the top-left entry, `pVec G` is
the first row tail and `pSchur G = pHead G - ∑ i, pVec G i * pWind G i` is the scalar Schur
complement.

The proof is the classical LDU argument.  Reindexing `G` along
`peelEquiv R : Fin R ⊕ Fin 1 ≃ Fin (R+1)` (which sends `Sum.inl i` to `i.succ` and `Sum.inr 0`
to `0`) exhibits `G` as the block matrix

`[[pTail G, pVec G], [pVec G, [pHead G]]]`,

the determinant of which is computed by `Matrix.det_fromBlocks₁₁` as
`(pTail G).det * (pHead G - pVec G · (pTail G)⁻¹ · pVec G).det`.  The trailing block is `1 × 1`
and its entry is exactly `pSchur G`, since `(pTail G)⁻¹ ·ᵥ pVec G = pWind G`.  Positive
definiteness enters through `pTail_posDef`, which makes the leading block invertible.
-/

noncomputable section

set_option linter.style.haveILetI false

open Matrix

namespace Work.HP.Sig2

/-- The `(0,0)` entry of the `1 × 1` Schur complement `[pHead G] - pVec G · (pTail G)⁻¹ · pVec G`
of the head block is the scalar Schur complement `pSchur G`.  No hypothesis on `G` is needed: this
is the definition of `pSchur` and `pWind` written with matrix products. -/
theorem schur_entry_eq_pSchur {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) :
    (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => pHead G) -
      (Matrix.of (fun (_ : Fin 1) (j : Fin R) => pVec G j) *
        ((pTail G)⁻¹ * Matrix.of (fun (i : Fin R) (_ : Fin 1) => pVec G i)))) 0 0
      = pSchur G := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, pSchur, pWind, Matrix.mulVec,
    dotProduct]

theorem peel_det {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (hG : G.PosDef) :
    G.det = pSchur G * (pTail G).det := by
  -- The tail block of a positive definite matrix is invertible, so that `⅟ (pTail G)` makes sense
  -- and `Matrix.det_fromBlocks₁₁` can be used with `pTail G` as the leading block.
  letI hInv : Invertible (pTail G) :=
    ((nonempty_invertible_iff_isUnit (pTail G)).mpr (pTail_posDef G hG).isUnit).some
  have hSchur : (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => pHead G) -
      Matrix.of (fun (_ : Fin 1) (j : Fin R) => pVec G j) * ⅟(pTail G) *
        Matrix.of (fun (i : Fin R) (_ : Fin 1) => pVec G i)) 0 0 = pSchur G := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.mul_assoc]
    exact schur_entry_eq_pSchur G
  calc G.det
      = (G.submatrix (peelEquiv R) (peelEquiv R)).det :=
        (Matrix.det_submatrix_equiv_self (peelEquiv R) G).symm
    _ = (Matrix.fromBlocks (pTail G)
          (Matrix.of (fun i (_ : Fin 1) => pVec G i))
          (Matrix.of (fun (_ : Fin 1) j => pVec G j))
          (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => pHead G))).det := by
        rw [submatrix_peel G hG]
    _ = (pTail G).det *
        (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => pHead G) -
          Matrix.of (fun (_ : Fin 1) (j : Fin R) => pVec G j) * ⅟(pTail G) *
            Matrix.of (fun (i : Fin R) (_ : Fin 1) => pVec G i)).det :=
        Matrix.det_fromBlocks₁₁ _ _ _ _
    _ = (pTail G).det * pSchur G := by rw [Matrix.det_fin_one, hSchur]
    _ = pSchur G * (pTail G).det := mul_comm _ _

end Work.HP.Sig2
