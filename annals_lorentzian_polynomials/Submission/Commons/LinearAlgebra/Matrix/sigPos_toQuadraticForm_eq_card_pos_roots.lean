import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one

noncomputable section

open Matrix
open scoped Matrix

namespace QuadraticForm

/-- The positive signature of a quadratic form, as used in the statement of
`Commons.LinearAlgebra.Matrix.sigPos_toQuadraticForm_eq_card_pos_roots`. -/
noncomputable abbrev sigPos {R M : Type*} [AddCommGroup M] [CommRing R] [LinearOrder R]
    [Module R M] (Q : QuadraticForm R M) : ℕ :=
  _root_.sigPos Q

end QuadraticForm

namespace Commons.LinearAlgebra.Matrix

private lemma dotProduct_mulVec_transpose {m n : Type*} [Fintype m] [Fintype n]
    (x : m → ℝ) (A : Matrix m n ℝ) (y : n → ℝ) :
    x ⬝ᵥ A *ᵥ y = Aᵀ *ᵥ x ⬝ᵥ y := by
  rw [dotProduct_mulVec, Matrix.mulVec_transpose]

private lemma weightedSumSquares_eq_dotProduct_diagonal {n : ℕ} (w : Fin n → ℝ)
    (x : Fin n → ℝ) :
    QuadraticMap.weightedSumSquares ℝ w x = x ⬝ᵥ diagonal w *ᵥ x := by
  simp [QuadraticMap.weightedSumSquares_apply, Matrix.mulVec_diagonal, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring

private lemma toQuadraticForm'_apply_dotProduct_mulVec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    A.toQuadraticForm' x = x ⬝ᵥ A *ᵥ x := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

private lemma card_pos_roots_eq_ncard_pos_eigenvalues {n : ℕ} (w : Fin n → ℝ) :
    ({i | 0 < w i} : Set (Fin n)).ncard =
      ((Multiset.map w Finset.univ.val).filter (fun r : ℝ => 0 < r)).card := by
  rw [Multiset.filter_map]
  rw [Multiset.card_map]
  have hset : ({i | 0 < w i} : Set (Fin n)) =
      (Finset.univ.filter (fun i : Fin n => 0 < w i) : Set (Fin n)) := by
    ext i
    simp
  rw [hset, Set.ncard_coe_finset]
  rw [← Finset.filter_val]
  rfl

private lemma weightedSumSquares_eq_toQuadraticForm'_of_decomp {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (U : Matrix.unitaryGroup (Fin n) ℝ) (w : Fin n → ℝ)
    (hAdecomp : A = (U : Matrix (Fin n) (Fin n) ℝ) * diagonal w *
      (U : Matrix (Fin n) (Fin n) ℝ)ᵀ) (x : Fin n → ℝ) :
    QuadraticMap.weightedSumSquares ℝ w ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x) =
      A.toQuadraticForm' x := by
  rw [toQuadraticForm'_apply_dotProduct_mulVec, hAdecomp]
  calc
    QuadraticMap.weightedSumSquares ℝ w ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x)
        = ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x) ⬝ᵥ diagonal w *ᵥ
          ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x) := by
          rw [weightedSumSquares_eq_dotProduct_diagonal]
    _ = x ⬝ᵥ (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ
          (diagonal w *ᵥ ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x)) := by
          conv_rhs => rw [dotProduct_mulVec_transpose]
    _ = x ⬝ᵥ ((U : Matrix (Fin n) (Fin n) ℝ) * diagonal w) *ᵥ
          ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x) := by
          rw [Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ ((U : Matrix (Fin n) (Fin n) ℝ) * diagonal w *
          (U : Matrix (Fin n) (Fin n) ℝ)ᵀ) *ᵥ x := by
          rw [Matrix.mulVec_mulVec]

theorem sigPos_toQuadraticForm_eq_card_pos_roots {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    QuadraticForm.sigPos A.toQuadraticForm' =
      (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card := by
  classical
  let hAherm : A.IsHermitian := by simpa [Matrix.isHermitian_iff_isSymm] using hA
  let w : Fin n → ℝ := hAherm.eigenvalues
  let U : Matrix.unitaryGroup (Fin n) ℝ := hAherm.eigenvectorUnitary
  have h_equiv : QuadraticMap.Equivalent A.toQuadraticForm'
      (QuadraticMap.weightedSumSquares ℝ w) := by
    let e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
      Matrix.toLin'OfInv (M := (U : Matrix (Fin n) (Fin n) ℝ))
        (M' := (star U : Matrix (Fin n) (Fin n) ℝ))
        (by simpa [Matrix.star_eq_conjTranspose] using (Unitary.coe_mul_star_self U))
        (by simpa [Matrix.star_eq_conjTranspose] using (Unitary.coe_star_mul_self U))
    refine ⟨{ e with
      map_app' := fun x => ?_ }⟩
    have hAdecomp : A = (U : Matrix (Fin n) (Fin n) ℝ) * diagonal w *
        (U : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
      simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using hAherm.spectral_theorem
    have he : e x = (U : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ x := by
      ext i
      simp [e, Matrix.toLin'OfInv_apply, Matrix.toLin'_apply, Matrix.star_eq_conjTranspose]
    change QuadraticMap.weightedSumSquares ℝ w (e x) = A.toQuadraticForm' x
    rw [he]
    exact weightedSumSquares_eq_toQuadraticForm'_of_decomp A U w hAdecomp x
  have hsig : QuadraticForm.sigPos A.toQuadraticForm' = ({i | 0 < w i} : Set (Fin n)).ncard := by
    change _root_.sigPos A.toQuadraticForm' = ({i | 0 < w i} : Set (Fin n)).ncard
    exact QuadraticForm.sigPos_of_equiv_weightedSumSquares h_equiv
  have hroots : A.charpoly.roots = Multiset.map w Finset.univ.val := by
    simpa [Function.comp_def] using hAherm.roots_charpoly_eq_eigenvalues
  rw [hsig, card_pos_roots_eq_ncard_pos_eigenvalues w]
  congr 1
  rw [hroots]

end Commons.LinearAlgebra.Matrix
