/-
  annals_wilkies_conjecture, AREA E3K: the Jacobian of the lifted system at a lifted point is
  invertible as soon as the Jacobian of the original system is.

  The lifted Jacobian has the block shape

      `[[ diag (1+t_p²)⁻¹ , ∂_t ], [ ∂_x , ∂_x ]]`

  with respect to the decomposition `Fin (rt+n) ≃ Fin rt ⊕ Fin n` (`tan` coordinates first).
  Expanding the determinant around the (invertible) top-left block gives the Schur complement
  `∂_x + ∂_t · diag (1+t_p²) · B`; the entrywise identity (`hD`, proved in `LiftEntry.lean`)
  identifies it with the original Jacobian `(S.ev (S.d a (f i)) x₀)`.
-/
import Submission.Work.WilE3K.LiftMain
import Mathlib

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re r : ℕ}

/-- The decomposition of the ambient coordinates of an `ETData` into `tan` coordinates and free
coordinates: `Sum.inl p ↦ E.tanCoord p`, `Sum.inr a ↦ E.freeCoord a`. -/
def coordEquiv (E : ETData N rt n re) : Fin rt ⊕ Fin n ≃ Fin (N + 1) :=
  finSumFinEquiv.trans (Fin.castOrderIso E.h).toEquiv

theorem coordEquiv_inl (E : ETData N rt n re) (p : Fin rt) :
    coordEquiv E (Sum.inl p) = E.tanCoord p := by
  simp only [coordEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, Fin.castOrderIso]
  exact Fin.ext rfl

theorem coordEquiv_inr (E : ETData N rt n re) (a : Fin n) :
    coordEquiv E (Sum.inr a) = E.freeCoord a := by
  simp only [coordEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right, Fin.castOrderIso]
  exact Fin.ext rfl

/-- **Schur complement determinant identity**, in the form with an explicit right inverse of the
top-left block. -/
theorem det_fromBlocks_aux {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (Dm : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (Ed : Matrix n n ℝ)
    (Ninv : Matrix m m ℝ) (hN : Ninv * Dm = 1) :
    (Matrix.fromBlocks Dm B C Ed).det = Dm.det * (Ed - C * Ninv * B).det := by
  have hfac : Matrix.fromBlocks Dm B C Ed
      = Matrix.fromBlocks 1 (0 : Matrix m n ℝ) (C * Ninv) 1 *
        Matrix.fromBlocks Dm B 0 (Ed - C * Ninv * B) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp [Matrix.mul_assoc, hN]
    · rw [Matrix.one_mul]; abel
  rw [hfac, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_one]
  ring

/-- **Nondegeneracy of a lifted point.**  If the entrywise identity `hD` holds (the chain-rule
comparison of the lifted Jacobian with the original one), then the lifted Jacobian at
`liftPoint S E x₀` is invertible as soon as the original Jacobian is. -/
theorem jac_det_ne_zero {S : Work.WilE3.SepChainLocal n r}
    (hn : Lift.rt S + n = (Lift.rt S + n - 1) + 1)
    (f : Fin n → EAPoly n r) (k : Fin (Lift.rt S) → ℤ) (x₀ : Fin n → ℝ)
    (hD : ∀ i a : Fin n, S.ev (S.d a (f i)) x₀ =
        (Lift.liftET S hn f k).evalPoly
            ((Lift.liftET S hn f k).dPoly ((Lift.liftET S hn f k).freeCoord a)
              ((Lift.liftET S hn f k).G i))
            (Lift.liftPoint S (Lift.liftET S hn f k) x₀)
        + ∑ p : Fin (Lift.rt S), (Lift.liftET S hn f k).evalPoly
            ((Lift.liftET S hn f k).dPoly ((Lift.liftET S hn f k).tanCoord p)
              ((Lift.liftET S hn f k).G i))
            (Lift.liftPoint S (Lift.liftET S hn f k) x₀)
          * ((1 + ((Lift.liftPoint S (Lift.liftET S hn f k) x₀)
              ((Lift.liftET S hn f k).tanCoord p)) ^ 2) * S.a (Lift.tanIdx S p) a))
    (hnd : (Matrix.of fun i a => S.ev (S.d a (f i)) x₀).det ≠ 0) :
    ((Lift.liftET S hn f k).jac (Lift.liftPoint S (Lift.liftET S hn f k) x₀)).det ≠ 0 := by
  classical
  set E := Lift.liftET S hn f k with hE
  set z := Lift.liftPoint S E x₀ with hz
  have hlam : ∀ (p : Fin (Lift.rt S)) (a : Fin n), E.lam p a = S.a (Lift.tanIdx S p) a := by
    intro p a
    simp only [hE, Lift.liftET, Lift.liftE, Lift.liftLam]
  set Dm : Matrix (Fin (Lift.rt S)) (Fin (Lift.rt S)) ℝ :=
    Matrix.diagonal (fun p => (1 + (z (E.tanCoord p)) ^ 2)⁻¹) with hDm
  set Ninv : Matrix (Fin (Lift.rt S)) (Fin (Lift.rt S)) ℝ :=
    Matrix.diagonal (fun p => 1 + (z (E.tanCoord p)) ^ 2) with hNinv
  set B : Matrix (Fin (Lift.rt S)) (Fin n) ℝ :=
    Matrix.of (fun p a => E.jac z (E.tanCoord p) (E.freeCoord a)) with hB
  set C : Matrix (Fin n) (Fin (Lift.rt S)) ℝ :=
    Matrix.of (fun i p => E.jac z (E.freeCoord i) (E.tanCoord p)) with hC
  set Ed : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun i a => E.jac z (E.freeCoord i) (E.freeCoord a)) with hEd
  have hblocks : (E.jac z).submatrix (coordEquiv E) (coordEquiv E)
      = Matrix.fromBlocks Dm B C Ed := by
    ext s t
    rcases s with p | a <;> rcases t with p' | a'
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, coordEquiv_inl,
        ETData.jac_tan, ETData.dTanFun_tan, hDm, Matrix.diagonal_apply]
      by_cases h : p' = p
      · subst h; simp [one_div]
      · have h2 : ¬ (p = p') := fun hh => h hh.symm
        simp [h, h2]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, coordEquiv_inl, coordEquiv_inr,
        hB, Matrix.of_apply]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, coordEquiv_inl, coordEquiv_inr,
        hC, Matrix.of_apply]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, coordEquiv_inr, hEd,
        Matrix.of_apply]
  have hNinvDm : Ninv * Dm = 1 := by
    rw [hNinv, hDm, Matrix.diagonal_mul_diagonal]
    ext p p'
    rw [Matrix.one_apply, Matrix.diagonal_apply]
    by_cases h : p = p'
    · subst h
      rw [if_pos rfl, if_pos rfl]
      exact mul_inv_cancel₀ (by positivity)
    · rw [if_neg h, if_neg h]
  have hSchur : Ed - C * Ninv * B = Matrix.of (fun i a => S.ev (S.d a (f i)) x₀) := by
    ext i a
    rw [Matrix.of_apply, hD i a]
    have hCNB : (C * Ninv * B) i a
        = ∑ p : Fin (Lift.rt S), E.evalPoly (E.dPoly (E.tanCoord p) (E.G i)) z
            * ((1 + (z (E.tanCoord p)) ^ 2) * (-(E.lam p a))) := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro p _
      rw [hNinv, Matrix.mul_diagonal]
      simp only [hC, hB, Matrix.of_apply, ETData.jac_tan, ETData.jac_free, ETData.dTanFun_free]
      ring
    rw [Matrix.sub_apply, hCNB]
    have hEdz : Ed i a = E.evalPoly (E.dPoly (E.freeCoord a) (E.G i)) z := by
      simp only [hEd, Matrix.of_apply, ETData.jac_free]
    rw [hEdz]
    have hsum : (∑ p : Fin (Lift.rt S), E.evalPoly (E.dPoly (E.tanCoord p) (E.G i)) z
          * ((1 + (z (E.tanCoord p)) ^ 2) * (-(E.lam p a))))
        = -∑ p : Fin (Lift.rt S), E.evalPoly (E.dPoly (E.tanCoord p) (E.G i)) z
            * ((1 + (z (E.tanCoord p)) ^ 2) * S.a (Lift.tanIdx S p) a) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rw [hlam p a]
      ring
    rw [hsum]
    ring
  have hdet := det_fromBlocks_aux Dm B C Ed Ninv hNinvDm
  have hDm_ne : Dm.det ≠ 0 := by
    intro h0
    have h1 : (Ninv * Dm).det = 1 := by rw [hNinvDm, Matrix.det_one]
    rw [Matrix.det_mul, h0, mul_zero] at h1
    exact one_ne_zero h1.symm
  have hfrom_ne : (Matrix.fromBlocks Dm B C Ed).det ≠ 0 := by
    rw [hdet, hSchur]
    exact mul_ne_zero hDm_ne hnd
  rw [← Matrix.det_submatrix_equiv_self (coordEquiv E) (E.jac z), hblocks]
  exact hfrom_ne

end Work.WilE3K
