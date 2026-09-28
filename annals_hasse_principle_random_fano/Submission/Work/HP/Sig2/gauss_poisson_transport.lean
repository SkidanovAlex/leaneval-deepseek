import Mathlib
import Submission.Work.HP.Sig2.GaussPoissonDefs

/-!
# Transport of the Gaussian Poisson summation identity to an arbitrary finite index type

`finStatement n` (see `GaussPoissonDefs`) is the 0-phase Gaussian Poisson summation identity
for matrices indexed by `Fin n`:

`Σ_{m ∈ ℤ^n} exp (-(π/s²) · qForm G (m + u)) = s^n / √(det G) · Σ_{m ∈ ℤ^n} exp (-(π s²) ·
qForm G⁻¹ m + 2πi · m·u)`.

The present file shows that the identity is *independent of the chosen labelling of the
coordinates*: given `H : ∀ n, finStatement n`, it holds for matrices indexed by an arbitrary
finite type `κ`.  The proof is a re-indexing: fix a bijection `e : κ ≃ Fin (card κ)`, transfer
the matrix `G` to `G.submatrix e.symm e.symm`, and observe that

* the quadratic form is invariant under the re-indexing (`qForm_submatrix_equiv`),
* the determinant is invariant (`det_submatrix_equiv`),
* the inverse is re-indexed consistently (`inv_submatrix_equiv`),
* and the `ℤ`-indexed sums over functions `κ → ℤ` are re-indexed by `intArrowEquiv`.
-/

open Matrix

namespace Work.HP.Sig2

/-- Re-index the lattice of integer-valued functions along an equivalence `e : κ ≃ Fin n`:
`m ↦ (fun i => m (e i))`. -/
def intArrowEquiv {κ : Type*} {n : ℕ} (e : κ ≃ Fin n) : (Fin n → ℤ) ≃ (κ → ℤ) where
  toFun m i := m (e i)
  invFun x j := x (e.symm j)
  left_inv m := by funext j; simp
  right_inv x := by funext i; simp

@[simp] lemma intArrowEquiv_apply {κ : Type*} {n : ℕ} (e : κ ≃ Fin n) (m : Fin n → ℤ)
    (i : κ) : intArrowEquiv e m i = m (e i) := rfl

/-- The quadratic form `qForm` is invariant under re-indexing a matrix along an equivalence. -/
lemma qForm_submatrix_equiv {κ : Type*} [Fintype κ] {n : ℕ} (e : κ ≃ Fin n)
    (G : Matrix κ κ ℝ) (x : Fin n → ℝ) :
    qForm (G.submatrix e.symm e.symm) x = qForm G (fun i => x (e i)) := by
  simp only [qForm, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e.symm (fun i : κ => ∑ j : κ, x (e i) * G i j * x (e j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Equiv.sum_comp e (fun j : Fin n => x i * G (e.symm i) (e.symm j) * x j)]
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The determinant is invariant under re-indexing a matrix along an equivalence. -/
lemma det_submatrix_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ} (e : κ ≃ Fin n)
    (G : Matrix κ κ ℝ) : (G.submatrix e.symm e.symm).det = G.det := by
  rw [show G.submatrix e.symm e.symm = Matrix.reindex e e G from rfl]
  rw [Matrix.det_reindex]
  simp

/-- The inverse of a positive definite matrix is re-indexed consistently. -/
lemma inv_submatrix_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ} (e : κ ≃ Fin n)
    (G : Matrix κ κ ℝ) (hG : G.PosDef) :
    (G.submatrix e.symm e.symm)⁻¹ = G⁻¹.submatrix e.symm e.symm := by
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.mpr (ne_of_gt hG.det_pos)
  apply Matrix.inv_eq_right_inv
  rw [Matrix.submatrix_mul_equiv G G⁻¹ e.symm e.symm e.symm]
  rw [Matrix.mul_nonsing_inv G hdet]
  exact submatrix_one_equiv e.symm

/-- `qForm` of the re-indexed inverse. -/
lemma qForm_inv_submatrix_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ} (e : κ ≃ Fin n)
    (G : Matrix κ κ ℝ) (hG : G.PosDef) (x : Fin n → ℝ) :
    qForm (G.submatrix e.symm e.symm)⁻¹ x = qForm G⁻¹ (fun i => x (e i)) := by
  rw [inv_submatrix_equiv e G hG, qForm_submatrix_equiv e G⁻¹ x]

/-- Pointwise form of `qForm_submatrix_equiv` adapted to the shifted arguments `(m + u)`. -/
lemma qForm_transport {κ : Type*} [Fintype κ] {n : ℕ} (e : κ ≃ Fin n)
    (G : Matrix κ κ ℝ) (u : κ → ℝ) (m : Fin n → ℤ) :
    qForm G (fun i => (m (e i) : ℝ) + u i)
      = qForm (G.submatrix e.symm e.symm) (fun j => (m j : ℝ) + u (e.symm j)) := by
  rw [qForm_submatrix_equiv e G (fun j : Fin n => (m j : ℝ) + u (e.symm j))]
  congr 1
  ext i
  simp only [Equiv.symm_apply_apply]

/-- The linear form `m ↦ m·u` re-indexed along `e`. -/
lemma sum_mul_u_submatrix {κ : Type*} [Fintype κ] {n : ℕ} (e : κ ≃ Fin n) (u : κ → ℝ)
    (m : Fin n → ℤ) :
    (∑ j : Fin n, (m j : ℝ) * u (e.symm j)) = ∑ j : κ, (m (e j) : ℝ) * u j := by
  rw [← Equiv.sum_comp e (fun j : Fin n => (m j : ℝ) * u (e.symm j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [Equiv.symm_apply_apply]

/-- Re-indexing of the left-hand (lattice-sum) side of the Poisson identity. -/
lemma transport_lhs {κ : Type*} [Fintype κ] {n : ℕ} (e : κ ≃ Fin n)
    (G : Matrix κ κ ℝ) (s : ℝ) (u : κ → ℝ) :
    (∑' x : κ → ℤ, Complex.exp (((-(Real.pi / s ^ 2) *
      (qForm G (fun i => (x i : ℝ) + u i))) : ℝ)))
    = ∑' m : Fin n → ℤ, Complex.exp (((-(Real.pi / s ^ 2) *
      (qForm (G.submatrix e.symm e.symm) (fun j => (m j : ℝ) + u (e.symm j)))) : ℝ)) := by
  rw [← Equiv.tsum_eq (intArrowEquiv e)
        (fun x : κ → ℤ => Complex.exp (((-(Real.pi / s ^ 2) *
          (qForm G (fun i => (x i : ℝ) + u i))) : ℝ)))]
  apply tsum_congr
  intro m
  simp only [intArrowEquiv_apply]
  rw [qForm_transport e G u m]

/-- Re-indexing of the right-hand (dual-lattice-sum) side of the Poisson identity. -/
lemma transport_rhs {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ} (e : κ ≃ Fin n)
    (G : Matrix κ κ ℝ) (hG : G.PosDef) (s : ℝ) (u : κ → ℝ) :
    ((s : ℂ) ^ n / ((Real.sqrt (G.submatrix e.symm e.symm).det : ℝ) : ℂ)) *
      (∑' m : Fin n → ℤ, Complex.exp (((-(Real.pi * s ^ 2) *
          (qForm (G.submatrix e.symm e.symm)⁻¹ (fun j => (m j : ℝ)))) : ℝ)
        + 2 * Real.pi * Complex.I * ((∑ j : Fin n, (m j : ℝ) * u (e.symm j) : ℝ) : ℂ)))
    = ((s : ℂ) ^ n / ((Real.sqrt G.det : ℝ) : ℂ)) *
      (∑' m : κ → ℤ, Complex.exp (((-(Real.pi * s ^ 2) *
          (qForm G⁻¹ (fun j => (m j : ℝ)))) : ℝ)
        + 2 * Real.pi * Complex.I * ((∑ j : κ, (m j : ℝ) * u j : ℝ) : ℂ))) := by
  rw [det_submatrix_equiv e G]
  congr 1
  rw [← Equiv.tsum_eq (intArrowEquiv e)
        (fun x : κ → ℤ => Complex.exp (((-(Real.pi * s ^ 2) *
          (qForm G⁻¹ (fun j => (x j : ℝ)))) : ℝ)
        + 2 * Real.pi * Complex.I * ((∑ j : κ, (x j : ℝ) * u j : ℝ) : ℂ)))]
  apply tsum_congr
  intro m
  simp only [intArrowEquiv_apply]
  congr 1
  rw [qForm_inv_submatrix_equiv e G hG (fun j : Fin n => (m j : ℝ)), sum_mul_u_submatrix e u m]

theorem gauss_poisson_transport (H : ∀ n, finStatement n)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℝ) (hG : G.PosDef) (s : ℝ) (hs : 0 < s) (u : κ → ℝ) :
    (∑' n : κ → ℤ,
      Complex.exp (((-(Real.pi / s ^ 2) *
        (∑ i, ∑ j, ((n i : ℝ) + u i) * G i j * ((n j : ℝ) + u j))) : ℝ)))
      = ((s : ℂ) ^ Fintype.card κ / ((Real.sqrt G.det : ℝ) : ℂ)) *
        ∑' m : κ → ℤ,
          Complex.exp (((-(Real.pi * s ^ 2) *
              (∑ i, ∑ j, (m i : ℝ) * G⁻¹ i j * (m j : ℝ))) : ℝ)
            + 2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * u j : ℝ) : ℂ)) := by
  change (∑' x : κ → ℤ,
      Complex.exp (((-(Real.pi / s ^ 2) * (qForm G (fun i => (x i : ℝ) + u i))) : ℝ)))
      = ((s : ℂ) ^ Fintype.card κ / ((Real.sqrt G.det : ℝ) : ℂ)) *
        ∑' m : κ → ℤ,
          Complex.exp (((-(Real.pi * s ^ 2) * (qForm G⁻¹ (fun i => (m i : ℝ)))) : ℝ)
            + 2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * u j : ℝ) : ℂ))
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have hG' : (G.submatrix e.symm e.symm).PosDef := hG.submatrix e.symm.injective
  have hfin := H (Fintype.card κ) (G.submatrix e.symm e.symm) hG' s hs (fun j => u (e.symm j))
  rw [transport_lhs e G s u, hfin, transport_rhs e G hG s u]

end Work.HP.Sig2
