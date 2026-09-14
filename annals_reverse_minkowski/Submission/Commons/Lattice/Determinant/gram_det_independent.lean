import Mathlib.Analysis.InnerProductSpace.GramMatrix

noncomputable section
open scoped BigOperators

namespace Commons.Lattice.Determinant

/- Gram-determinant independence of the chosen Z-basis of a lattice.

For E = EuclideanSpace ℝ (Fin n), a Z-lattice ℒ ≤ E (given only through two Z-bases
e f : Module.Basis (Fin m) ℤ ℒ of the same free module ℒ - no discreteness needed), the
determinants of the two ambient Gram matrices coincide:

    det (Matrix.of fun i j => inner ℝ (e i : E) (e j : E))
  = det (Matrix.of fun i j => inner ℝ (f i : E) (f j : E))

PROOF ROUTE:
1. Since e and f are bases of the same Z-module ℒ, each basis vector of f expands integrally
   in e: for each j, `(f j : ℒ) = Σ i, (e.repr (f j) i) • e i` (finite sum inside ℒ; use the
   basis expansion `e.sum_repr` or `Basis.repr_symm_apply`-style facts).  Because the
   inclusion `ℒ → E` is Z-linear, the ambient values satisfy the same identity with real
   coefficients `((e.repr (f j) i : ℤ) : ℝ)` (a `Submodule.subtype` linear map pushes sums and
   scalar multiples through).
2. Let `C := Matrix.of fun i j => (e.repr (f j) i : ℤ → ℝ)` be the real change-of-basis
   matrix (integer entries).  By (1) and bilinearity of the inner product,
   `(Matrix.of fun i j => inner ℝ (f i : E) (f j : E)) = Cᵀ * Gram_e * C` where
   `Gram_e := Matrix.of fun i j => inner ℝ (e i : E) (e j : E)`.
3. `Matrix.det_mul` twice and `Matrix.det_transpose` reduce the right-hand side to
   `det Gram_e * (det C)²`.  Since `C` is an integer matrix and `e`, `f` are bases of the
   same module, `C` is invertible over Z, so `det C = ±1` (a unit of Z), hence `(det C)² = 1`. -/

abbrev Eu (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Expansion of a lattice vector in the ambient space, with real coefficients. -/
lemma coerce_expand_real {n m : ℕ} (ℒ : Submodule ℤ (Eu n))
    (e : Module.Basis (Fin m) ℤ ℒ) (y : ℒ) :
    (y : Eu n) = ∑ i : Fin m, (((e.repr y i : ℤ) : ℝ)) • (e i : Eu n) := by
  have hco : ((∑ i : Fin m, (e.repr y i : ℤ) • (e i : ℒ) : ℒ) : Eu n) = (y : Eu n) := by
    exact congrArg (fun v : ℒ => (v : Eu n)) (e.sum_repr y)
  rw [← hco]
  change (Submodule.subtype ℒ) (∑ i : Fin m, (e.repr y i : ℤ) • (e i : ℒ))
      = ∑ i : Fin m, (((e.repr y i : ℤ) : ℝ)) • ((e i : ℒ) : Eu n)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  exact (Int.cast_smul_eq_zsmul ℝ (e.repr y i) ((e i : ℒ) : Eu n)).symm

/-- Bilinearity of the real inner product on finite linear combinations. -/
lemma inner_sum_sum {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : Fin m → E) (A B : Fin m → ℝ) :
    inner ℝ (∑ i, A i • x i) (∑ j, B j • y j) =
      ∑ i : Fin m, ∑ j : Fin m, (A i * B j) * inner ℝ (x i) (y j) := by
  rw [sum_inner]
  simp_rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- The Gram matrix of the `f`-basis equals the conjugated Gram matrix of `e` by the
change-of-basis matrix `e.toMatrix f` (with entries cast to `ℝ`). -/
lemma gram_of_f_eq_transpose_mul {n m : ℕ} (ℒ : Submodule ℤ (Eu n))
    (e f : Module.Basis (Fin m) ℤ ℒ) :
    Matrix.gram ℝ (fun i : Fin m => (f i : Eu n)) =
      ((e.toMatrix f).map (fun z : ℤ => (z : ℝ))).transpose *
        Matrix.gram ℝ (fun i : Fin m => (e i : Eu n)) *
        (e.toMatrix f).map (fun z : ℤ => (z : ℝ)) := by
  let C : Matrix (Fin m) (Fin m) ℝ := (e.toMatrix f).map (fun z : ℤ => (z : ℝ))
  have hf : ∀ b : Fin m, (f b : Eu n) = ∑ a : Fin m, C a b • (e a : Eu n) := by
    intro b
    have h := coerce_expand_real ℒ e (f b)
    simpa [C, Module.Basis.toMatrix_apply] using h
  change Matrix.gram ℝ (fun i : Fin m => (f i : Eu n)) =
      C.transpose * Matrix.gram ℝ (fun i : Fin m => (e i : Eu n)) * C
  ext i j
  calc
    inner ℝ ((f i : ℒ) : Eu n) ((f j : ℒ) : Eu n)
        = inner ℝ (∑ a : Fin m, C a i • (e a : Eu n)) (∑ b : Fin m, C b j • (e b : Eu n)) := by
          rw [hf i, hf j]
    _ = ∑ a : Fin m, ∑ b : Fin m, (C a i * C b j) * inner ℝ ((e a : ℒ) : Eu n) ((e b : ℒ) : Eu n) := by
          rw [inner_sum_sum]
    _ = ((C.transpose * Matrix.gram ℝ (fun i : Fin m => (e i : Eu n))) * C) i j := by
          simp_rw [Matrix.mul_apply]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          simp only [Matrix.transpose_apply, Matrix.gram_apply]
          ring

/-- The real change-of-basis matrix between two `ℤ`-bases of the same module has
determinant `±1`, so its square is `1`. -/
lemma det_change_sq_eq_one {n m : ℕ} (ℒ : Submodule ℤ (Eu n))
    (e f : Module.Basis (Fin m) ℤ ℒ) :
    (((e.toMatrix f).map (fun z : ℤ => (z : ℝ))).det) ^ 2 = 1 := by
  let C : Matrix (Fin m) (Fin m) ℝ := (e.toMatrix f).map (fun z : ℤ => (z : ℝ))
  let M : Matrix (Fin m) (Fin m) ℤ := e.toMatrix f
  let N : Matrix (Fin m) (Fin m) ℤ := f.toMatrix e
  have hMN : M * N = 1 := by
    dsimp [M, N]
    exact Module.Basis.toMatrix_mul_toMatrix_flip e f
  have hd : M.det * N.det = 1 := by
    have := congrArg Matrix.det hMN
    simpa [Matrix.det_mul, Matrix.det_one] using this
  have hCd : C.det = (M.det : ℝ) := by
    dsimp [C, M]
    exact (Int.cast_det M).symm
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hd with hM | hM
  · rw [hCd, hM]
    norm_num
  · rw [hCd, hM]
    norm_num

/-- Gram determinants coincide for two `ℤ`-bases of the same module. -/
lemma gram_det_eq {n m : ℕ} (ℒ : Submodule ℤ (Eu n))
    (e f : Module.Basis (Fin m) ℤ ℒ) :
    (Matrix.gram ℝ (fun i : Fin m => (e i : Eu n))).det =
    (Matrix.gram ℝ (fun i : Fin m => (f i : Eu n))).det := by
  let C : Matrix (Fin m) (Fin m) ℝ := (e.toMatrix f).map (fun z : ℤ => (z : ℝ))
  have hchange : Matrix.gram ℝ (fun i : Fin m => (f i : Eu n)) =
      C.transpose * Matrix.gram ℝ (fun i : Fin m => (e i : Eu n)) * C := by
    simpa [C] using gram_of_f_eq_transpose_mul ℒ e f
  have hdet : (Matrix.gram ℝ (fun i : Fin m => (f i : Eu n))).det =
      (Matrix.gram ℝ (fun i : Fin m => (e i : Eu n))).det * (C.det ^ 2) := by
    rw [hchange]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, pow_two]
    ring
  rw [hdet]
  have hsq : C.det ^ 2 = 1 := by
    simpa [C] using det_change_sq_eq_one ℒ e f
  rw [hsq]
  ring

/-- Gram-determinant independence of the chosen Z-basis of a lattice.

For E = EuclideanSpace ℝ (Fin n), a Z-lattice ℒ ≤ E (given only through two Z-bases
e f : Module.Basis (Fin m) ℤ ℒ of the same free module ℒ - no discreteness needed), the
determinants of the two ambient Gram matrices coincide:

    det (Matrix.of fun i j => inner ℝ (e i : E) (e j : E))
  = det (Matrix.of fun i j => inner ℝ (f i : E) (f j : E)) -/
theorem gram_det_independent {n m : ℕ}
    (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (e f : Module.Basis (Fin m) ℤ ℒ) :
    (Matrix.of (fun i : Fin m => fun j : Fin m =>
      inner ℝ ((e i : ℒ) : EuclideanSpace ℝ (Fin n)) ((e j : ℒ) : EuclideanSpace ℝ (Fin n)))).det =
    (Matrix.of (fun i : Fin m => fun j : Fin m =>
      inner ℝ ((f i : ℒ) : EuclideanSpace ℝ (Fin n)) ((f j : ℒ) : EuclideanSpace ℝ (Fin n)))).det := by
  simpa [Matrix.gram] using gram_det_eq ℒ e f

end Commons.Lattice.Determinant