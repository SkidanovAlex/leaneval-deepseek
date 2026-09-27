import Mathlib
import Submission.Work.Mostow.poAux

/-!
# Auxiliary matrices for `Work.Mostow.poCenter` (the centre of `O(n,1)`)

`J = pmOneMat = diag(1,…,1,−1)`.  The centre of `O(n,1)` is computed by testing against two
explicit families of elements of `O(n,1)`:

* diagonal sign matrices `diagSign a` (a `−1` at the index `a`, `1` elsewhere): a central matrix
  must commute with all of them, which forces it to be diagonal;
* hyperbolic boosts `boostMat_poCenterDefs i c s` in the `(e_i, e_time)`-plane (`c² − s² = 1`), which mix the
  spatial coordinate `i` with the time coordinate and hence equate the diagonal entries.

This file contains the definitions (and the trivial structural lemmas about them); the two
computational facts (`diagSign`/`boostMat_poCenterDefs` preserve the form `J`) are stated here as
`diagonal_form` (proved) and `boost_form` (proved in a separate module).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix
open scoped Matrix

noncomputable section

variable {n : ℕ}

/-! ## The diagonal of `J` -/

/-- The diagonal entries of `J = pmOneMat`: `−1` at the time coordinate, `1` elsewhere. -/
def jSign (n : ℕ) : Fin n ⊕ Fin 1 → ℝ := fun c => if c = Sum.inr 0 then -1 else 1

@[simp] lemma jSign_inl (i : Fin n) : jSign n (Sum.inl i) = 1 := by simp [jSign]
@[simp] lemma jSign_inr (j : Fin 1) : jSign n (Sum.inr j) = -1 := by
  obtain rfl : j = 0 := Subsingleton.elim j 0
  simp [jSign]

theorem pmOneMat_eq_diagonal_poCenterDefs :
    (pmOneMat : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) = Matrix.diagonal (jSign n) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · simp [pmOneMat, jSign, Matrix.diagonal, Matrix.one_apply]
  · simp [pmOneMat, jSign, Matrix.diagonal]
  · simp [pmOneMat, jSign, Matrix.diagonal]
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    obtain rfl : j = 0 := Subsingleton.elim j 0
    simp [pmOneMat, jSign, Matrix.diagonal]

/-! ## Diagonal sign matrices -/

/-- A diagonal matrix all of whose entries are `±1` preserves the form `J`. -/
theorem diagonal_form (f : Fin n ⊕ Fin 1 → ℝ) (hf : ∀ c, f c = 1 ∨ f c = -1) :
    (Matrix.diagonal f)ᵀ * pmOneMat * (Matrix.diagonal f) = pmOneMat ∧
    (Matrix.diagonal f) * pmOneMat * (Matrix.diagonal f)ᵀ = pmOneMat := by
  have key : (Matrix.diagonal f)ᵀ * pmOneMat * (Matrix.diagonal f) = pmOneMat := by
    rw [pmOneMat_eq_diagonal_poCenterDefs, Matrix.diagonal_transpose, mul_assoc, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_diagonal_iff]
    intro c
    rcases hf c with h | h <;> simp [h]
  exact ⟨key, by simpa [Matrix.diagonal_transpose] using key⟩

/-- The diagonal sign matrix with a `−1` at the index `a` and `1` elsewhere. -/
def diagSign (a : Fin n ⊕ Fin 1) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.diagonal (fun c => if c = a then -1 else 1)

/-- The element of `O(n,1)` given by `diagSign a`. -/
def diagSignElem (a : Fin n ⊕ Fin 1) : O1 n :=
  O1.ofMatrix (diagSign a)
    (diagonal_form (fun c => if c = a then -1 else 1)
      (by intro c; by_cases h : c = a <;> simp [h]))

@[simp] lemma mat_diagSignElem (a : Fin n ⊕ Fin 1) : mat (diagSignElem a) = diagSign a :=
  mat_O1_ofMatrix _ _

/-! ## Hyperbolic boosts -/

/-- The `n × n` block of a boostMat_poCenterDefs in the `(e_i, e_time)`-plane: identity with `c` in position `i`. -/
def boostP_poCenterDefs (i : Fin n) (c : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun p => if p = i then c else 1)

/-- The `n × 1` block of a boostMat_poCenterDefs. -/
def boostU (i : Fin n) (s : ℝ) : Matrix (Fin n) (Fin 1) ℝ := fun p _ => if p = i then s else 0

/-- The `1 × n` block of a boostMat_poCenterDefs. -/
def boostV (i : Fin n) (s : ℝ) : Matrix (Fin 1) (Fin n) ℝ := fun _ p => if p = i then s else 0

/-- The `1 × 1` block of a boostMat_poCenterDefs. -/
def boostW (c : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => c

/-- The hyperbolic boostMat_poCenterDefs in the `(e_i, e_time)`-plane with `cosh`-parameter `c` and
`sinh`-parameter `s` (`c² − s² = 1`); it is an element of `O(n,1)`. -/
def boostMat_poCenterDefs (i : Fin n) (c s : ℝ) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks (boostP_poCenterDefs i c) (boostU i s) (boostV i s) (boostW c)

lemma boostP_transpose_poCenterDefs (i : Fin n) (c : ℝ) : (boostP_poCenterDefs i c)ᵀ = boostP_poCenterDefs i c := by
  rw [boostP_poCenterDefs, Matrix.diagonal_transpose]

lemma boostU_transpose (i : Fin n) (s : ℝ) : (boostU i s)ᵀ = boostV i s := by
  ext j p
  rw [Matrix.transpose_apply]
  rfl

lemma boostV_transpose (i : Fin n) (s : ℝ) : (boostV i s)ᵀ = boostU i s := by
  ext p j
  rw [Matrix.transpose_apply]
  rfl

lemma boostW_transpose (c : ℝ) : (boostW c)ᵀ = boostW c := by
  ext j k
  rw [Matrix.transpose_apply]
  rfl

/-- The boostMat_poCenterDefs is a symmetric matrix. -/
lemma boost_transpose (i : Fin n) (c s : ℝ) : (boostMat_poCenterDefs i c s)ᵀ = boostMat_poCenterDefs i c s := by
  rw [boostMat_poCenterDefs, Matrix.fromBlocks_transpose, boostP_transpose_poCenterDefs, boostV_transpose, boostU_transpose,
    boostW_transpose]

/-- The spatial/time entry of the boostMat_poCenterDefs is `s` (in particular nonzero when `s ≠ 0`). -/
@[simp] lemma boost_apply_spatial_time (i : Fin n) (c s : ℝ) :
    boostMat_poCenterDefs i c s (Sum.inl i) (Sum.inr 0) = s := by
  rw [boostMat_poCenterDefs, Matrix.fromBlocks_apply₁₂]
  simp [boostU]

/-- The time/spatial entry of the boostMat_poCenterDefs is `s`. -/
@[simp] lemma boost_apply_time_spatial (i : Fin n) (c s : ℝ) :
    boostMat_poCenterDefs i c s (Sum.inr 0) (Sum.inl i) = s := by
  rw [boostMat_poCenterDefs, Matrix.fromBlocks_apply₂₁]
  simp [boostV]

/-! ## The underlying matrix map is injective -/

/-- `mat` is injective: an element of `O(n,1)` is determined by its matrix. -/
theorem mat_injective : Function.Injective (mat : O1 n → Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := by
  intro A B h
  have := congrArg MatrixSum.ofMatrix h
  simpa [mat] using this

end

end Work.Mostow
