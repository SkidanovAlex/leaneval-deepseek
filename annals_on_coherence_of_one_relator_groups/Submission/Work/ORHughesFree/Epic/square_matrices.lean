import Mathlib
import Submission.Work.ORHughesFree.Epic

namespace Work.ORHughesFree.Epic

theorem square_matrices {R S : Type} [Ring R] [Ring S] (f : R →+* S) {m n : ℕ}
    (X : Matrix (Fin 1) (Fin m) S) (P : Matrix (Fin m) (Fin n) R) (Y : Matrix (Fin n) (Fin 1) S)
    (hX : ∃ P' : Matrix (Fin 1) (Fin n) R, X * P.map f = P'.map f)
    (hY : ∃ Q' : Matrix (Fin m) (Fin 1) R, P.map f * Y = Q'.map f)
    (d : S) (hd : d = (X * P.map f * Y) 0 0) :
    ∃ (N : ℕ) (X₂ : Matrix (Fin 1) (Fin N) S) (P₂ : Matrix (Fin N) (Fin N) R)
      (Y₂ : Matrix (Fin N) (Fin 1) S),
      (∃ P₂' : Matrix (Fin 1) (Fin N) R, X₂ * P₂.map f = P₂'.map f) ∧
      (∃ Q₂' : Matrix (Fin N) (Fin 1) R, P₂.map f * Y₂ = Q₂'.map f) ∧
      d = (X₂ * P₂.map f * Y₂) 0 0 := by
  -- Given a `1 × m` row `X`, an `m × n` matrix `P` and an `n × 1` column `Y` over `S` such that
  -- both products `X * P.map f` and `P.map f * Y` lift to `R`, we enlarge to a square `N × N`
  -- matrix by placing `P` in the upper right corner of a `(m + n) × (m + n)` block matrix;
  -- the row and column vectors extend correspondingly and keep the `(0,0)` entry `d`.
  obtain ⟨P', hP'⟩ := hX
  obtain ⟨Q', hQ'⟩ := hY
  -- `c` identifies the block index with the plain index `Fin (m + n)`.
  let c : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  -- The block matrices (over the sum index `Fin m ⊕ Fin n`).
  let Xb : Matrix (Fin 1) (Fin m ⊕ Fin n) S :=
    fun i j => Sum.elim (fun a => X i a) (fun _ => (0 : S)) j
  let Pb : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R :=
    fun i j => Sum.elim (fun a => Sum.elim (fun _ => (0 : R)) (fun b => P a b) j)
      (fun _ => (0 : R)) i
  let Yb : Matrix (Fin m ⊕ Fin n) (Fin 1) S :=
    fun i j => Sum.elim (fun _ => (0 : S)) (fun b => Y b j) i
  let P'b : Matrix (Fin 1) (Fin m ⊕ Fin n) R :=
    fun i j => Sum.elim (fun _ => (0 : R)) (fun b => P' i b) j
  let Q'b : Matrix (Fin m ⊕ Fin n) (Fin 1) R :=
    fun i j => Sum.elim (fun a => Q' a j) (fun _ => (0 : R)) i
  -- The left product lifts.
  have A' : Xb * Pb.map f = P'b.map f := by
    ext i j
    rw [Matrix.mul_apply]
    cases j with
    | inl a =>
      simp only [Matrix.map, Matrix.of_apply, Fintype.sum_sum_type, Xb, Pb, P'b,
        Sum.elim_inl, Sum.elim_inr]
      simp
    | inr b =>
      have h := congrArg (fun M : Matrix (Fin 1) (Fin n) S => M i b) hP'
      simp only [Matrix.mul_apply, Matrix.map, Matrix.of_apply] at h
      simp only [Matrix.map, Matrix.of_apply, Fintype.sum_sum_type, Xb, Pb, P'b,
        Sum.elim_inl, Sum.elim_inr]
      simpa using h
  -- The right product lifts.
  have B' : Pb.map f * Yb = Q'b.map f := by
    ext i j
    rw [Matrix.mul_apply]
    cases i with
    | inl a =>
      have h := congrArg (fun M : Matrix (Fin m) (Fin 1) S => M a j) hQ'
      simp only [Matrix.mul_apply, Matrix.map, Matrix.of_apply] at h
      simp only [Matrix.map, Matrix.of_apply, Fintype.sum_sum_type, Pb, Yb, Q'b,
        Sum.elim_inl, Sum.elim_inr]
      simpa using h
    | inr b =>
      simp only [Matrix.map, Matrix.of_apply, Fintype.sum_sum_type, Pb, Yb, Q'b,
        Sum.elim_inl, Sum.elim_inr]
      simp
  -- The `(0,0)` entry is unchanged.
  have C' : (Xb * Pb.map f * Yb) 0 0 = ((P'.map f) * Y) 0 0 := by
    rw [A', Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.map, Matrix.of_apply, P'b, Yb, Sum.elim_inl, Sum.elim_inr]
    simp
  -- Reindex the block matrices from `Fin m ⊕ Fin n` to `Fin (m + n)`.
  refine ⟨m + n, Xb.submatrix id c.symm, Pb.submatrix c.symm c.symm,
    Yb.submatrix c.symm id, ?_, ?_, ?_⟩
  · refine ⟨P'b.submatrix id c.symm, ?_⟩
    rw [← Matrix.submatrix_map f c.symm c.symm Pb,
      ← Matrix.submatrix_mul Xb (Pb.map f) id c.symm c.symm c.symm.bijective,
      A', Matrix.submatrix_map]
  · refine ⟨Q'b.submatrix c.symm id, ?_⟩
    rw [← Matrix.submatrix_map f c.symm c.symm Pb,
      ← Matrix.submatrix_mul (Pb.map f) Yb c.symm c.symm id c.symm.bijective,
      B', Matrix.submatrix_map]
  · have hC : (Xb.submatrix id c.symm * (Pb.submatrix c.symm c.symm).map f *
        Yb.submatrix c.symm id) 0 0 = (Xb * Pb.map f * Yb) 0 0 := by
      rw [← Matrix.submatrix_map f c.symm c.symm Pb,
        ← Matrix.submatrix_mul Xb (Pb.map f) id c.symm c.symm c.symm.bijective,
        ← Matrix.submatrix_mul (Xb * Pb.map f) Yb id c.symm id c.symm.bijective]
      rfl
    rw [hC, C', hd, hP']

end Work.ORHughesFree.Epic
