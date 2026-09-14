import Mathlib

namespace Commons.LinearAlgebra.Matrix

open scoped BigOperators

set_option autoImplicit false

/-- The set of real square matrices of determinant of absolute value one and with all
columns bounded in Euclidean norm by `C` is compact. -/
theorem isCompact_det_one_bounded_cols {m : ℕ} {C : ℝ} :
    IsCompact {A : Matrix (Fin m) (Fin m) ℝ |
      |A.det| = 1 ∧ ∀ i : Fin m,
        ‖(WithLp.toLp 2 (fun j : Fin m => A j i) : EuclideanSpace ℝ (Fin m))‖ ≤ C} := by
  classical
  -- Column norm as a function of the matrix.
  let colNorm (i : Fin m) (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
    ‖(WithLp.toLp 2 (fun j : Fin m => A j i) : EuclideanSpace ℝ (Fin m))‖
  -- It is continuous (w.r.t. the product topology on matrices and the usual topology on ℝ).
  have hcolNorm_cont (i : Fin m) : Continuous (colNorm i) := by
    have hcol : Continuous (fun A : Matrix (Fin m) (Fin m) ℝ => (fun j : Fin m => A j i)) := by
      refine continuous_pi ?_
      intro j
      exact continuous_id.matrix_elem j i
    have htoLp : Continuous (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) := by
      simpa [EuclideanSpace] using (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ))
    exact continuous_norm.comp (htoLp.comp hcol)
  -- The determinant has absolute value one: a closed condition.
  have hdet_closed :
      IsClosed {A : Matrix (Fin m) (Fin m) ℝ | |A.det| = 1} := by
    exact isClosed_eq
      (continuous_abs.comp
        (continuous_id.matrix_det : Continuous fun A : Matrix (Fin m) (Fin m) ℝ => A.det))
      (continuous_const : Continuous fun A : Matrix (Fin m) (Fin m) ℝ => (1 : ℝ))
  -- Each column bound is a closed condition.
  have hcol_closed (i : Fin m) :
      IsClosed {A : Matrix (Fin m) (Fin m) ℝ | colNorm i A ≤ C} := by
    exact (isClosed_Iic (a := C)).preimage (hcolNorm_cont i)
  have hSclosed :
      IsClosed {A : Matrix (Fin m) (Fin m) ℝ |
        |A.det| = 1 ∧ ∀ i : Fin m, colNorm i A ≤ C} := by
    rw [show {A : Matrix (Fin m) (Fin m) ℝ |
          |A.det| = 1 ∧ ∀ i : Fin m, colNorm i A ≤ C} =
          {A : Matrix (Fin m) (Fin m) ℝ | |A.det| = 1} ∩
            {A : Matrix (Fin m) (Fin m) ℝ | ∀ i : Fin m, colNorm i A ≤ C} by
        ext A
        simp]
    refine hdet_closed.inter ?_
    rw [show {A : Matrix (Fin m) (Fin m) ℝ | ∀ i : Fin m, colNorm i A ≤ C} =
          ⋂ i : Fin m, {A : Matrix (Fin m) (Fin m) ℝ | colNorm i A ≤ C} by
        ext A
        simp]
    exact isClosed_iInter hcol_closed
  -- Bound the entries of such a matrix by `B = max C 0`.
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right C 0
  have hSsub : {A : Matrix (Fin m) (Fin m) ℝ |
        |A.det| = 1 ∧ ∀ i : Fin m, colNorm i A ≤ C} ⊆
      (Set.Icc (-B) B).matrix := by
    intro A hA
    rcases hA with ⟨hdet, hcol⟩
    rw [Set.mem_matrix]
    intro j i
    have hv : colNorm i A ≤ C := hcol i
    have hentry : |A j i| ≤ C := by
      have h1 : |A j i| ≤ colNorm i A := by
        have h := PiLp.norm_apply_le
          (x := (WithLp.toLp 2 (fun k : Fin m => A k i) : EuclideanSpace ℝ (Fin m))) j
        simpa [colNorm] using h
      exact le_trans h1 hv
    have hAbs : |A j i| ≤ B := by
      dsimp [B]
      exact le_trans hentry (le_max_left C 0)
    exact abs_le.mp hAbs
  have hKcompact : IsCompact ((Set.Icc (-B) B).matrix : Set (Matrix (Fin m) (Fin m) ℝ)) := by
    exact IsCompact.matrix isCompact_Icc
  -- Assemble: the set is closed and contained in the compact box above.
  exact IsCompact.of_isClosed_subset hKcompact hSclosed hSsub

end Commons.LinearAlgebra.Matrix
