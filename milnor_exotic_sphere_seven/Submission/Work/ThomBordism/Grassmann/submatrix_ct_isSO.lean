import Mathlib
import Submission.Work.ThomBordism.Grassmann.FibreBaseDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Grassmann

/-!
# The top-left block of an element of `SO(k)` with a trivial last column/row

If `A ∈ SO(k)` vanishes off the last entry of its last column and last row and has
`A (lastk) (lastk) = 1`, then the top-left `(k-1) × (k-1)` block `A.submatrix ct ct` is again
orthogonal with determinant `1`.  Indeed such an `A` is the block matrix `diag(B, 1)` with
`B = A.submatrix ct ct`, so orthogonality of `A` restricts to orthogonality of `B` and
`det A = det B · 1`.
-/

theorem submatrix_ct_isSO (k : ℕ) (hk : 1 ≤ k) (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : Work.ThomBordism.Grassmann.IsSO A)
    (hcol : ∀ i : Fin k, i ≠ Work.ThomBordism.Grassmann.lastk k hk →
      A (Work.ThomBordism.Grassmann.lastk k hk) i = 0)
    (hrow : ∀ j : Fin k, j ≠ Work.ThomBordism.Grassmann.lastk k hk →
      A j (Work.ThomBordism.Grassmann.lastk k hk) = 0)
    (hd : A (Work.ThomBordism.Grassmann.lastk k hk) (Work.ThomBordism.Grassmann.lastk k hk) = 1) :
    Work.ThomBordism.Grassmann.IsSO (A.submatrix (Work.ThomBordism.Grassmann.ct k hk) (Work.ThomBordism.Grassmann.ct k hk)) := by
  -- Orthogonality of the columns of `A` restricted to the first `k-1` indices.
  have key : ∀ i j : Fin (k-1),
      (∑ l : Fin (k-1), A (ct k hk l) (ct k hk i) * A (ct k hk l) (ct k hk j))
        = (1 : Matrix (Fin (k-1)) (Fin (k-1)) ℝ) i j := by
    intro i j
    have hsum : (∑ l : Fin k, A l (ct k hk i) * A l (ct k hk j))
        = (1 : Matrix (Fin k) (Fin k) ℝ) (ct k hk i) (ct k hk j) := by
      rw [← hA.1]
      simp [Matrix.mul_apply]
    rw [sum_fin_eq k hk (fun l => A l (ct k hk i) * A l (ct k hk j))] at hsum
    simp only [hcol (ct k hk i) (ct_ne_lastk k hk i), hcol (ct k hk j) (ct_ne_lastk k hk j),
      zero_mul, add_zero] at hsum
    rw [hsum]
    simp [Matrix.one_apply, (ct_injective k hk).eq_iff]
  constructor
  · ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
    exact key i j
  · -- `A` is `diag(B,1)` up to reindexing, so its determinant is `det B`.
    have hblocks : A.submatrix (sumEquiv k hk) (sumEquiv k hk) =
        Matrix.fromBlocks (A.submatrix (ct k hk) (ct k hk))
          (0 : Matrix (Fin (k-1)) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin (k-1)) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext x y
      rcases x with i | u <;> rcases y with j | v
      · simp [Matrix.submatrix_apply]
      · simpa using hrow (ct k hk i) (ct_ne_lastk k hk i)
      · simpa using hcol (ct k hk j) (ct_ne_lastk k hk j)
      · have huv : u = v := Subsingleton.elim u v
        rw [huv]
        simpa [Matrix.one_apply] using hd
    have h1 : (A.submatrix (sumEquiv k hk) (sumEquiv k hk)).det = 1 := by
      rw [Matrix.det_submatrix_equiv_self, hA.2]
    rw [hblocks, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one] at h1
    exact h1

end Work.ThomBordism.Grassmann
