import Mathlib
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

theorem contDiffAt_inv_entry {n : ℕ} (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℝ)
    (hX : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞) (fun w => X w p q) z)
    (hdet : (X z).det ≠ 0) (p q : Fin n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => ((X w)⁻¹) p q) z := by
  classical
  -- Package the componentwise smoothness as smoothness of the family of matrix entries.
  have hXpi : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Fin n → ℝ => (fun i j => X w i j)) z := by
    rw [contDiffAt_pi]; intro i; rw [contDiffAt_pi]; intro j; exact hX i j
  -- The determinant and the entries of the adjugate depend polynomially on the entries.
  have hdetA : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (X w).det) z :=
    (Work.Diff.EXT.contDiff_matrix_det_pi (n := n)).contDiffAt.comp z hXpi
  have hadj : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (X w).adjugate p q) z :=
    (Work.Diff.EXT.contDiff_matrix_adjugate_entry_pi (n := n) p q).contDiffAt.comp z hXpi
  have hdetinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => ((X w).det)⁻¹) z := hdetA.inv hdet
  have hmain : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => ((X w).det)⁻¹ * (X w).adjugate p q) z :=
    hdetinv.mul hadj
  -- Cramer's rule: `A⁻¹ = (det A)⁻¹ • A.adjugate`.
  rw [show (fun w => ((X w)⁻¹) p q) = fun w => ((X w).det)⁻¹ * (X w).adjugate p q from by
    funext w
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact congrFun Ring.inverse_eq_inv' _]
  exact hmain

end Work.Diff.STE.B3
