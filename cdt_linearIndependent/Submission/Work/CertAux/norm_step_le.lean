import Mathlib
import Submission.Work.Cert.aLoop_aux

namespace Work.CertAux

/-- One-step telescoping norm bound for the `θ`-partial sums: writing
`q ^ (tri (k+1)) = q ^ (tri k) * q ^ (k+1)`, the error `r - q ^ tri (k+1)` splits as
`(r - u*v) + u*(v - q^(k+1)) + (u - q^(tri k))*q^(k+1)`, and the triangle inequality
plus submultiplicativity of `‖·‖` gives the stated budget. -/
theorem norm_step_le (q u v r : ℂ) (k : ℕ) (A B C D E : ℝ)
    (hA : ‖r - u * v‖ ≤ A) (hB : ‖u‖ ≤ B) (hC : ‖v - q ^ (k + 1)‖ ≤ C)
    (hD : ‖u - q ^ (Work.Cert.tri k)‖ ≤ D) (hE : ‖q ^ (k + 1)‖ ≤ E) :
    ‖r - q ^ (Work.Cert.tri (k + 1))‖ ≤ A + B * C + D * E := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg u) hB
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hC
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) hD
  have hE0 : 0 ≤ E := le_trans (norm_nonneg _) hE
  have hdecomp : r - q ^ Work.Cert.tri (k + 1)
      = (r - u * v) + u * (v - q ^ (k + 1)) + (u - q ^ Work.Cert.tri k) * q ^ (k + 1) := by
    rw [Work.Cert.tri_succ k, pow_add]; ring
  have hmul1 : ‖u * (v - q ^ (k + 1))‖ ≤ B * C := by
    rw [norm_mul]; exact mul_le_mul hB hC (norm_nonneg _) hB0
  have hmul2 : ‖(u - q ^ Work.Cert.tri k) * q ^ (k + 1)‖ ≤ D * E := by
    rw [norm_mul]; exact mul_le_mul hD hE (norm_nonneg _) hD0
  have hsum1 : ‖(r - u * v) + u * (v - q ^ (k + 1))‖
      ≤ ‖r - u * v‖ + ‖u * (v - q ^ (k + 1))‖ := norm_add_le _ _
  calc ‖r - q ^ Work.Cert.tri (k + 1)‖
      = ‖(r - u * v) + u * (v - q ^ (k + 1)) + (u - q ^ Work.Cert.tri k) * q ^ (k + 1)‖ := by
        rw [hdecomp]
    _ ≤ ‖(r - u * v) + u * (v - q ^ (k + 1))‖ + ‖(u - q ^ Work.Cert.tri k) * q ^ (k + 1)‖ :=
        norm_add_le _ _
    _ ≤ (A + B * C) + D * E := by linarith
    _ = A + B * C + D * E := by ring

end Work.CertAux
