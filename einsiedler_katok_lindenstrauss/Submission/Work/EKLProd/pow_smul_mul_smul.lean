import Mathlib
import Submission.Work.EKLContract.Defs

namespace Work.EKLProd

/-- Conjugation identity: pushing the diagonal element `α^n` through the product `g * u`.

Both sides are `• x` applied to the same group element: the left is `α^n * (g * u)`, the right
collapses (via `mul_smul`) to `(g * (α^n * u * (α^n)⁻¹)) * α^n = g * (α^n * u)`, and these agree
because `α^n` commutes with `g` (hypothesis `hc`). -/
theorem pow_smul_mul_smul {t : Fin 3 → ℝ} (n : ℕ) {g u : Work.EKLContract.SL3}
    (hc : (Work.EKLContract.aDiag t)^n * g = g * (Work.EKLContract.aDiag t)^n)
    (x : Work.EKLContract.X3) :
    (Work.EKLContract.aDiag t)^n • ((g * u) • x)
      = g • (((Work.EKLContract.aDiag t)^n * u * ((Work.EKLContract.aDiag t)^n)⁻¹)
          • ((Work.EKLContract.aDiag t)^n • x)) := by
  -- Reassociate both sides so that the group element acts directly on `x`.
  rw [← mul_smul, ← mul_smul, ← mul_smul]
  congr 1
  -- The remaining goal is an identity of group elements, `g = (α^n)⁻¹ * g * (α^n)`, obtained
  -- by conjugating the commutation hypothesis `hc` with `(α^n)⁻¹`.
  have hg : ((Work.EKLContract.aDiag t)^n)⁻¹ * g * (Work.EKLContract.aDiag t)^n = g := by
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  conv_lhs => rw [← hg]
  group

end Work.EKLProd
