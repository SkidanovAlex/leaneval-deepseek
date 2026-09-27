import Mathlib
import Submission.Work.KT.Psi.cubeMvNAux

namespace Work.KT.Psi

open Matrix Kronecker

set_option linter.style.haveILetI false in
/-- The triple Kronecker product `M ↦ M ⊗ M ⊗ M` is multiplicative, as soon as the coefficient
ring is commutative.

Writing `M ⊗ₖ M ⊗ₖ M` as `(M ⊗ₖ M) ⊗ₖ M`, the two-factor identity
`Matrix.mul_kronecker_mul` gives
`((P ⊗ P) ⊗ P) * ((Q ⊗ Q) ⊗ Q) = ((P ⊗ P) * (Q ⊗ Q)) ⊗ (P * Q)`, and applying it once more to
the middle factor `(P ⊗ P) * (Q ⊗ Q) = (P * Q) ⊗ (P * Q)` yields the claim. -/
theorem kron3_mul {A : Type} [Ring A] (hA : ∀ x y : A, x * y = y * x)
    {x y z : ℕ} (P : Matrix (Fin x) (Fin y) A) (Q : Matrix (Fin y) (Fin z) A) :
    Work.KT.Psi.kron3r P * Work.KT.Psi.kron3r Q = Work.KT.Psi.kron3r (P * Q) := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  show ((P ⊗ₖ P) ⊗ₖ P) * ((Q ⊗ₖ Q) ⊗ₖ Q) = ((P * Q) ⊗ₖ (P * Q)) ⊗ₖ (P * Q)
  rw [← mul_kronecker_mul (P ⊗ₖ P) (Q ⊗ₖ Q) P Q, ← mul_kronecker_mul P Q P Q]

end Work.KT.Psi
