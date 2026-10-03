import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs

set_option autoImplicit false

namespace Work.ORHughesFree.NaturalExtension

/-- The ring homomorphism `Matₙ(R) → Matₙ(R ⧸ I)` obtained by applying the quotient map
entrywise.  Its kernel is the ideal of matrices all of whose entries lie in `I`. -/
def matrixQuotMap {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →+* Matrix (Fin n) (Fin n) (R ⧸ I) :=
  RingHom.mapMatrix (Ideal.Quotient.mk I)

@[simp]
theorem matrixQuotMap_apply {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    matrixQuotMap I n M i j = Ideal.Quotient.mk I (M i j) :=
  rfl

end Work.ORHughesFree.NaturalExtension
