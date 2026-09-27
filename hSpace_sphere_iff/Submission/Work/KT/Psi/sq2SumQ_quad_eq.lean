import Mathlib
import Submission.Work.KT.Psi.psi2sum_Aux
import Submission.Work.KT.Psi.psi2sum_Setup
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Defs

namespace Work.KT.Psi

open Matrix

/-- The `ε`-projected Kronecker square `(p ⊕ q) ⊗ (p ⊕ q)`, written on the "unreindexed" index
`(Fin p.1 ⊕ Fin q.1) × (Fin p.1 ⊕ Fin q.1)`, has the following block form under the four-block
decomposition `quadEquiv`: the Kronecker square `psi2sumB` multiplied by the block form
`(1/2)(1 + ε·swap)` of the projector. -/
theorem sq2SumQ_quad_eq {A : Type} [Ring A] [Algebra ℂ A] (ε : ℂ) {p q : Work.KT.Mat A} :
    Matrix.reindex (Work.KT.Psi.quadEquiv (Fin p.1) (Fin q.1))
        (Work.KT.Psi.quadEquiv (Fin p.1) (Fin q.1))
        (Work.KT.Psi.sq2PartQ ε p q) =
      Work.KT.Psi.psi2sumB p q *
        (algebraMap ℂ A (1 / 2) • (1 + algebraMap ℂ A ε • Work.KT.Psi.psi2sumQB A p.1 q.1)) := by
  simp only [sq2PartQ]
  rw [reindex_mul', reindex_smul, reindex_add', reindex_one', reindex_smul,
    quadEquiv_kron (R := A) p.2 q.2,
    quadEquiv_perm (R := A) (ι := Fin p.1) (κ := Fin q.1)]
  rfl

end Work.KT.Psi
