import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.mvN_comm

namespace Work.KT.K0Prod

/-- `Work.KT.mulCls` (`[p]·[q] := [p ⊗ q]` on generators, zero if either factor is not
idempotent) respects Murray--von Neumann equivalence in each variable: the Kronecker product of
idempotents is idempotent over a commutative ring (`Work.KT.Mat.kron_idem`), and `Mat.MvN` is
respected by `Mat.kron` (`Work.KT.mvN_kron_left`, `Work.KT.mvN_kron_right`). -/
theorem mulCls_mvN (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) :
    (∀ (p p' q : Work.KT.Mat A), p.IsIdem → p'.IsIdem → Work.KT.Mat.MvN p p' →
      Work.KT.mulCls p q = Work.KT.mulCls p' q) ∧
    (∀ (p q q' : Work.KT.Mat A), q.IsIdem → q'.IsIdem → Work.KT.Mat.MvN q q' →
      Work.KT.mulCls p q = Work.KT.mulCls p q') := by
  classical
  constructor
  · intro p p' q hp hp' hpp'
    by_cases hq : q.IsIdem
    · rw [Work.KT.mulCls, if_pos ⟨hp, hq⟩, Work.KT.mulCls, if_pos ⟨hp', hq⟩]
      exact Work.KT.cls_eq_of_mvN (Work.KT.Mat.kron_idem hcomm hp hq)
        (Work.KT.Mat.kron_idem hcomm hp' hq) (Work.KT.mvN_kron_left hcomm hpp' hq)
    · rw [Work.KT.mulCls, if_neg (fun h => hq h.2), Work.KT.mulCls, if_neg (fun h => hq h.2)]
  · intro p q q' hq hq' hqq'
    by_cases hp : p.IsIdem
    · rw [Work.KT.mulCls, if_pos ⟨hp, hq⟩, Work.KT.mulCls, if_pos ⟨hp, hq'⟩]
      exact Work.KT.cls_eq_of_mvN (Work.KT.Mat.kron_idem hcomm hp hq)
        (Work.KT.Mat.kron_idem hcomm hp hq') (Work.KT.mvN_kron_right hcomm hqq' hp)
    · rw [Work.KT.mulCls, if_neg (fun h => hp h.1), Work.KT.mulCls, if_neg (fun h => hp h.1)]

end Work.KT.K0Prod
