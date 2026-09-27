import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.mvN_additive

namespace Work.KT.K0Prod

/-! ## Elementary rewrites of `mulCls` on idempotents -/

lemma mulCls_of_idem {A : Type} [Ring A] (p q : Mat A) (hp : p.IsIdem) (hq : q.IsIdem) :
    mulCls p q = cls (p.kron q) := by
  unfold mulCls; rw [if_pos ⟨hp, hq⟩]

lemma mulCls_of_not_idem_left {A : Type} [Ring A] (p q : Mat A) (hp : ¬ p.IsIdem) :
    mulCls p q = 0 := by
  unfold mulCls; rw [if_neg (fun h => hp h.1)]

lemma mulCls_of_not_idem_right {A : Type} [Ring A] (p q : Mat A) (hq : ¬ q.IsIdem) :
    mulCls p q = 0 := by
  unfold mulCls; rw [if_neg (fun h => hq h.2)]

/-- `Work.KT.mulCls` (`[p]·[q] := [p ⊗ q]` on generators, zero if either factor is not idempotent)
is additive in each variable separately, on idempotents: the Kronecker product distributes over
block sums up to Murray--von Neumann equivalence (`Work.KT.mvN_additive`), so on classes one uses
`Work.KT.cls_eq_of_mvN` and `Work.KT.cls_sum`. -/
theorem mulCls_add (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) :
    (∀ (p q r : Work.KT.Mat A), q.IsIdem → r.IsIdem →
      Work.KT.mulCls p (q.sum r) = Work.KT.mulCls p q + Work.KT.mulCls p r) ∧
    (∀ (p q r : Work.KT.Mat A), p.IsIdem → q.IsIdem →
      Work.KT.mulCls (p.sum q) r = Work.KT.mulCls p r + Work.KT.mulCls q r) := by
  constructor
  · intro p q r hq hr
    by_cases hp : p.IsIdem
    · rw [mulCls_of_idem p (q.sum r) hp (Mat.sum_idem hq hr),
          mulCls_of_idem p q hp hq, mulCls_of_idem p r hp hr,
          ← cls_sum (Mat.kron_idem hcomm hp hq) (Mat.kron_idem hcomm hp hr)]
      exact cls_eq_of_mvN (Mat.kron_idem hcomm hp (Mat.sum_idem hq hr))
        (Mat.sum_idem (Mat.kron_idem hcomm hp hq) (Mat.kron_idem hcomm hp hr))
        (mvN_additive.1 A p q r)
    · rw [mulCls_of_not_idem_left p (q.sum r) hp, mulCls_of_not_idem_left p q hp,
          mulCls_of_not_idem_left p r hp, zero_add]
  · intro p q r hp hq
    by_cases hr : r.IsIdem
    · rw [mulCls_of_idem (p.sum q) r (Mat.sum_idem hp hq) hr,
          mulCls_of_idem p r hp hr, mulCls_of_idem q r hq hr,
          ← cls_sum (Mat.kron_idem hcomm hp hr) (Mat.kron_idem hcomm hq hr)]
      exact cls_eq_of_mvN (Mat.kron_idem hcomm (Mat.sum_idem hp hq) hr)
        (Mat.sum_idem (Mat.kron_idem hcomm hp hr) (Mat.kron_idem hcomm hq hr))
        (mvN_additive.2 A p q r)
    · rw [mulCls_of_not_idem_right (p.sum q) r hr, mulCls_of_not_idem_right p r hr,
          mulCls_of_not_idem_right q r hr, add_zero]

end Work.KT.K0Prod
