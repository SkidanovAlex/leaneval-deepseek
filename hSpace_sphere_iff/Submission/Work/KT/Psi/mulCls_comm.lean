import Mathlib
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.mvN_comm

namespace Work.KT.Psi

theorem mulCls_comm {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p q : Mat A) : mulCls p q = mulCls q p := by
  classical
  unfold mulCls
  by_cases hp : p.IsIdem <;> by_cases hq : q.IsIdem
  · rw [if_pos ⟨hp, hq⟩, if_pos ⟨hq, hp⟩]
    exact cls_eq_of_mvN (Mat.kron_idem hA hp hq) (Mat.kron_idem hA hq hp)
      (mvN_kron_comm hA p q)
  · rw [if_neg (fun h => hq h.2), if_neg (fun h => hq h.1)]
  · rw [if_neg (fun h => hp h.1), if_neg (fun h => hp h.2)]
  · rw [if_neg (fun h => hp h.1), if_neg (fun h => hp h.2)]

end Work.KT.Psi
