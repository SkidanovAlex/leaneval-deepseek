import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.hk_k0_eq_diff
import Submission.Work.KT.rel_cancel

namespace Work.KT

open Matrix

noncomputable section

variable {R : Type} [Ring R]

/-- **Normal form for `K₀`**: every element is the difference of the class of an idempotent matrix and the class of an identity matrix (no relation between the two sizes is required). Hints: `cls (p.sum q) = cls p + cls q` (`cls_sum`); for idempotent `p`, `cls p = cls (p.sum (Mat.one R k)) - cls (Mat.one R k)`; for non-idempotent `p`, `cls p = 0` (`cls_of_not_idem`); `cls (Mat.one R (m+n)) = cls (Mat.one R m) + cls (Mat.one R n)`, so the negative part of a difference can be enlarged; `-(cls F - cls 1_n) = cls (Mat.one R n).sum (1 - F) - cls (Mat.one R F.1)` using that `F ⊕ (1-F) ~ 1`; and `z` is a `FreeAbelianGroup` combination of generators. -/
theorem k0_rep {R : Type} [Ring R] (z : K0 R) :
    ∃ (F : Mat R) (n : ℕ), F.IsIdem ∧ z = cls F - cls (Mat.one R n) := by
  -- Every element is the difference of two idempotents of a common size.
  obtain ⟨m, P, Q, hP, hQ, hz⟩ := hk_k0_eq_diff R z
  have hidP : Mat.IsIdem (⟨m, P⟩ : Mat R) := hP
  have hidQ : Mat.IsIdem (⟨m, Q⟩ : Mat R) := hQ
  -- The complementary idempotent `1 - Q`.
  have hQc : Mat.IsIdem (⟨m, 1 - Q⟩ : Mat R) := Mat.isIdem_one_sub hidQ
  -- `Q ⊕ (1 - Q) ~ 1_m`, hence `cls Q + cls (1 - Q) = cls 1_m`.
  have hQsum : cls (Mat.sum (⟨m, Q⟩ : Mat R) ⟨m, 1 - Q⟩) = cls (Mat.one R m) :=
    cls_eq_of_mvN (Mat.sum_idem hidQ hQc) (Mat.one_isIdem R m)
      (mvN_sum_compl R (⟨m, Q⟩ : Mat R) hidQ)
  have hsplit : cls (Mat.sum (⟨m, Q⟩ : Mat R) ⟨m, 1 - Q⟩) =
      cls (⟨m, Q⟩ : Mat R) + cls ⟨m, 1 - Q⟩ := cls_sum hidQ hQc
  have hQeq : cls (⟨m, Q⟩ : Mat R) = cls (Mat.one R m) - cls ⟨m, 1 - Q⟩ := by
    rw [eq_sub_iff_add_eq]
    exact hsplit.symm.trans hQsum
  refine ⟨Mat.sum (⟨m, P⟩ : Mat R) ⟨m, 1 - Q⟩, m, Mat.sum_idem hidP hQc, ?_⟩
  rw [hz, hQeq, cls_sum hidP hQc]
  abel

end

end Work.KT
