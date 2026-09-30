import Mathlib
import Submission.Work.BW.expPoly_aux
import Submission.Work.BW.expPoly_zeros

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- `Op 1` is the forward difference operator; on the level of `natDegree` it at least drops the
degree by one (in the truncated sense, which also covers the constant polynomials). -/
lemma natDegree_Op_one_le (Q : Polynomial ℂ) :
    (Op (1 : ℂ) Q).natDegree ≤ Q.natDegree - 1 := by
  have h : Op (1 : ℂ) Q = Polynomial.taylor (1 : ℂ) Q - Q := by simp [Op]
  rw [h]
  exact natDegree_taylor_one_sub_le Q

/-- When `Op 1 Q` does not vanish, it strictly lowers the degree. (The only polynomials for which
`Op 1 Q` vanishes are the constants, and for those `natDegree Q = 0`.) -/
lemma natDegree_Op_one_lt (Q : Polynomial ℂ) (hQ : Op (1 : ℂ) Q ≠ 0) :
    (Op (1 : ℂ) Q).natDegree < Q.natDegree := by
  have hle := natDegree_Op_one_le Q
  have hpos : 1 ≤ Q.natDegree := by
    by_contra h
    have h0 : Q.natDegree = 0 := by omega
    apply hQ
    rw [eq_C_of_natDegree_eq_zero h0]
    simp [Op]
  omega

/-- Invariant along the iteration of the forward difference operator: either the `m`-th iterate has
already vanished, or its degree has dropped by at least `m`. -/
lemma iterate_Op_one_eq_zero_or (m : ℕ) (Q : Polynomial ℂ) :
    ((Op (1 : ℂ))^[m]) Q = 0 ∨ (((Op (1 : ℂ))^[m]) Q).natDegree + m ≤ Q.natDegree := by
  induction m generalizing Q with
  | zero => right; simp
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    rcases ih (Op (1 : ℂ) Q) with h | h
    · exact Or.inl h
    · by_cases h0 : Op (1 : ℂ) Q = 0
      · refine Or.inl ?_
        rw [h0, Function.iterate_fixed (show Op (1 : ℂ) 0 = 0 by simp [Op])]
      · refine Or.inr ?_
        have hlt := natDegree_Op_one_lt Q h0
        omega

/-- Iterating the forward difference operator `Op 1` more than `natDegree` times kills the
polynomial. -/
theorem Op_one_iterate_zero (Q : Polynomial ℂ) :
    ((Work.BW.Op (1 : ℂ))^[Q.natDegree + 1]) Q = 0 := by
  rcases iterate_Op_one_eq_zero_or (Q.natDegree + 1) Q with h | h
  · exact h
  · omega

end Work.BW
