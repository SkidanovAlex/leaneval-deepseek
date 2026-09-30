import Mathlib
import Submission.Work.Certificates.Sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates.SVec

/-- Pointwise form of `toFun` on a cons: the contribution of the head plus the tail. -/
private theorem toFun_cons_apply {n : ℕ} (p : Fin n × ℤ) (l : List (Fin n × ℤ)) (i : Fin n) :
    toFun (p :: l) i = (if p.1 = i then p.2 else 0) + toFun l i := by
  simp [toFun, List.map_cons, List.sum_cons]

/-- Pointwise form of `toFun` on a singleton. -/
private theorem toFun_single_apply {n : ℕ} (p : Fin n × ℤ) (i : Fin n) :
    toFun ([p] : List (Fin n × ℤ)) i = if p.1 = i then p.2 else 0 := by
  simp [toFun]

/-- `insert p` adds the contribution of `p` to the sparse vector, as a function `Fin n → ℤ`.
Insertion into an *arbitrary* list (not necessarily with strictly increasing indices) still
preserves `toFun` up to the summand `toFun [p]`: this is the content of the three branches of
`insert` (place before, merge at an equal index, recurse past a smaller index), the zero
coefficient cases being handled by cancellation. -/
theorem toFun_insert {n : ℕ} (p : Fin n × ℤ) (l : List (Fin n × ℤ)) :
    toFun (insert p l) = toFun ([p] : List (Fin n × ℤ)) + toFun l := by
  have key : ∀ (l : List (Fin n × ℤ)) (i : Fin n),
      toFun (insert p l) i = toFun ([p] : List (Fin n × ℤ)) i + toFun l i := by
    intro l
    induction l with
    | nil =>
      intro i
      rw [insert]
      by_cases h : p.2 = 0
      · rw [ite_eq_left h]; simp [toFun, h]
      · rw [ite_eq_right h]; simp [toFun]
    | cons q qs ih =>
      intro i
      rw [insert]
      by_cases hlt : p.1 < q.1
      · rw [ite_eq_left hlt]
        by_cases hz : p.2 = 0
        · rw [ite_eq_left hz, toFun_single_apply]; simp [hz]
        · rw [ite_eq_right hz, toFun_single_apply, toFun_cons_apply]
      · rw [ite_eq_right hlt]
        by_cases heq : p.1 = q.1
        · rw [ite_eq_left heq]
          by_cases hz : p.2 + q.2 = 0
          · rw [ite_eq_left hz, toFun_single_apply, toFun_cons_apply, heq]
            by_cases hi : q.1 = i
            · simp only [hi, ite_true]; omega
            · simp [hi]
          · rw [ite_eq_right hz, toFun_single_apply, toFun_cons_apply, toFun_cons_apply, heq]
            by_cases hi : q.1 = i
            · simp only [hi, ite_true]; ring
            · simp [hi]
        · rw [ite_eq_right heq, toFun_cons_apply, ih, toFun_single_apply, toFun_cons_apply]
          ring
  funext i
  exact key l i

end Work.Certificates.SVec
