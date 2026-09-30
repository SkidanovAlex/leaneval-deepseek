import Mathlib
import Submission.Work.Certificates.Sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates.SOp

/-! ### Auxiliary facts about `SVec.toFun`

These are the pointwise facts comparing the sparse-list operations `++` and coefficient-wise
negation with the corresponding operations on functions `Fin n → ℤ`.  They are kept in their own
namespace so that they cannot collide with the auxiliary lemmas of the sibling files. -/

namespace SubAux

/-- `SVec.toFun` is additive with respect to concatenation of sparse vectors. -/
theorem toFun_append {n : ℕ} (a b : SVec n) :
    SVec.toFun (a ++ b) = SVec.toFun a + SVec.toFun b := by
  funext i
  simp [SVec.toFun, List.map_append, List.sum_append, Pi.add_apply]

/-- Negating the coefficients of a sparse vector negates its semantics. -/
theorem toFun_map_neg {n : ℕ} (a : SVec n) :
    SVec.toFun (a.map (fun q : Fin n × ℤ => (q.1, -q.2))) = -SVec.toFun a := by
  funext i
  simp only [SVec.toFun, Pi.neg_apply]
  rw [List.sum_neg, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  by_cases h : p.1 = i <;> simp [h]

end SubAux

theorem toMatrix_sub {n m : ℕ} (A B : SOp n m) :
    toMatrix (sub A B) = toMatrix A - toMatrix B := by
  ext i j
  simp only [toMatrix, sub, add, neg]
  rw [SubAux.toFun_append, SubAux.toFun_map_neg, sub_eq_add_neg]
  simp [Pi.add_apply, Pi.neg_apply, toMatrix]

end Work.Certificates.SOp
