import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASEntries

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

/-- `asM w i j = (w + i)^j` is a Vandermonde matrix in the five distinct nodes
`w, w+1, …, w+4`, so its determinant is the constant `∏_{i<j} (j - i) = 288`.

This is `Matrix.det_vandermonde` followed by the evaluation of the (constant) double product
`∏_i ∏_{j>i} ((w+j) - (w+i))`: each factor is the natural-number difference `j - i`, and the
resulting product over `Fin 5` is `1! · 2! · 3! · 4! = 288`. -/
theorem asM_det {R : Type*} [CommRing R] (w : R) : (Work.MotAS.asM w).det = 288 := by
  -- The inner Vandermonde factors are the natural-number differences `j - i`.
  have hfac : ∀ i j : Fin 5, i < j → (w + ↑↑j - (w + ↑↑i)) = ((j.val - i.val : ℕ) : R) := by
    intro i j hij
    rw [add_sub_add_left_eq_sub, ← Nat.cast_sub (Nat.le_of_lt hij)]
  -- Rewrite the whole (constant) product as the cast of a product in `ℕ`.
  have hprod : (∏ i : Fin 5, ∏ j ∈ Finset.Ioi i, (w + ↑↑j - (w + ↑↑i)))
      = ((∏ i : Fin 5, ∏ j ∈ Finset.Ioi i, (j.val - i.val : ℕ)) : ℕ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl ?_
    intro j hj
    exact hfac i j (Finset.mem_Ioi.mp hj)
  rw [show Work.MotAS.asM w = Matrix.vandermonde (fun i : Fin 5 => w + (i : ℕ)) from rfl]
  rw [Matrix.det_vandermonde]
  rw [hprod]
  have hnat : (∏ i : Fin 5, ∏ j ∈ Finset.Ioi i, (j.val - i.val : ℕ)) = 288 := by decide
  rw [hnat]
  norm_num

end Work.MotAS
