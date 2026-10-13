/-
  WilG4c / ineqSet_mem.

  `ineqSet N` is the conclusion of the `ε`-`δ` formula, in the big space

    `(x, c, ε, δ | y, u, w)`:

    `(u - w - ∑ i, c i * (y i - x i))^2 ≤ ε^2 * ∑ i, (y i - x i)^2`.

  It is the complement of the positivity set of the single polynomial

    `ineqPoly N = (X u - X w - ∑ i, X (c i) * (X (y i) - X (x i)))^2
        - X ε^2 * ∑ i, (X (y i) - X (x i))^2`,

  whose value at `z` is the difference of the two sides.  The complement of the
  positivity set of a polynomial is `Ω`-definable by `Work.WilG1.Calc.pos_mem`
  followed by `SOMin.compl`, with format `bigDim N + 3` and degree
  `(ineqPoly N).totalDegree + 2`; hence the `∃ A B` form.
-/
import Mathlib
import Submission.Work.WilG4c.EpsSetDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.WilG4c

open WilkiesDesign

/-- The polynomial whose value at `z` is `(u - w - ∑ i, c i * (y i - x i))^2`
minus `ε^2 * ∑ i, (y i - x i)^2`.  Its positivity set is the complement of `ineqSet N`. -/
private noncomputable def ineqPoly (N : ℕ) : MvPolynomial (Fin (bigDim N)) ℝ :=
  (MvPolynomial.X (uIdx N) - MvPolynomial.X (wBigIdx N)
    - ∑ i : Fin N, MvPolynomial.X (cIdx N i) *
        (MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i))) ^ 2
  - MvPolynomial.X (eIdx N) ^ 2 *
      ∑ i : Fin N, (MvPolynomial.X (yIdx N i) - MvPolynomial.X (xIdx N i)) ^ 2

/-- Evaluation of `ineqPoly` in coordinates. -/
private theorem eval_ineqPoly (N : ℕ) (z : Fin (bigDim N) → ℝ) :
    MvPolynomial.eval z (ineqPoly N) =
      (z (uIdx N) - z (wBigIdx N) - ∑ i : Fin N, z (cIdx N i) * (z (yIdx N i) - z (xIdx N i))) ^ 2
        - z (eIdx N) ^ 2 * ∑ i : Fin N, (z (yIdx N i) - z (xIdx N i)) ^ 2 := by
  simp only [ineqPoly, map_sub, map_sum, map_mul, map_pow, MvPolynomial.eval_X]

/-- `ineqSet N` is exactly the complement of the positivity set of `ineqPoly N`. -/
private theorem ineqSet_eq (N : ℕ) :
    ineqSet N = ({z : Fin (bigDim N) → ℝ | 0 < MvPolynomial.eval z (ineqPoly N)})ᶜ := by
  ext z
  rw [ineqSet, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_ofPred_eq, eval_ineqPoly]
  constructor <;> intro h <;> linarith

theorem ineqSet_mem (S : WilkiesDesign.SOMin) (N : ℕ) :
    ∃ A B : ℕ, Work.WilG4c.ineqSet N ∈ S.Ω A B (Work.WilG4c.bigDim N) := by
  refine ⟨bigDim N + 2 + 1, (ineqPoly N).totalDegree + 2, ?_⟩
  rw [ineqSet_eq]
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := bigDim N) (D := 0) (ineqPoly N)
  simpa using S.compl h

end Work.WilG4c
