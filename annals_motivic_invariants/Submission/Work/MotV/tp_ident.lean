import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.TpAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Route V, node TP: the fifth-power monomial identities

For the quadric of the twisted Klein curve whose square monomial is `y_j ^ 2` (that is, the quadric
with index `k = 3 * j`), the three monomials are the square `(j, j)`, the consecutive pair
`(j + 2, j + 3)` and the distance-two pair `(j + 1, j + 4)`.  The fifth power of the value of each
of them, scaled by the fixed fifth power `(v h) ^ (rr j)`, is the corresponding product of weights
`wt i = (v h) ^ i * (v (y i)) ^ 5`.

This is the arithmetic content of the index identity `i + l ≡ 4 * k (mod 5)` for the three pairs
of the `k`-th quadric, together with the fact that the value of `twMon h y i l` is `1`, `v h` or
`v h ^ 2` times `v (y i) * v (y l)` according to whether `i + l` is `< 5` or `≥ 5`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

noncomputable section

/-- The three fifth-power monomial identities of the quadric with square monomial `y_j ^ 2`. -/
theorem tp_ident {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) (h : F) (y : Fin 5 → F) (j : Fin 5) :
    (v (twMon h y j j)) ^ 5 * (v h) ^ rr j = wt v h y j * wt v h y j ∧
    (v (twMon h y (j + 2) (j + 3))) ^ 5 * (v h) ^ rr j
        = wt v h y (j + 2) * wt v h y (j + 3) ∧
    (v (twMon h y (j + 1) (j + 4))) ^ 5 * (v h) ^ rr j
        = wt v h y (j + 1) * wt v h y (j + 4) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (fin_cases j <;>
      simp [wt, rr, twMon, map_mul, pow_succ, pow_zero] <;>
      simp only [mul_comm, mul_left_comm, mul_assoc])

end

end Work.MotV
