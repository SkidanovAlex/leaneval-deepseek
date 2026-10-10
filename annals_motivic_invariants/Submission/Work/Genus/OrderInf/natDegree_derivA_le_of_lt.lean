import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial

namespace Work.Genus.OrderInf

/-- **Strict-degree case of the `X^(2 deg)`-vanishing bound for `p' q - p q'`.**
If `q ≠ 0` and `natDegree p < natDegree q` then `p.derivative * q - p * q.derivative` has degree at
most `2 * natDegree q - 2` (ℤ formulation). -/
theorem natDegree_derivA_le_of_lt {F : Type*} [Field F] (p q : Polynomial F) (hq : q ≠ 0)
    (hlt : p.natDegree < q.natDegree) :
    ((p.derivative * q - p * q.derivative).natDegree : ℤ) ≤ 2 * (q.natDegree : ℤ) - 2 := by
  have hn : 1 ≤ q.natDegree := by omega
  -- Degree bound for the `p * q'` term.
  have hB : (p * q.derivative).natDegree ≤ 2 * q.natDegree - 2 := by
    calc (p * q.derivative).natDegree ≤ p.natDegree + q.derivative.natDegree := natDegree_mul_le
      _ ≤ p.natDegree + (q.natDegree - 1) :=
            Nat.add_le_add_left (natDegree_derivative_le q) _
      _ ≤ 2 * q.natDegree - 2 := by omega
  -- Degree bound for the `p' * q` term.
  have hA : (p.derivative * q).natDegree ≤ 2 * q.natDegree - 2 := by
    rcases eq_or_ne p.natDegree 0 with h0 | h0
    · -- `p` is constant, hence `p' = 0`.
      rw [derivative_of_natDegree_zero h0, zero_mul, natDegree_zero]
      omega
    · calc (p.derivative * q).natDegree ≤ p.derivative.natDegree + q.natDegree := natDegree_mul_le
        _ ≤ (p.natDegree - 1) + q.natDegree :=
              Nat.add_le_add_right (natDegree_derivative_le p) _
        _ ≤ 2 * q.natDegree - 2 := by omega
  have hcast : ((2 * q.natDegree - 2 : ℕ) : ℤ) = 2 * (q.natDegree : ℤ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * q.natDegree)]
    push_cast
    first | refl_ring1 | ring
  calc ((p.derivative * q - p * q.derivative).natDegree : ℤ)
      ≤ ((2 * q.natDegree - 2 : ℕ) : ℤ) := by
        exact_mod_cast (natDegree_sub_le _ _).trans (max_le hA hB)
    _ = 2 * (q.natDegree : ℤ) - 2 := hcast

end Work.Genus.OrderInf
