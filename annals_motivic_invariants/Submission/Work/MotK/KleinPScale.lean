import Mathlib
import Submission.Work.MotK.KleinData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Weight of the Klein--Fisher Pfaffians under diagonal rescaling

`kleinP a b` is the Pfaffian vector of the skew matrix `M_{i j} = c_{j-i} x_{i+j}`.
Every monomial of the `k`-th Pfaffian `p_k` has index sum `≡ -k (mod 5)`; hence for a
fifth root of unity `ζ` the diagonal substitution `x_i ↦ ζ^i z_i` rescales `p_k` by
`ζ^{-k} = ζ^{5-k}`.  This is the `μ_5`-weight of the Klein coordinates and is the
elementary input of the `T`-eigen-scheme (`coord`, `T_diag`).
-/

namespace Work.MotK

theorem KleinPScale {R : Type*} [CommRing R] (a b ζ : R) (hζ : ζ ^ 5 = 1) (z : Fin 5 → R)
    (k : Fin 5) :
    Work.MotK.kleinP a b (fun i : Fin 5 => ζ ^ (i : ℕ) * z i) k =
      ζ ^ (5 - (k : ℕ)) * Work.MotK.kleinP a b z k := by
  fin_cases k <;>
    simp only [kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four',
      kleinP0, kleinP1, kleinP2, kleinP3, kleinP4] <;>
    norm_num
  · ring_nf
    rw [hζ]
    first | refl_ring1 | ring
  · ring_nf
  · ring_nf
    rw [show ζ ^ 8 = ζ ^ 3 from by rw [show (8 : ℕ) = 5 + 3 from rfl, pow_add, hζ, one_mul]]
  · ring_nf
    rw [show ζ ^ 7 = ζ ^ 2 from by rw [show (7 : ℕ) = 5 + 2 from rfl, pow_add, hζ, one_mul]]
  · ring_nf
    rw [show ζ ^ 6 = ζ ^ 1 from by rw [show (6 : ℕ) = 5 + 1 from rfl, pow_add, hζ, one_mul]]
    first | refl_ring1 | ring

end Work.MotK
