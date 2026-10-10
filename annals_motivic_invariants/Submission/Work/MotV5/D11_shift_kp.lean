import Mathlib
import Submission.Work.MotV5.exists_kleinData_ASGood
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

open Work.MotV5

/-- **The five Klein-coordinate shift identities** (the computation behind
`Work.MotV5.exists_kleinData_shiftProj`).

In an arbitrary field `F` of characteristic `5`, for `x, y : F` with `y² - y = x³ - x²` and
`x ≠ 0`, put `u = y/x²`, `v = 1/x - y/x³` (the image of the generic point `(x,y)` under translation
by the `5`-torsion point `(0,0)` of `E : y² - y = x³ - x²`) and `κ_i = kp_i(x,y)`, where
`kp_0 = 1`, `kp_1 = 1 + 4y + x + 4xy + 4x²`, `kp_2 = 4 + 3x + 4xy + 3x²`, `kp_3 = 4 + 2x + xy + 3x²`,
`kp_4 = y + xy + 4x²` are the `Work.MotV5` Klein coordinates of `D11` (defined in
`Submission/Work/MotV5/exists_kleinData_ASGood.lean`).  Then, cyclically in `Fin 5`,
`κ_i(u,v) · κ_1(x,y) = κ_{i+1}(x,y)`.  (For `i = 4` this also gives `κ_1(x,y) ≠ 0`.) -/
theorem D11_shift_kp {F : Type} [Field F] [CharP F 5] (x y : F)
    (hrel : y ^ 2 - y - x ^ 3 + x ^ 2 = 0) (hx : x ≠ 0) :
    kp0 (y / x ^ 2) (1 / x - y / x ^ 3) * kp1 x y = kp1 x y ∧
    kp1 (y / x ^ 2) (1 / x - y / x ^ 3) * kp1 x y = kp2 x y ∧
    kp2 (y / x ^ 2) (1 / x - y / x ^ 3) * kp1 x y = kp3 x y ∧
    kp3 (y / x ^ 2) (1 / x - y / x ^ 3) * kp1 x y = kp4 x y ∧
    kp4 (y / x ^ 2) (1 / x - y / x ^ 3) * kp1 x y = kp0 x y := by
  -- in characteristic `5` we have `5 = 0`; this is used to reduce the polynomial
  -- identities modulo the curve relation (all residuals below are divisible by `5`)
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `kp₀ = 1`
    unfold kp0
    first | refl_ring1 | ring
  · -- `i = 0`: `κ₁(u,v)·κ₁(x,y) = κ₂(x,y)`
    unfold kp1 kp2
    field_simp
    linear_combination (norm := first | refl_ring1 | ring1)
        (-x ^ 4 - 15 * x ^ 3 - 24 * x ^ 2 * y - 16 * x ^ 2 - 5 * x * y ^ 2 - 40 * x * y
            - 20 * x - 40 * y ^ 2 - 26 * y - 20) * hrel
      + (8 * x ^ 2 * y ^ 3 + 4 * x ^ 2 * y ^ 2 + 2 * x ^ 2 * y + 4 * x ^ 2 + x * y ^ 4
            + 7 * x * y ^ 3 - 4 * x * y ^ 2 - 4 * x * y + 8 * y ^ 4 - 6 * y ^ 3 - 2 * y ^ 2
            - 4 * y) * h5
  · -- `i = 1`: `κ₂(u,v)·κ₁(x,y) = κ₃(x,y)`
    unfold kp1 kp2 kp3
    field_simp
    linear_combination (norm := first | refl_ring1 | ring1)
        (-13 * x ^ 4 - 15 * x ^ 3 * y - 15 * x ^ 3 - 43 * x ^ 2 * y - 15 * x ^ 2
            - 25 * x * y ^ 2 - 49 * x * y - 15 * x - 15 * y ^ 3 - 65 * y ^ 2 - 41 * y
            - 15) * hrel
      + (14 * x ^ 2 * y ^ 3 + 8 * x ^ 2 * y ^ 2 + 6 * x ^ 2 * y + 3 * x ^ 2 + 5 * x * y ^ 4
            + 4 * x * y ^ 3 - 7 * x * y ^ 2 - 3 * x * y + 3 * y ^ 5 + 10 * y ^ 4 - 8 * y ^ 3
            - 6 * y ^ 2 - 3 * y) * h5
  · -- `i = 2`: `κ₃(u,v)·κ₁(x,y) = κ₄(x,y)`
    unfold kp1 kp3 kp4
    field_simp
    linear_combination (norm := first | refl_ring1 | ring1)
        (-12 * x ^ 4 - 15 * x ^ 3 * y - 16 * x ^ 3 - 38 * x ^ 2 * y - 20 * x ^ 2
            - 20 * x * y ^ 2 - 32 * x * y - 20 * x - 15 * y ^ 3 - 45 * y ^ 2 - 19 * y
            - 20) * hrel
      + (13 * x ^ 2 * y ^ 3 + 6 * x ^ 2 * y ^ 2 + 4 * x ^ 2 + 4 * x * y ^ 4 + 4 * x * y ^ 3
            - 2 * x * y ^ 2 - 4 * x * y + 3 * y ^ 5 + 6 * y ^ 4 - 6 * y ^ 3 - 4 * y) * h5
  · -- `i = 3`: `κ₄(u,v)·κ₁(x,y) = κ₀(x,y) = 1`
    unfold kp0 kp1 kp4
    field_simp
    linear_combination (norm := first | refl_ring1 | ring1)
        (-4 * x ^ 3 - 4 * x ^ 2 * y - 4 * x ^ 2 - 8 * x * y - 5 * x - 20 * y ^ 2 - 4 * y
            - 5) * hrel
      + (4 * x ^ 2 * y ^ 3 + 4 * x ^ 2 * y ^ 2 + x ^ 2 + 4 * x * y ^ 3 - x * y + 4 * y ^ 4
            - 4 * y ^ 3 - y) * h5

end Work.MotV5
