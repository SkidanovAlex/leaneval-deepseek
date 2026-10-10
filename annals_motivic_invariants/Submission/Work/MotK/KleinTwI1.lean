/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.KleinTwData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The twisted inverse relation I1' for the Klein model

The T-twist (Kummer coordinates `x_i = w^i y_i`, `w^5 = h`) of the inverse identity
I1 `R_i(p(x)) = s(x) x_i` of `Submission/Work/MotK/KleinIdents`:

`kleinTwR a b h (kleinTwP a b h y) k = kleinTwS a b h y * y k`.

Note the *inverse* twist `z_j = w^{4j} y_j` in `kleinTwR`: with the grading
`deg y_i = i mod 5` and `kleinTwR_k` of index degree `-k`, the substitution `z_j = w^{4j} y_j`
carries `w^{-4k} = w^{k}` (`w^5 = h`), which is why no extra power of `w` appears.

Proved componentwise (`fin_cases` on `k`) by rewriting with the definitions and `ring`, the
same recipe as `KleinIdents`.  Verified in the CAS by `cas/s08_twist.py` (identity I1').
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-! ## Component (`rfl`) lemmas for the twisted data -/

theorem kleinTwP_zero (a b h : R) (y : Fin 5 → R) : kleinTwP a b h y 0 = kleinTwP0 a b h y := rfl
theorem kleinTwP_one (a b h : R) (y : Fin 5 → R) : kleinTwP a b h y 1 = kleinTwP1 a b h y := rfl
theorem kleinTwP_two (a b h : R) (y : Fin 5 → R) : kleinTwP a b h y 2 = kleinTwP2 a b h y := rfl
theorem kleinTwP_three (a b h : R) (y : Fin 5 → R) : kleinTwP a b h y 3 = kleinTwP3 a b h y := rfl
theorem kleinTwP_four (a b h : R) (y : Fin 5 → R) : kleinTwP a b h y 4 = kleinTwP4 a b h y := rfl

theorem kleinTwR_zero (a b h : R) (y : Fin 5 → R) : kleinTwR a b h y 0 = kleinTwR0 a b h y := rfl
theorem kleinTwR_one (a b h : R) (y : Fin 5 → R) : kleinTwR a b h y 1 = kleinTwR1 a b h y := rfl
theorem kleinTwR_two (a b h : R) (y : Fin 5 → R) : kleinTwR a b h y 2 = kleinTwR2 a b h y := rfl
theorem kleinTwR_three (a b h : R) (y : Fin 5 → R) : kleinTwR a b h y 3 = kleinTwR3 a b h y := rfl
theorem kleinTwR_four (a b h : R) (y : Fin 5 → R) : kleinTwR a b h y 4 = kleinTwR4 a b h y := rfl

/-! ## I1': `kleinTwR_k(kleinTwP) = kleinTwS · y_k`, componentwise -/

theorem kleinTwI1_zero (a b h : R) (y : Fin 5 → R) :
    kleinTwR a b h (kleinTwP a b h y) 0 = kleinTwS a b h y * y 0 := by
  simp only [kleinTwR_zero, kleinTwR0, kleinTwP_zero, kleinTwP_one, kleinTwP_two, kleinTwP_three,
    kleinTwP_four, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4, kleinTwS]
  first | refl_ring1 | ring

theorem kleinTwI1_one (a b h : R) (y : Fin 5 → R) :
    kleinTwR a b h (kleinTwP a b h y) 1 = kleinTwS a b h y * y 1 := by
  simp only [kleinTwR_one, kleinTwR1, kleinTwP_zero, kleinTwP_one, kleinTwP_two, kleinTwP_three,
    kleinTwP_four, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4, kleinTwS]
  first | refl_ring1 | ring

theorem kleinTwI1_two (a b h : R) (y : Fin 5 → R) :
    kleinTwR a b h (kleinTwP a b h y) 2 = kleinTwS a b h y * y 2 := by
  simp only [kleinTwR_two, kleinTwR2, kleinTwP_zero, kleinTwP_one, kleinTwP_two, kleinTwP_three,
    kleinTwP_four, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4, kleinTwS]
  first | refl_ring1 | ring

theorem kleinTwI1_three (a b h : R) (y : Fin 5 → R) :
    kleinTwR a b h (kleinTwP a b h y) 3 = kleinTwS a b h y * y 3 := by
  simp only [kleinTwR_three, kleinTwR3, kleinTwP_zero, kleinTwP_one, kleinTwP_two, kleinTwP_three,
    kleinTwP_four, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4, kleinTwS]
  first | refl_ring1 | ring

theorem kleinTwI1_four (a b h : R) (y : Fin 5 → R) :
    kleinTwR a b h (kleinTwP a b h y) 4 = kleinTwS a b h y * y 4 := by
  simp only [kleinTwR_four, kleinTwR4, kleinTwP_zero, kleinTwP_one, kleinTwP_two, kleinTwP_three,
    kleinTwP_four, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4, kleinTwS]
  first | refl_ring1 | ring

/-- **I1'** (T-twist of the inverse relation): `R_k(p(y)) = s(y) · y_k` in Kummer coordinates. -/
theorem KleinTwI1 {R : Type*} [CommRing R] (a b h : R) (y : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinTwR a b h (Work.MotK.kleinTwP a b h y) k = Work.MotK.kleinTwS a b h y * y k := by
  fin_cases k
  · change kleinTwR a b h (kleinTwP a b h y) 0 = kleinTwS a b h y * y 0
    exact kleinTwI1_zero a b h y
  · change kleinTwR a b h (kleinTwP a b h y) 1 = kleinTwS a b h y * y 1
    exact kleinTwI1_one a b h y
  · change kleinTwR a b h (kleinTwP a b h y) 2 = kleinTwS a b h y * y 2
    exact kleinTwI1_two a b h y
  · change kleinTwR a b h (kleinTwP a b h y) 3 = kleinTwS a b h y * y 3
    exact kleinTwI1_three a b h y
  · change kleinTwR a b h (kleinTwP a b h y) 4 = kleinTwS a b h y * y 4
    exact kleinTwI1_four a b h y

end Work.MotK
