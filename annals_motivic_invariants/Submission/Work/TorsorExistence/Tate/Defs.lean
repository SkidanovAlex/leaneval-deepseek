/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TorsorExistence.Tate
-/
import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Tate normal form for `X₁(5)`

This file sets up the curve

`tateCurve c : y² + (1 - c)xy - cy = x³ - cx²`,  i.e. `(a₁, a₂, a₃, a₄, a₆) = (1 - c, -c, -c, 0, 0)`,

whose affine point `T = (0, 0)` satisfies `2T = (c, c²)`, `4T = (0, c) = -T`, hence `5T = 0`.
The curve is the classical Tate normal form for the modular curve `X₁(5)`: over any field in
which `c` is chosen so that `Δ = c⁵(c² - 11c - 1) ≠ 0`, it is an elliptic curve with a rational
point of exact order `5`.

The purpose of this file is only to fix the notation used by the group-law lemmas
(`tateCurve`, `tateCurve_Δ`, `tateCurve_c₄`, the affine points `(0,0)`, `(c,c²)`, `(0,c)`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.TorsorExistence.Tate

open WeierstrassCurve WeierstrassCurve.Affine

variable {𝕜 : Type} [Field 𝕜]

/-- **The Tate normal form.**  `E(c) : y² + (1 - c)xy - cy = x³ - cx²`. -/
def tateCurve (c : 𝕜) : WeierstrassCurve 𝕜 := ⟨1 - c, -c, -c, 0, 0⟩

@[simp] lemma tateCurve_a₁ (c : 𝕜) : (tateCurve c).a₁ = 1 - c := rfl
@[simp] lemma tateCurve_a₂ (c : 𝕜) : (tateCurve c).a₂ = -c := rfl
@[simp] lemma tateCurve_a₃ (c : 𝕜) : (tateCurve c).a₃ = -c := rfl
@[simp] lemma tateCurve_a₄ (c : 𝕜) : (tateCurve c).a₄ = 0 := rfl
@[simp] lemma tateCurve_a₆ (c : 𝕜) : (tateCurve c).a₆ = 0 := rfl

/-- The discriminant of the Tate normal form: `Δ = c⁵(c² - 11c - 1)`. -/
lemma tateCurve_Δ (c : 𝕜) : (tateCurve c).Δ = c ^ 5 * (c ^ 2 - 11 * c - 1) := by
  simp only [tateCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  first | refl_ring1 | ring

/-- The invariant `c₄` of the Tate normal form: `c₄ = c⁴ - 12c³ + 14c² + 12c + 1`. -/
lemma tateCurve_c₄ (c : 𝕜) :
    (tateCurve c).c₄ = c ^ 4 - 12 * c ^ 3 + 14 * c ^ 2 + 12 * c + 1 := by
  simp only [tateCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  first | refl_ring1 | ring

/-- `(0, 0)` is on the Tate normal form. -/
lemma tateCurve_equation_zero (c : 𝕜) : Equation (tateCurve c) 0 0 := by
  rw [equation_iff]
  simp only [tateCurve]
  first | refl_ring1 | ring

/-- `(c, c²) = 2T` is on the Tate normal form. -/
lemma tateCurve_equation_self (c : 𝕜) : Equation (tateCurve c) c (c ^ 2) := by
  rw [equation_iff]
  simp only [tateCurve]
  first | refl_ring1 | ring

/-- `(0, c) = -T` is on the Tate normal form. -/
lemma tateCurve_equation_dbl (c : 𝕜) : Equation (tateCurve c) 0 c := by
  rw [equation_iff]
  simp only [tateCurve]
  first | refl_ring1 | ring

/-- The `Y`-coordinate of `-(0,0)` on the Tate normal form is `c`. -/
lemma tateCurve_negY_zero (c : 𝕜) : negY (tateCurve c) 0 0 = c := by
  simp only [WeierstrassCurve.Affine.negY, tateCurve]
  first | refl_ring1 | ring

end Work.TorsorExistence.Tate
