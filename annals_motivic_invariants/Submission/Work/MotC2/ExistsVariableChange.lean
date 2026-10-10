import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- Given coefficients `(a, b, c, d, e)` with `b, e ≠ 0` satisfying the six relations produced by
substituting `x ↦ a + b·x`, `y ↦ c + d·x + e·y` into the Weierstrass relation (with `e² = b³`), the
admissible change of variables `C = (e/b, a, d/b, c)` stabilises `E`: `C • E = E`.  Concretely the
five coefficient equations of `C • E = E` reduce (after multiplying by powers of `b`) to exactly
the relations `hQ1, hQ0, h3, hP2, hP1, hP0` listed below. -/
theorem ExistsVariableChange (L : Type*) [Field L] (E : WeierstrassCurve L)
    (a b c d e : L) (hb : b ≠ 0) (he : e ≠ 0) (h3 : e ^ 2 = b ^ 3)
    (hQ1 : e * (2 * d + E.a₁ * (b - e)) = 0)
    (hQ0 : e * (2 * c + E.a₁ * a + E.a₃ * (1 - e)) = 0)
    (hP2 : d ^ 2 + E.a₂ * e ^ 2 + E.a₁ * b * d - 3 * a * b ^ 2 - E.a₂ * b ^ 2 = 0)
    (hP1 : 2 * c * d + E.a₄ * e ^ 2 + (E.a₁ * a + E.a₃) * d + E.a₁ * b * c - 3 * a ^ 2 * b -
      2 * E.a₂ * a * b - E.a₄ * b = 0)
    (hP0 : c ^ 2 + E.a₆ * e ^ 2 + (E.a₁ * a + E.a₃) * c - a ^ 3 - E.a₂ * a ^ 2 - E.a₄ * a - E.a₆ = 0) :
    ∃ C : WeierstrassCurve.VariableChange L,
      C • E = E ∧ C.r = a ∧ (C.u : L) = e / b ∧ C.s = d / b ∧ C.t = c := by
  -- The inverse of the unit `e / b`: it is `b / e`.
  have hCinv : Units.val ((Units.mk0 (e / b) (div_ne_zero he hb))⁻¹) = b / e := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_div]
  refine ⟨⟨Units.mk0 (e / b) (div_ne_zero he hb), a, d / b, c⟩, ?_, rfl, ?_, rfl, rfl⟩
  · -- `C • E = E`: compare the five Weierstrass coefficients one by one.
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · -- `a₁`: `(b/e) * (a₁ + 2d/b) = a₁`, i.e. `2d + a₁(b-e) = 0`.
      rw [WeierstrassCurve.variableChange_a₁, hCinv]
      have h : 2 * d + E.a₁ * (b - e) = 0 := (mul_eq_zero.mp hQ1).resolve_left he
      field_simp
      linear_combination (norm := first | refl_ring1 | ring1) h
    · -- `a₂`: `(b/e)^2 * (a₂ - (d/b)a₁ + 3a - (d/b)^2) = a₂`, i.e. `hP2` (using `e^2 = b^3`).
      rw [WeierstrassCurve.variableChange_a₂, hCinv]
      field_simp
      linear_combination (norm := first | refl_ring1 | ring1) -hP2
    · -- `a₃`: `(b/e)^3 * (a₃ + a·a₁ + 2c) = a₃`, i.e. `2c + a₁a + a₃(1-e) = 0` (using `e^3 = e·b^3`).
      rw [WeierstrassCurve.variableChange_a₃, hCinv]
      have h : 2 * c + E.a₁ * a + E.a₃ * (1 - e) = 0 := (mul_eq_zero.mp hQ0).resolve_left he
      field_simp
      linear_combination (norm := first | refl_ring1 | ring1) b ^ 3 * h - E.a₃ * e * h3
    · -- `a₄`: `(b/e)^4 * (a₄ - (d/b)a₃ + 2a·a₂ - (c + a·d/b)a₁ + 3a^2 - 2(d/b)c) = a₄`, i.e. `hP1`.
      rw [WeierstrassCurve.variableChange_a₄, hCinv]
      field_simp
      linear_combination (norm := first | refl_ring1 | ring1) -b ^ 3 * hP1 - E.a₄ * e ^ 2 * h3
    · -- `a₆`: `(b/e)^6 * (a₆ + a·a₄ + a^2a₂ + a^3 - c·a₃ - c^2 - a·c·a₁) = a₆`, i.e. `hP0`.
      rw [WeierstrassCurve.variableChange_a₆, hCinv]
      field_simp
      linear_combination (norm := first | refl_ring1 | ring1) -b ^ 6 * hP0 - E.a₆ * (b ^ 3 * e ^ 2 + e ^ 4) * h3
  · exact Units.val_mk0 (div_ne_zero he hb)

end Work.MotC2
