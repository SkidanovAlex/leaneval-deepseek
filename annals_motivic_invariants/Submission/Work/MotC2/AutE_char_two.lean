import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- **Silverman, *AEC*, Prop. A.1.2 in characteristic two**: every change of variables `C`
fixing a Weierstrass model `W` with `a₁ ≠ 0` satisfies `C * C = 1`.

Route (characteristic `2`, so `2 = 0`, `CharTwo.add_self_eq_zero`):
* `WeierstrassCurve.variableChange_a₁ : (C • W).a₁ = ↑C.u⁻¹ * (W.a₁ + 2 * C.s)`, so
  `C • W = W` gives `↑C.u⁻¹ * W.a₁ = W.a₁`, so `↑C.u⁻¹ = 1` by `ha₁`, i.e. `C.u = 1`
  (`Units.ext`, `inv_eq_one`).
* `WeierstrassCurve.variableChange_a₃ : (C • W).a₃ = ↑C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)`,
  so `C • W = W` plus `C.u = 1` gives `C.r * W.a₁ = 0`, hence `C.r = 0` by `ha₁`.
* `WeierstrassCurve.VariableChange.mul_def` with `C.u = 1` and `C.r = 0`:
  `C * C = ⟨1 * 1, C.r * 1 ^ 2 + C.r, 1 * C.s + C.s, C.t * 1 ^ 3 + C.r * C.s * 1 ^ 2 + C.t⟩
         = ⟨1, 2 * C.r, 2 * C.s, 2 * C.t⟩ = ⟨1, 0, 0, 0⟩ = 1`
  (`VariableChange.one_def`), using `2 = 0` in characteristic two. -/
theorem AutE_char_two {L : Type*} [Field L] [CharP L 2] (W : WeierstrassCurve L)
    (ha₁ : W.a₁ ≠ 0) (C : WeierstrassCurve.VariableChange L) (hC : C • W = W) : C * C = 1 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  -- The `a₁`-coefficient gives `↑C.u⁻¹ = 1`.
  have ha₁' : (C • W).a₁ = W.a₁ := by rw [hC]
  rw [WeierstrassCurve.variableChange_a₁, h2, zero_mul, add_zero] at ha₁'
  have huval : (↑C.u⁻¹ : L) = 1 :=
    mul_right_cancel₀ ha₁ (by rw [one_mul]; exact ha₁')
  have hu : C.u = 1 := inv_eq_one.mp (Units.ext huval)
  -- The `a₃`-coefficient, with `↑C.u⁻¹ = 1` and `2 = 0`, gives `C.r * W.a₁ = 0`.
  have ha₃' : (C • W).a₃ = W.a₃ := by rw [hC]
  rw [WeierstrassCurve.variableChange_a₃, h2, zero_mul, add_zero, huval] at ha₃'
  simp only [one_pow, one_mul] at ha₃'
  have hr : C.r = 0 := (mul_eq_zero.mp (by linear_combination ha₃')).resolve_right ha₁
  have hss : C.s + C.s = 0 := by rw [← two_mul, h2, zero_mul]
  have htt : C.t + C.t = 0 := by rw [← two_mul, h2, zero_mul]
  -- Finally compute `C * C` coordinatewise.
  rw [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def]
  ext
  · simp [hu]
  · simp [hr]
  · simpa [hu] using hss
  · simpa [hu, hr] using htt

end Work.MotC2
