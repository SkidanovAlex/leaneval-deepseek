import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- **Silverman, *AEC*, Prop. A.1.2 in characteristics `≠ 2, 3`**: every change of variables
`C` fixing a Weierstrass model `W`, with `C.u ^ 2 = 1` and `2, 3` invertible in the field,
satisfies `C * C = 1`.

Route (write `u = C.u`, `r = C.r`, `s = C.s`, `t = C.t`, `↑u` for the coercion to `L`).
* `hu : u ^ 2 = 1` gives `(↑u - 1) * (↑u + 1) = 0`, hence `↑u = 1` or `↑u = -1`.
* `variableChange_a₁ : ↑u⁻¹ * (W.a₁ + 2 * s) = W.a₁` gives `2 * s = (↑u - 1) * W.a₁`
  (multiply by `↑u`), so `s = 0` if `↑u = 1` and `s = -W.a₁` if `↑u = -1` (here `2 ≠ 0`).
* `variableChange_a₂` with `↑u⁻¹ ^ 2 = 1` gives `3 * r = s * (W.a₁ + s)`, which is `0` in both
  cases (`s = 0`, resp. `s = -W.a₁`), so `r = 0` (here `3 ≠ 0`).
* `variableChange_a₃` with `r = 0` gives `↑u⁻¹ ^ 3 * (W.a₃ + 2 * t) = W.a₃`, so `t = 0` if
  `↑u = 1` and `t = -W.a₃` if `↑u = -1` (here `2 ≠ 0`).
* Finally `VariableChange.mul_def` gives
  `C * C = ⟨↑u * ↑u, r * ↑u ^ 2 + r, ↑u * s + s, t * ↑u ^ 3 + r * s * ↑u ^ 2 + t⟩
         = ⟨1, 0, s * (↑u + 1), t * (↑u ^ 3 + 1)⟩ = ⟨1, 0, 0, 0⟩ = 1`
  (`VariableChange.one_def`): `r = 0` kills the second and (with `s`) the fourth coordinate, and
  `s * (↑u + 1) = 0`, `t * (↑u ^ 3 + 1) = 0` because `↑u = 1` (with `s = t = 0`) or `↑u = -1`
  (with `↑u + 1 = 0`, `↑u ^ 3 + 1 = 0`).

No ellipticity of `W` is needed. -/
theorem AutE_char_ne_two_three {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0)
    (W : WeierstrassCurve L) (C : WeierstrassCurve.VariableChange L) (hu : C.u ^ 2 = 1)
    (hC : C • W = W) : C * C = 1 := by
  -- The `u`-coefficient, coerced to `L`, has square `1`.
  have hu' : (↑C.u : L) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  -- The three coefficient equations coming from `C • W = W`.
  have ha1 : (↑C.u⁻¹ : L) * (W.a₁ + 2 * C.s) = W.a₁ := by
    rw [← WeierstrassCurve.variableChange_a₁ W C, hC]
  have ha2 : (↑C.u⁻¹ : L) ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) = W.a₂ := by
    rw [← WeierstrassCurve.variableChange_a₂ W C, hC]
  have ha3 : (↑C.u⁻¹ : L) ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) = W.a₃ := by
    rw [← WeierstrassCurve.variableChange_a₃ W C, hC]
  -- `↑u = 1` or `↑u = -1`.
  have hfac : ((↑C.u : L) - 1) * ((↑C.u : L) + 1) = 0 := by linear_combination hu'
  rcases mul_eq_zero.mp hfac with h | h
  · have h1u : (↑C.u : L) = 1 := sub_eq_zero.mp h
    have huinv : (↑C.u⁻¹ : L) = 1 := by rw [Units.val_inv_eq_inv_val, h1u, inv_one]
    have hs : C.s = 0 := by
      have h' : W.a₁ + 2 * C.s = W.a₁ := by simpa [huinv] using ha1
      have h2' : 2 * C.s = 0 := by linear_combination h'
      exact (mul_eq_zero.mp h2').resolve_left h2
    have hr : C.r = 0 := by
      have h' : W.a₂ + 3 * C.r = W.a₂ := by simpa [huinv, hs] using ha2
      have h2' : 3 * C.r = 0 := by linear_combination h'
      exact (mul_eq_zero.mp h2').resolve_left h3
    have ht : C.t = 0 := by
      have h' : W.a₃ + 2 * C.t = W.a₃ := by simpa [huinv, hr] using ha3
      have h2' : 2 * C.t = 0 := by linear_combination h'
      exact (mul_eq_zero.mp h2').resolve_left h2
    ext
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def,
        Units.val_mul, Units.val_one]
      linear_combination (norm := first | refl_ring1 | ring1) hu'
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def]
      rw [hr]; ring
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def]
      rw [h1u, hs]; ring
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def]
      rw [hr, ht, h1u]; ring
  · have h1u : (↑C.u : L) = -1 := add_eq_zero_iff_eq_neg.mp h
    have huinv : (↑C.u⁻¹ : L) = -1 := by rw [Units.val_inv_eq_inv_val, h1u, inv_neg, inv_one]
    have hsq2 : (↑C.u⁻¹ : L) ^ 2 = 1 := by rw [huinv]; norm_num
    have hcube : (↑C.u⁻¹ : L) ^ 3 = -1 := by rw [huinv]; norm_num
    have hs : C.s = -W.a₁ := by
      have h' : -(W.a₁ + 2 * C.s) = W.a₁ := by simpa [huinv] using ha1
      have h2' : 2 * C.s = -(2 * W.a₁) := by linear_combination -h'
      have h3' : 2 * (C.s + W.a₁) = 0 := by linear_combination h2'
      exact add_eq_zero_iff_eq_neg.mp ((mul_eq_zero.mp h3').resolve_left h2)
    have hr : C.r = 0 := by
      have h' : W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 = W.a₂ := by
        have h2'' := ha2
        rw [hsq2, one_mul] at h2''
        exact h2''
      rw [hs] at h'
      have h2' : 3 * C.r = 0 := by linear_combination h'
      exact (mul_eq_zero.mp h2').resolve_left h3
    have ht : C.t = -W.a₃ := by
      have h' : -(W.a₃ + 2 * C.t) = W.a₃ := by
        have h3'' := ha3
        rw [hcube, hr] at h3''
        simpa using h3''
      have h2' : 2 * C.t = -(2 * W.a₃) := by linear_combination -h'
      have h3' : 2 * (C.t + W.a₃) = 0 := by linear_combination h2'
      exact add_eq_zero_iff_eq_neg.mp ((mul_eq_zero.mp h3').resolve_left h2)
    ext
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def,
        Units.val_mul, Units.val_one]
      linear_combination (norm := first | refl_ring1 | ring1) hu'
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def]
      rw [hr]; ring
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def]
      rw [h1u, hs]; ring
    · simp only [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def]
      rw [hr, ht, h1u]; ring

end Work.MotC2
