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

/-- Explicit form of `Aut(E,O) = {±1}` in characteristic two: a change of variables `C` fixing a
Weierstrass model `W` over a field of characteristic two, with `W.a₁ ≠ 0`, is either the identity,
or `C.u = -1`, `C.r = 0`, `C.s = -W.a₁`, `C.t = -W.a₃` (in characteristic two these say
`C.u = 1 = -1`, `C.s = W.a₁ = -W.a₁`, `C.t = W.a₃ = -W.a₃`).

Route (characteristic two: `2 = 0`, `3 = 1`, and `-x = x` for every `x`, `CharTwo.neg_eq`):
* `WeierstrassCurve.variableChange_a₁ : (C • W).a₁ = ↑C.u⁻¹ * (W.a₁ + 2 * C.s)` with `C • W = W`
  and `2 = 0` gives `↑C.u⁻¹ * W.a₁ = W.a₁`, hence `↑C.u⁻¹ = 1` by `ha₁`, i.e. `C.u = 1`.
* `WeierstrassCurve.variableChange_a₃` with `2 = 0`, `C.u = 1` gives `C.r * W.a₁ = 0`, hence
  `C.r = 0` by `ha₁`.
* `WeierstrassCurve.variableChange_a₂` with `↑C.u⁻¹ ^ 2 = 1`, `2 = 0`, `3 = 1`, `C.r = 0` gives
  `s * (s + W.a₁) = 0` where `s = C.s`.
* `WeierstrassCurve.variableChange_a₄ : (C • W).a₄ = ↑C.u⁻¹ ^ 4 *
    (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t)`
  with `↑C.u⁻¹ ^ 4 = 1`, `2 = 0`, `C.r = 0` gives `C.t * W.a₁ = C.s * W.a₃`
  (i.e. `C.t * W.a₁ = -C.s * W.a₃` and `-x = x`).
* If `s = 0` then `C.t * W.a₁ = 0`, so `C.t = 0`, and `C = (1, 0, 0, 0) = 1`
  (`VariableChange.ext`, `VariableChange.one_def`).
* If `s + W.a₁ = 0`, then `C.s = W.a₁ = -W.a₁`, and `C.t * W.a₁ = W.a₁ * W.a₃` gives
  `C.t = W.a₃ = -W.a₃`; with `C.u = 1 = -1` and `C.r = 0` the second disjunct holds. -/
theorem AutEExplicit_char_two {L : Type*} [Field L] [CharP L 2] (W : WeierstrassCurve L)
    (ha₁ : W.a₁ ≠ 0) (C : WeierstrassCurve.VariableChange L) (hC : C • W = W) :
    C = 1 ∨ (C.u = -1 ∧ C.r = 0 ∧ C.s = -W.a₁ ∧ C.t = -W.a₃) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have h3 : (3 : L) = 1 := by
    have h31 : (3 : L) = (2 : L) + 1 := by norm_num
    rw [h31, h2, zero_add]
  -- The `a₁`-coefficient gives `↑C.u⁻¹ = 1`, hence `C.u = 1`.
  have ha₁' : (C • W).a₁ = W.a₁ := by rw [hC]
  rw [WeierstrassCurve.variableChange_a₁, h2, zero_mul, add_zero] at ha₁'
  have huval : (↑C.u⁻¹ : L) = 1 := mul_right_cancel₀ ha₁ (by rw [one_mul]; exact ha₁')
  have hu : C.u = 1 := inv_eq_one.mp (Units.ext huval)
  -- The `a₃`-coefficient gives `C.r = 0`.
  have ha₃' : (C • W).a₃ = W.a₃ := by rw [hC]
  rw [WeierstrassCurve.variableChange_a₃, h2, zero_mul, add_zero, huval] at ha₃'
  simp only [one_pow, one_mul] at ha₃'
  have hr : C.r = 0 := (mul_eq_zero.mp (by linear_combination ha₃')).resolve_right ha₁
  -- The `a₂`-coefficient gives `C.s * (C.s + W.a₁) = 0`.
  have hs : C.s * (C.s + W.a₁) = 0 := by
    have ha₂' : (C • W).a₂ = W.a₂ := by rw [hC]
    rw [WeierstrassCurve.variableChange_a₂, huval, hr, h3] at ha₂'
    simp only [one_pow, one_mul, mul_zero, add_zero] at ha₂'
    linear_combination (norm := first | refl_ring1 | ring1) -ha₂'
  -- The `a₄`-coefficient gives `C.t * W.a₁ = C.s * W.a₃`.
  have ht : C.t * W.a₁ = C.s * W.a₃ := by
    have ha₄' : (C • W).a₄ = W.a₄ := by rw [hC]
    rw [WeierstrassCurve.variableChange_a₄, huval, h2, hr, h3] at ha₄'
    ring_nf at ha₄'
    have h' : C.s * W.a₃ + C.t * W.a₁ = 0 := by linear_combination -ha₄'
    have h1 : C.t * W.a₁ = -(C.s * W.a₃) := by linear_combination h'
    rw [CharTwo.neg_eq] at h1
    exact h1
  rcases mul_eq_zero.mp hs with hs0 | hs1
  · -- Case `C.s = 0`: then `C.t = 0` and `C = (1, 0, 0, 0) = 1`.
    left
    have ht0 : C.t = 0 := by
      have h : C.t * W.a₁ = 0 := by rw [ht, hs0, zero_mul]
      exact (mul_eq_zero.mp h).resolve_right ha₁
    rw [WeierstrassCurve.VariableChange.one_def]
    apply WeierstrassCurve.VariableChange.ext
    · exact hu
    · exact hr
    · exact hs0
    · exact ht0
  · -- Case `C.s + W.a₁ = 0`: the second disjunct holds.
    right
    have hsneg : C.s = -W.a₁ := by linear_combination hs1
    have htneg : C.t = -W.a₃ := by
      have h : C.t * W.a₁ = (-W.a₃) * W.a₁ := by rw [ht, hsneg]; ring
      exact mul_right_cancel₀ ha₁ h
    refine ⟨?_, hr, hsneg, htneg⟩
    rw [hu]
    ext
    simp [CharTwo.neg_eq]

end Work.MotC2
