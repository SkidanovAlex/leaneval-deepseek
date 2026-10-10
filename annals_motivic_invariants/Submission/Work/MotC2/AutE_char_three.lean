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

/-- **Silverman, *AEC*, Prop. A.1.2 in characteristic three**: every change of variables `C`
fixing a Weierstrass model `W` with `b₂ ≠ 0` and `C.u ^ 2 = 1` satisfies `C * C = 1`.

Route (characteristic `3`: `2 = -1 ≠ 0`, `3 = 0`; write `u = C.u`, `r = C.r`, `s = C.s`,
`t = C.t`, with `↑u` the coercion to `L`).
* `hu : u ^ 2 = 1` in `Lˣ` gives `(↑u - 1) * (↑u + 1) = 0` in the field, hence `↑u = 1` or
  `↑u = -1`.
* `variableChange_a₁`: `↑u⁻¹ * (W.a₁ + 2 * s) = W.a₁`, i.e. `2 * s = (↑u - 1) * W.a₁`,
  i.e. `s = (1 - ↑u) * W.a₁` (since `2⁻¹ = 2 = -1` in characteristic `3`).  So `↑u = 1 → s = 0`
  and `↑u = -1 → s = -W.a₁`.
* `variableChange_a₂` with `u ^ 2 = 1` gives `s * (W.a₁ + s) = 0` (as `3 * r = 0`).
* Case `↑u = 1`: `s = 0`.  `variableChange_a₃` gives `r * W.a₁ + 2 * t = 0`, and
  `variableChange_a₄` gives `2 * r * W.a₂ - t * W.a₁ = 0`; eliminating `t` (`2 * t = -r * W.a₁`,
  so `t = r * W.a₁` as `2⁻¹ = 2`) gives `r * (2 * W.a₂ - W.a₁ ^ 2) = 0`, i.e. `-r * W.b₂ = 0`
  (using `W.b₂ = W.a₁ ^ 2 + 4 * W.a₂ = W.a₁ ^ 2 + W.a₂` in characteristic `3`), hence `r = 0` by
  `hb₂`, and then `t = 0`; so `C = (1, 0, 0, 0) = 1`.
* Case `↑u = -1`: `s = -W.a₁`.  `variableChange_a₃` gives `r * W.a₁ + 2 * t = W.a₃` and
  `variableChange_a₄` becomes `W.a₁ * W.a₃ + 2 * r * W.a₂ + r * W.a₁ ^ 2 + W.a₁ * t = 0`;
  substituting the first into the second kills the `W.a₃` and `t` terms and leaves
  `2 * r * W.b₂ = 0`, hence `r = 0` by `hb₂`.
* In either case `r = 0` and `↑u = ±1`, so `VariableChange.mul_def` gives
  `C * C = ⟨↑u * ↑u, r * ↑u ^ 2 + r, ↑u * s + s, t * ↑u ^ 3 + r * s * ↑u ^ 2 + t⟩
         = ⟨1, 0, s * (↑u + 1), t * (↑u ^ 3 + 1)⟩ = ⟨1, 0, 0, 0⟩ = 1`
  (`VariableChange.one_def`); in the case `↑u = 1` we moreover have `s = t = 0`. -/
theorem AutE_char_three {L : Type*} [Field L] [CharP L 3] (W : WeierstrassCurve L)
    (hb₂ : W.b₂ ≠ 0) (C : WeierstrassCurve.VariableChange L) (hu : C.u ^ 2 = 1)
    (hC : C • W = W) : C * C = 1 := by
  -- Basic facts about `u = C.u`
  have huu : C.u * C.u = (1 : Lˣ) := by rw [← pow_two, hu]
  have huvm : (↑C.u : L) * (↑C.u : L) = 1 := by rw [← Units.val_mul, huu, Units.val_one]
  have hune : (↑C.u : L) ≠ 0 := C.u.ne_zero
  have h3 : (3 : L) = 0 := CharP.cast_eq_zero L 3
  have hu3 : (↑C.u : L) ^ 3 = ↑C.u := by linear_combination (↑C.u) * huvm
  have hu4 : (↑C.u : L) ^ 4 = 1 := by
    linear_combination (norm := first | refl_ring1 | ring1) ((↑C.u : L) ^ 2 + 1) * huvm
  have huinv4 : ((↑C.u : L))⁻¹ ^ 4 = 1 := by rw [inv_pow, hu4, inv_one]
  -- `r = 0` from the transformation law of `b₄` (`6 = 0` in characteristic three)
  have hb4 := congrArg WeierstrassCurve.b₄ hC
  rw [WeierstrassCurve.variableChange_b₄, Units.val_inv_eq_inv_val] at hb4
  have hrb : C.r * W.b₂ = 0 := by
    rw [huinv4, one_mul] at hb4
    linear_combination (norm := first | refl_ring1 | ring1) hb4 - (2 * C.r ^ 2) * h3
  have hr : C.r = 0 := (mul_eq_zero.mp hrb).resolve_right hb₂
  -- the `a₁` law: `u * (a₁ + 2 s) = a₁`, i.e. `2 * s = (u - 1) * a₁`
  have h1raw := congrArg WeierstrassCurve.a₁ hC
  rw [WeierstrassCurve.variableChange_a₁, Units.val_inv_eq_inv_val,
    inv_eq_of_mul_eq_one_right huvm] at h1raw
  have h1m : W.a₁ + 2 * C.s = (↑C.u : L) * W.a₁ := by
    have h := congrArg (fun x => (↑C.u : L) * x) h1raw
    rw [← mul_assoc, huvm, one_mul] at h
    exact h
  have e1 : (2 : L) * C.s = ((↑C.u : L) - 1) * W.a₁ := by linear_combination h1m
  -- the `a₃` law: `u * (a₃ + r a₁ + 2 t) = a₃` (using `u ^ 3 = u`)
  have h3raw := congrArg WeierstrassCurve.a₃ hC
  rw [WeierstrassCurve.variableChange_a₃, Units.val_inv_eq_inv_val] at h3raw
  have h3m : W.a₃ + C.r * W.a₁ + 2 * C.t = (↑C.u : L) * W.a₃ := by
    have h := congrArg (fun x => (↑C.u : L) ^ 3 * x) h3raw
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hune, one_pow, one_mul, hu3] at h
    exact h
  -- `u ^ 2 = 1` forces `u = 1` or `u = -1`
  have hcases : (↑C.u : L) = 1 ∨ (↑C.u : L) = -1 := by
    have h2 : (↑C.u : L) ^ 2 = 1 := by rw [pow_two]; exact huvm
    have hfac : ((↑C.u : L) - 1) * ((↑C.u : L) + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp hfac with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hcases with hu1 | hum
  · -- case `u = 1`: `2 s = 0` and `2 t = 0`
    have hs1 : (2 : L) * C.s = 0 := by rw [hu1] at e1; linear_combination e1
    have ht1 : (2 : L) * C.t = 0 := by rw [hu1, hr] at h3m; linear_combination h3m
    rw [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def]
    refine WeierstrassCurve.VariableChange.ext ?_ ?_ ?_ ?_
    · exact huu
    · rw [hr]; ring
    · rw [hu1]; linear_combination hs1
    · rw [hr, hu1]; linear_combination ht1
  · -- case `u = -1`: the remaining terms vanish since `u + 1 = 0` and `u ^ 3 + 1 = 0`
    rw [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def]
    refine WeierstrassCurve.VariableChange.ext ?_ ?_ ?_ ?_
    · exact huu
    · rw [hr]; ring
    · rw [hum]; ring
    · rw [hr, hum]; ring

end Work.MotC2
