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

/-- Explicit form of `Aut(E,O) = {±1}` in characteristic three: a change of variables `C` fixing a
Weierstrass model `W` over a field of characteristic three, with `W.b₂ ≠ 0` and `C.u ^ 2 = 1`, is
either the identity, or `C.u = -1`, `C.r = 0`, `C.s = -W.a₁`, `C.t = -W.a₃`.

Route (characteristic three: `3 = 0`, `2 ≠ 0`; write `u = C.u`, `r = C.r`, `s = C.s`, `t = C.t`,
`↑u` for the coercion to `L`):
* `C.u ^ 2 = 1` gives `(↑C.u - 1) * (↑C.u + 1) = 0`, hence `↑C.u = 1` or `↑C.u = -1`.
* `WeierstrassCurve.variableChange_b₄ : (C • W).b₄ = ↑C.u⁻¹ ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2)`
  with `C • W = W`, `↑C.u ^ 4 = 1` (from `C.u ^ 2 = 1`) and `6 = 0` gives `C.r * W.b₂ = 0`, hence
  `C.r = 0` by `hb₂`.  (This replaces the use of `3 * C.r = 0`, which is vacuous here.)
* `variableChange_a₁ : ↑C.u⁻¹ * (W.a₁ + 2 * C.s) = W.a₁` gives `2 * C.s = (↑C.u - 1) * W.a₁`, so
  `C.s = 0` if `↑C.u = 1` and `C.s = -W.a₁` if `↑C.u = -1` (`2 ≠ 0`).
* `variableChange_a₃ : ↑C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) = W.a₃` with `C.r = 0` gives
  `2 * C.t = (↑C.u - 1) * W.a₃`, so `C.t = 0` if `↑C.u = 1` and `C.t = -W.a₃` if `↑C.u = -1`.
* In the case `↑C.u = 1` conclude `C = (1, 0, 0, 0) = 1` (`VariableChange.ext`,
  `VariableChange.one_def`, `Units.ext`); in the case `↑C.u = -1` the second disjunct holds
  (`C.u = -1` as units via `Units.ext`). -/
theorem AutEExplicit_char_three {L : Type*} [Field L] [CharP L 3] (W : WeierstrassCurve L)
    (hb₂ : W.b₂ ≠ 0) (C : WeierstrassCurve.VariableChange L) (hu : C.u ^ 2 = 1) (hC : C • W = W) :
    C = 1 ∨ (C.u = -1 ∧ C.r = 0 ∧ C.s = -W.a₁ ∧ C.t = -W.a₃) := by
  -- Characteristic three: `3 = 0` and `2 ≠ 0`.
  have h3 : (3 : L) = 0 := CharP.cast_eq_zero L 3
  have h2 : (2 : L) ≠ 0 := by
    intro h
    exact one_ne_zero (by linear_combination h3 - h)
  -- The unit `u = C.u` has square one.
  have huu : C.u * C.u = (1 : Lˣ) := by rw [← pow_two, hu]
  have huvm : (↑C.u : L) * (↑C.u : L) = 1 := by rw [← Units.val_mul, huu, Units.val_one]
  have hune : (↑C.u : L) ≠ 0 := C.u.ne_zero
  have hu3 : (↑C.u : L) ^ 3 = ↑C.u := by linear_combination (↑C.u) * huvm
  have hu4 : (↑C.u : L) ^ 4 = 1 := by
    linear_combination (norm := first | refl_ring1 | ring1) ((↑C.u : L) ^ 2 + 1) * huvm
  have huinv4 : ((↑C.u : L))⁻¹ ^ 4 = 1 := by rw [inv_pow, hu4, inv_one]
  -- `r = 0` from the transformation law of `b₄` (`6 = 0` in characteristic three).
  have hb4 := congrArg WeierstrassCurve.b₄ hC
  rw [WeierstrassCurve.variableChange_b₄, Units.val_inv_eq_inv_val] at hb4
  have hrb : C.r * W.b₂ = 0 := by
    rw [huinv4, one_mul] at hb4
    linear_combination (norm := first | refl_ring1 | ring1) hb4 - (2 * C.r ^ 2) * h3
  have hr : C.r = 0 := (mul_eq_zero.mp hrb).resolve_right hb₂
  -- The `a₁` law: `↑u * (a₁ + 2 s) = a₁`, i.e. `2 * s = (↑u - 1) * a₁`.
  have h1raw := congrArg WeierstrassCurve.a₁ hC
  rw [WeierstrassCurve.variableChange_a₁, Units.val_inv_eq_inv_val,
    inv_eq_of_mul_eq_one_right huvm] at h1raw
  have h1m : W.a₁ + 2 * C.s = (↑C.u : L) * W.a₁ := by
    have h := congrArg (fun x => (↑C.u : L) * x) h1raw
    rw [← mul_assoc, huvm, one_mul] at h
    exact h
  have e1 : (2 : L) * C.s = ((↑C.u : L) - 1) * W.a₁ := by linear_combination h1m
  -- The `a₃` law: `↑u ^ 3 * (a₃ + r a₁ + 2 t) = a₃`, i.e. (with `r = 0`) `2 * t = (↑u - 1) * a₃`.
  have h3raw := congrArg WeierstrassCurve.a₃ hC
  rw [WeierstrassCurve.variableChange_a₃, Units.val_inv_eq_inv_val] at h3raw
  have h3m : W.a₃ + C.r * W.a₁ + 2 * C.t = (↑C.u : L) * W.a₃ := by
    have h := congrArg (fun x => (↑C.u : L) ^ 3 * x) h3raw
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hune, one_pow, one_mul, hu3] at h
    exact h
  have e3 : (2 : L) * C.t = ((↑C.u : L) - 1) * W.a₃ := by
    rw [hr, zero_mul, add_zero] at h3m
    linear_combination (norm := first | refl_ring1 | ring1) h3m
  -- `↑u = 1` or `↑u = -1`.
  have hfac : ((↑C.u : L) - 1) * ((↑C.u : L) + 1) = 0 := by
    have h2' : (↑C.u : L) ^ 2 = 1 := by rw [pow_two]; exact huvm
    linear_combination (norm := first | refl_ring1 | ring1) h2'
  rcases mul_eq_zero.mp hfac with h | h
  · -- Case `↑u = 1`: `s = t = 0` and `C = 1`.
    have h1u : (↑C.u : L) = 1 := sub_eq_zero.mp h
    left
    have hus : C.u = 1 := Units.ext (by simpa using h1u)
    have hs : C.s = 0 := by
      have h2s : (2 : L) * C.s = 0 := by rw [h1u] at e1; linear_combination e1
      exact (mul_eq_zero.mp h2s).resolve_left h2
    have ht : C.t = 0 := by
      have h2t : (2 : L) * C.t = 0 := by rw [h1u] at e3; linear_combination e3
      exact (mul_eq_zero.mp h2t).resolve_left h2
    refine WeierstrassCurve.VariableChange.ext ?_ ?_ ?_ ?_
    · simpa only [WeierstrassCurve.VariableChange.one_def] using hus
    · simpa only [WeierstrassCurve.VariableChange.one_def] using hr
    · simpa only [WeierstrassCurve.VariableChange.one_def] using hs
    · simpa only [WeierstrassCurve.VariableChange.one_def] using ht
  · -- Case `↑u = -1`: `s = -a₁`, `t = -a₃`.
    have h1u : (↑C.u : L) = -1 := add_eq_zero_iff_eq_neg.mp h
    right
    have hu_neg : C.u = -1 := Units.ext (by rw [h1u, Units.val_neg, Units.val_one])
    have hs : C.s = -W.a₁ := by
      have h2s : (2 : L) * C.s = -(2 * W.a₁) := by rw [h1u] at e1; linear_combination e1
      have h' : 2 * (C.s + W.a₁) = 0 := by linear_combination h2s
      exact add_eq_zero_iff_eq_neg.mp ((mul_eq_zero.mp h').resolve_left h2)
    have ht : C.t = -W.a₃ := by
      have h2t : (2 : L) * C.t = -(2 * W.a₃) := by rw [h1u] at e3; linear_combination e3
      have h' : 2 * (C.t + W.a₃) = 0 := by linear_combination h2t
      exact add_eq_zero_iff_eq_neg.mp ((mul_eq_zero.mp h').resolve_left h2)
    exact ⟨hu_neg, hr, hs, ht⟩

end Work.MotC2
