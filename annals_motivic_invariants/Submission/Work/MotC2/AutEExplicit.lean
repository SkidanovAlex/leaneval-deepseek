import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.AutE_u_sq_eq_one
import Submission.Work.MotC2.AutEExplicit_char_two
import Submission.Work.MotC2.AutEExplicit_char_three

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotC2

/-- **Silverman, *AEC*, Prop. A.1.2, explicit form in characteristics `≠ 2, 3`**: if a change of
variables `C` fixes a Weierstrass model `W` over a field with `2, 3` invertible and `C.u ^ 2 = 1`,
then `C` is either the identity or the negation `(u, r, s, t) = (-1, 0, -a₁, -a₃)`.

Route (write `u = C.u`, `r = C.r`, `s = C.s`, `t = C.t`, `↑u` for the coercion to `L`).
* `hu : u ^ 2 = 1` gives `(↑u - 1) * (↑u + 1) = 0`, hence `↑u = 1` or `↑u = -1`.
* `variableChange_a₁ : ↑u⁻¹ * (W.a₁ + 2 * s) = W.a₁` gives `2 * s = (↑u - 1) * W.a₁`, so `s = 0`
  if `↑u = 1` and `s = -W.a₁` if `↑u = -1` (here `2 ≠ 0`).
* `variableChange_a₂` with `↑u⁻¹ ^ 2 = 1` gives `3 * r = s * (W.a₁ + s)`, which is `0` in both
  cases (`s = 0`, resp. `s = -W.a₁`), so `r = 0` (here `3 ≠ 0`).
* `variableChange_a₃` with `r = 0` gives `2 * t = (↑u - 1) * W.a₃`, so `t = 0` if `↑u = 1` and
  `t = -W.a₃` if `↑u = -1` (here `2 ≠ 0`). -/
theorem AutEExplicit_char_ne_two_three {L : Type*} [Field L] (h2 : (2 : L) ≠ 0)
    (h3 : (3 : L) ≠ 0) (W : WeierstrassCurve L) (C : WeierstrassCurve.VariableChange L)
    (hu : C.u ^ 2 = 1) (hC : C • W = W) :
    C = 1 ∨ (C.u = -1 ∧ C.r = 0 ∧ C.s = -W.a₁ ∧ C.t = -W.a₃) := by
  have hu' : (↑C.u : L) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  -- The three coefficient equations coming from `C • W = W`.
  have ha1 : (↑C.u⁻¹ : L) * (W.a₁ + 2 * C.s) = W.a₁ := by
    rw [← WeierstrassCurve.variableChange_a₁ W C, hC]
  have ha2 : (↑C.u⁻¹ : L) ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) = W.a₂ := by
    rw [← WeierstrassCurve.variableChange_a₂ W C, hC]
  have ha3 : (↑C.u⁻¹ : L) ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) = W.a₃ := by
    rw [← WeierstrassCurve.variableChange_a₃ W C, hC]
  have hfac : ((↑C.u : L) - 1) * ((↑C.u : L) + 1) = 0 := by linear_combination hu'
  rcases mul_eq_zero.mp hfac with h | h
  · -- case `↑u = 1`
    have h1u : (↑C.u : L) = 1 := sub_eq_zero.mp h
    have huinv : (↑C.u⁻¹ : L) = 1 := by rw [Units.val_inv_eq_inv_val, h1u, inv_one]
    have ha1u : W.a₁ + 2 * C.s = W.a₁ := by
      have hh := ha1
      rw [huinv, one_mul] at hh
      exact hh
    have hs : C.s = 0 := by
      have h2' : 2 * C.s = 0 := by linear_combination ha1u
      exact (mul_eq_zero.mp h2').resolve_left h2
    have ha2u : W.a₂ + 3 * C.r = W.a₂ := by
      have hh := ha2
      rw [huinv] at hh
      simp only [one_pow, one_mul] at hh
      rw [hs] at hh
      simpa using hh
    have hr : C.r = 0 := by
      have h2' : 3 * C.r = 0 := by linear_combination ha2u
      exact (mul_eq_zero.mp h2').resolve_left h3
    have ha3u : W.a₃ + 2 * C.t = W.a₃ := by
      have hh := ha3
      rw [huinv] at hh
      simp only [one_pow, one_mul] at hh
      rw [hr, zero_mul, add_zero] at hh
      simpa using hh
    have ht : C.t = 0 := by
      have h2' : 2 * C.t = 0 := by linear_combination ha3u
      exact (mul_eq_zero.mp h2').resolve_left h2
    exact Or.inl (WeierstrassCurve.VariableChange.ext (Units.ext h1u) hr hs ht)
  · -- case `↑u = -1`
    have h1u : (↑C.u : L) = -1 := add_eq_zero_iff_eq_neg.mp h
    have huinv : (↑C.u⁻¹ : L) = -1 := by rw [Units.val_inv_eq_inv_val, h1u, inv_neg, inv_one]
    have hsq : (↑C.u⁻¹ : L) ^ 2 = 1 := by rw [huinv]; ring
    have hcube : (↑C.u⁻¹ : L) ^ 3 = -1 := by rw [huinv]; ring
    have ha1u : -(W.a₁ + 2 * C.s) = W.a₁ := by
      have hh := ha1
      rw [huinv, neg_one_mul] at hh
      exact hh
    have hs : C.s = -W.a₁ := by
      have h2' : 2 * C.s = -(2 * W.a₁) := by linear_combination -ha1u
      have h3' : 2 * (C.s + W.a₁) = 0 := by linear_combination h2'
      exact add_eq_zero_iff_eq_neg.mp ((mul_eq_zero.mp h3').resolve_left h2)
    have ha2u : W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 = W.a₂ := by
      have hh := ha2
      rw [hsq, one_mul] at hh
      exact hh
    have hr : C.r = 0 := by
      rw [hs] at ha2u
      have h2' : 3 * C.r = 0 := by linear_combination ha2u
      exact (mul_eq_zero.mp h2').resolve_left h3
    have ha3u : -(W.a₃ + C.r * W.a₁ + 2 * C.t) = W.a₃ := by
      have hh := ha3
      rw [hcube, neg_one_mul] at hh
      exact hh
    have ht : C.t = -W.a₃ := by
      rw [hr, zero_mul, add_zero] at ha3u
      have h2' : 2 * C.t = -(2 * W.a₃) := by linear_combination -ha3u
      have h3' : 2 * (C.t + W.a₃) = 0 := by linear_combination h2'
      exact add_eq_zero_iff_eq_neg.mp ((mul_eq_zero.mp h3').resolve_left h2)
    exact Or.inr ⟨Units.ext h1u, hr, hs, ht⟩

/-- Strengthening of `Work.MotC2.AutE`: for `j ≠ 0, 1728` the only admissible changes of variables
stabilising `E` are the identity and the negation `C = (-1, 0, -a₁, -a₃)`, i.e. `C.u = -1`,
`C.r = 0`, `C.s = -a₁`, `C.t = -a₃`.  (This is the explicit form of `Aut(E, O) = {±1}`; note that
in characteristic `2`, `-1 = 1`, `-a₁ = a₁`, `-a₃ = a₃`.)

Route: `AutE_u_sq_eq_one` gives `C.u ^ 2 = 1`.  In characteristic `≠ 2`, `(↑C.u - 1)(↑C.u + 1) = 0`
so `C.u = ±1`; the `a₁`, `a₂` and `a₃` coefficient equations of `C • E = E` then give
`s = 0, r = 0, t = 0` (if `C.u = 1`, whence `C = 1`), resp. `s = -a₁, r = 0, t = -a₃` (if
`C.u = -1`); in characteristic `3` the `a₄` equation replaces the use of `3 r = 0`
(`r·b₂ = 0`, and `b₂ ≠ 0` since `j ≠ 0`).  In characteristic `2`, the `a₁`-equation gives
`C.u = 1` (using `a₁ ≠ 0`, which follows from `j ≠ 0`), the `a₃`-equation gives `C.r = 0`, the
`a₂`-equation gives `s(s + a₁) = 0`, and the `a₄`-equation gives `t a₁ = s a₃`; hence either
`s = t = 0` (and `C = 1`) or `s = a₁`, `t = a₃`, which is the asserted form since `2 = 0`. -/
theorem AutEExplicit (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (hj0 : E.j ≠ 0) (hj : E.j ≠ 1728) (C : WeierstrassCurve.VariableChange L) (hC : C • E = E) :
    C = 1 ∨ (C.u = -1 ∧ C.r = 0 ∧ C.s = -E.a₁ ∧ C.t = -E.a₃) := by
  -- Split according to the characteristic of the base field.  `AutE_u_sq_eq_one` supplies
  -- `C.u ^ 2 = 1` in the two branches where the field has characteristic `≠ 2`.
  by_cases h2 : (2 : L) = 0
  · -- characteristic `2`
    haveI : CharP L 2 := (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h2
    exact AutEExplicit_char_two E
      (fun ha₁ => hj0 (WeierstrassCurve.j_eq_zero_of_char_two (W := E) ha₁)) C hC
  · by_cases h3 : (3 : L) = 0
    · -- characteristic `3`
      haveI : CharP L 3 := (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h3
      exact AutEExplicit_char_three E
        (fun hb₂ => hj0 (WeierstrassCurve.j_eq_zero_of_char_three (W := E) hb₂)) C
        (AutE_u_sq_eq_one E hj0 hj C hC) hC
    · -- characteristic neither `2` nor `3`
      exact AutEExplicit_char_ne_two_three h2 h3 E C (AutE_u_sq_eq_one E hj0 hj C hC) hC

end Work.MotC2
