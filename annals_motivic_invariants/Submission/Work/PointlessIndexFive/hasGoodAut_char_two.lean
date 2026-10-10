import Mathlib
import Submission.Work.PointlessIndexFive.GoodAut

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HasGoodAut` in characteristic two

Silverman, *AEC*, Proposition A.1.2 for the characteristic-`2` family `a₁ ≠ 0`:
every automorphism of such a Weierstrass model has order dividing `2`.

The argument is shorter than in the other characteristics because characteristic `2` kills all the
correction terms in the group law of `VariableChange 𝕜`.  Let `C = (u, r, s, t)` be an admissible
change of variables fixing `W`.

* `a₁`: `(C • W).a₁ = C.u⁻¹ * (W.a₁ + 2 * C.s) = C.u⁻¹ * W.a₁` equals `W.a₁ ≠ 0`, so
  `C.u⁻¹ = 1`, i.e. `C.u = 1`.
* `a₃`: `(C • W).a₃ = C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) = W.a₃ + C.r * W.a₁` equals
  `W.a₃`, so `C.r * W.a₁ = 0`, i.e. `C.r = 0`.
* With `C.u = 1` and `C.r = 0`, the group law
  `C * C' = ⟨C.u * C'.u, C.r * C'.u ^ 2 + C'.r, C'.u * C.s + C'.s, ⋯⟩` gives
  `C * C = ⟨1, 0, 2 * C.s, 2 * C.t⟩ = 1` in characteristic `2`.

No ellipticity of `W` is needed, and the `a₂`, `a₄`, `a₆` coefficients are not used at all.
-/

namespace Work.PointlessIndexFive

open WeierstrassCurve

theorem hasGoodAut_char_two {𝕜 : Type} [Field 𝕜] [CharP 𝕜 2]
    (W : WeierstrassCurve 𝕜) (ha₁ : W.a₁ ≠ 0) : Work.PointlessIndexFive.HasGoodAut W := by
  intro σ
  refine Or.inl ?_
  let C : WeierstrassCurve.VariableChange 𝕜 := ↑σ
  have hC : C • W = W := σ.2
  -- the `u`-coefficient of `σ` is trivial
  have hu : C.u = 1 := by
    have h := congrArg WeierstrassCurve.a₁ hC
    rw [WeierstrassCurve.variableChange_a₁] at h
    simp only [CharTwo.two_eq_zero, zero_mul, add_zero] at h
    have h1 : (↑C.u⁻¹ : 𝕜) = 1 := mul_right_cancel₀ ha₁ (by simpa using h)
    exact inv_eq_one.mp (Units.ext h1)
  -- the `r`-coefficient of `σ` is trivial
  have hr : C.r = 0 := by
    have h := congrArg WeierstrassCurve.a₃ hC
    rw [WeierstrassCurve.variableChange_a₃] at h
    simp only [hu, inv_one, one_pow, Units.val_one, one_mul, CharTwo.two_eq_zero, zero_mul,
      add_zero] at h
    exact (mul_eq_zero.mp (add_eq_left.mp h)).resolve_right ha₁
  -- hence `σ ^ 2 = 1`: the group law of `VariableChange` has only `2 * C.s` and `2 * C.t` left,
  -- and characteristic `2` kills both
  have hsq : C * C = 1 := by
    rw [WeierstrassCurve.VariableChange.mul_def, WeierstrassCurve.VariableChange.one_def]
    refine WeierstrassCurve.VariableChange.ext ?_ ?_ ?_ ?_
    · rw [hu]; simp
    · rw [hr]; simp
    · show (↑C.u : 𝕜) * C.s + C.s = 0
      rw [hu]
      simp only [Units.val_one, one_mul]
      exact CharTwo.add_self_eq_zero C.s
    · show C.t * (↑C.u : 𝕜) ^ 3 + C.r * C.s * (↑C.u : 𝕜) ^ 2 + C.t = 0
      rw [hu, hr]
      simp only [Units.val_one, one_pow, mul_one, zero_mul, add_zero]
      exact CharTwo.add_self_eq_zero C.t
  rw [orderOf_dvd_iff_pow_eq_one]
  exact Subtype.ext (by rw [pow_two]; exact hsq)

end Work.PointlessIndexFive
