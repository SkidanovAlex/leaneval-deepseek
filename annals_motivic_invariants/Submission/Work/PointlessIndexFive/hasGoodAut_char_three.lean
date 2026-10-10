/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessIndexFive
-/
import Mathlib
import Submission.Work.PointlessIndexFive.GoodAut

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Silverman, *AEC*, A.1.2 in characteristic `3`: the models with `a₁ = a₃ = 0`, `a₂ ≠ 0`

The Tate normal form of the paper's step (B) is used in characteristic `3` in the shape
`y² = x³ + a₂x² + a₄x + a₆` with `a₂ ≠ 0` (i.e. `a₁ = a₃ = 0`), for which the short model
`y² = x³ + a₄x + a₆` of `Work.Arithmetic.Aut_orderOf_dvd_of_short` is unavailable — the
change to short form requires `2, 3` invertible, which fails in characteristic `3`.  This file
supplies Silverman, *AEC*, Proposition A.1.2 for that shape, by the same coefficient comparison:
an admissible change of variables `C = (u, r, s, t)` fixing such a model is forced by the first
four coefficient equations to be `C = (u, 0, 0, 0)` with `u ^ 2 = 1`, whence `C ^ 2 = 1` and
every automorphism has order dividing `2`.

## Main result

* `Work.PointlessIndexFive.hasGoodAut_char_three`
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.PointlessIndexFive

/-- In a field of characteristic `3` we have `2 ≠ 0`. -/
private lemma two_ne_zero_of_charP_three {𝕜 : Type} [Field 𝕜] [CharP 𝕜 3] :
    (2 : 𝕜) ≠ 0 := by
  have h : ((2 : ℕ) : 𝕜) ≠ 0 := by
    intro hzero
    rw [CharP.cast_eq_zero_iff 𝕜 3] at hzero
    norm_num at hzero
  simpa using h

/-- **Silverman, *AEC*, Proposition A.1.2, in characteristic `3`.**  If `W` is a Weierstrass
model with `a₁ = a₃ = 0` and `a₂ ≠ 0`, then every automorphism of `W` has order dividing `2`
(in particular dividing `6`), so `W` has `HasGoodAut`.

Comparing coefficients in `C • W = W`, with `3 = 0` and using `variableChange_aᵢ`:
* `a₁`: `u⁻¹ * (2 * s) = 0`, so `s = 0`;
* `a₂`: `u⁻² * a₂ = a₂`, so `u ^ 2 = 1` (here `a₂ ≠ 0` is used);
* `a₃`: `u⁻³ * (2 * t) = 0`, so `t = 0`;
* `a₄`: `u⁻⁴ * (a₄ + 2 * r * a₂) = a₄`, and `u⁻⁴ = 1` by `u ^ 2 = 1`, so `2 * r * a₂ = 0`,
  whence `r = 0`.

Thus `C = (u, 0, 0, 0)` with `u ^ 2 = 1`, i.e. `C ^ 2 = 1` (`Work.Arithmetic.vc_pow_zero`). -/
theorem hasGoodAut_char_three {𝕜 : Type} [Field 𝕜] [CharP 𝕜 3]
    (W : WeierstrassCurve 𝕜) (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (ha₂ : W.a₂ ≠ 0) :
    Work.PointlessIndexFive.HasGoodAut W := by
  intro σ
  refine Or.inl ?_
  let C : WeierstrassCurve.VariableChange 𝕜 := ↑σ
  have hC : C • W = W := σ.2
  have h2 : (2 : 𝕜) ≠ 0 := two_ne_zero_of_charP_three
  have h3 : (3 : 𝕜) = 0 := CharP.cast_eq_zero 𝕜 3
  -- the `a₁`-coefficient of `C • W = W` forces `s = 0`
  have hs : C.s = 0 := by
    have h := congrArg WeierstrassCurve.a₁ hC
    rw [WeierstrassCurve.variableChange_a₁, h₁, zero_add] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (Units.ne_zero C.u⁻¹)
    · exact (mul_eq_zero.mp h').resolve_left h2
  -- the `a₂`-coefficient forces `u ^ 2 = 1`, using `a₂ ≠ 0`
  have hu2 : C.u ^ 2 = 1 := by
    have h := congrArg WeierstrassCurve.a₂ hC
    rw [WeierstrassCurve.variableChange_a₂] at h
    have h' : (↑(C.u⁻¹ ^ 2) : 𝕜) * W.a₂ = W.a₂ := by simpa [hs, h₁, h3] using h
    have hx : C.u⁻¹ ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_one]
      apply mul_right_cancel₀ ha₂
      simpa using h'
    rw [inv_pow] at hx
    exact inv_eq_one.mp hx
  -- the `a₃`-coefficient forces `t = 0`
  have ht : C.t = 0 := by
    have h := congrArg WeierstrassCurve.a₃ hC
    rw [WeierstrassCurve.variableChange_a₃] at h
    have h' : (↑(C.u⁻¹) : 𝕜) ^ 3 * (2 * C.t) = 0 := by simpa [h₃, h₁] using h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (pow_ne_zero 3 (Units.ne_zero C.u⁻¹))
    · exact (mul_eq_zero.mp h'').resolve_left h2
  -- the `a₄`-coefficient, with `u⁻⁴ = 1` from `u ^ 2 = 1`, forces `r = 0`
  have hr : C.r = 0 := by
    have h := congrArg WeierstrassCurve.a₄ hC
    rw [WeierstrassCurve.variableChange_a₄] at h
    have hu4 : (↑(C.u⁻¹) : 𝕜) ^ 4 = 1 := by
      have hv : (↑C.u : 𝕜) ^ 2 = 1 := by
        simpa using congrArg (fun x : 𝕜ˣ => (x : 𝕜)) hu2
      have hv4 : (↑C.u : 𝕜) ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hv, one_pow]
      rw [Units.val_inv_eq_inv_val, inv_pow, hv4, inv_one]
    have h1 := h
    rw [hu4, one_mul] at h1
    rw [hs, ht, h₁, h₃, h3] at h1
    ring_nf at h1
    have hzero : C.r * W.a₂ * 2 = 0 :=
      add_left_cancel (a := W.a₄) (by rw [h1, add_zero])
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact (mul_eq_zero.mp h').resolve_right ha₂
    · exact absurd h' h2
  -- hence `C = (u, 0, 0, 0)` with `u ^ 2 = 1`, so `C ^ 2 = 1` and `orderOf σ ∣ 2`
  have hCeq : C = ⟨C.u, 0, 0, 0⟩ := by ext <;> simp [hs, hr, ht]
  rw [← Subgroup.orderOf_coe σ]
  change orderOf C ∣ 2
  rw [orderOf_dvd_iff_pow_eq_one, hCeq, Work.Arithmetic.vc_pow_zero, hu2,
    WeierstrassCurve.VariableChange.one_def]

end Work.PointlessIndexFive
