/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TorsorExistence
-/
import Mathlib
import Submission.Work.Arithmetic.Defs
import Submission.Work.TorsorExistence.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# An elliptic curve with `j ≠ 1728` and `Aut(E) ⊆ {1}` over a field of characteristic `2`

The proof of Silverman, *AEC*, Proposition A.1.2 in characteristic `2`, using the curve
`E : y² + xy = x³ + 1` (the model `⟨1, 0, 0, 0, 1⟩`).  Over a field of characteristic `2`
its invariants are `Δ = 1` and `j = 1`, so `j ≠ 0 = 1728`; and an admissible variable change
`C = (u, r, s, t)` with `C • E = E` is forced by the first, third and sixth coefficient
equations to satisfy `u = 1`, `r = 0`, `t = 0`, whence `C ^ 2 = 1`, i.e. every automorphism
of `E` has order dividing `2` (Silverman, *AEC*, A.1.2).
-/

set_option linter.style.haveILetI false

namespace Work.TorsorExistence

noncomputable section

/-- The Weierstrass model `y² + xy = x³ + 1`, that is `⟨1, 0, 0, 0, 1⟩`: its coefficients are
`a₁ = 1` and `a₆ = 1`, all the others being `0`. -/
private def curveCharTwo (𝕜 : Type) [Field 𝕜] : WeierstrassCurve 𝕜 := ⟨1, 0, 0, 0, 1⟩

/-- In characteristic `2` the curve `y² + xy = x³ + 1` has discriminant `Δ = 1`: with
`a₁ = 1`, `a₂ = a₃ = a₄ = 0`, `a₆ = 1` we get `b₈ = a₁ ^ 2 * a₆ = 1` and
`Δ = a₁ ^ 4 * b₈ = 1`. -/
private lemma curveCharTwo_Δ (𝕜 : Type) [Field 𝕜] [CharP 𝕜 2] :
    (curveCharTwo 𝕜).Δ = 1 := by
  rw [WeierstrassCurve.Δ_of_char_two, WeierstrassCurve.b₈_of_char_two]
  simp [curveCharTwo]

/-- `y² + xy = x³ + 1` is an elliptic curve over a field of characteristic `2`. -/
private lemma curveCharTwo_isElliptic (𝕜 : Type) [Field 𝕜] [CharP 𝕜 2] :
    (curveCharTwo 𝕜).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, curveCharTwo_Δ]
  exact isUnit_one

/-- In characteristic `2` the curve `y² + xy = x³ + 1` has `j = 1`: by
`WeierstrassCurve.j_of_char_two`, `j = Δ'⁻¹ * a₁ ^ 12 = 1⁻¹ * 1 = 1`. -/
private lemma curveCharTwo_j (𝕜 : Type) [Field 𝕜] [CharP 𝕜 2]
    [h : (curveCharTwo 𝕜).IsElliptic] : (curveCharTwo 𝕜).j = 1 := by
  rw [WeierstrassCurve.j_of_char_two]
  have hΔ' : (curveCharTwo 𝕜).Δ' = 1 := by
    rw [Units.ext_iff, WeierstrassCurve.coe_Δ', curveCharTwo_Δ]
    rfl
  rw [hΔ']
  simp [curveCharTwo]

/-- In characteristic `2` the curve `y² + xy = x³ + 1` has `j = 1 ≠ 1728 = 0`. -/
private lemma curveCharTwo_j_ne (𝕜 : Type) [Field 𝕜] [CharP 𝕜 2]
    [h : (curveCharTwo 𝕜).IsElliptic] : (curveCharTwo 𝕜).j ≠ 1728 := by
  rw [curveCharTwo_j]
  intro hc
  have h1728 : (1728 : 𝕜) = 0 := by
    have h' := (CharP.cast_eq_zero_iff 𝕜 2 1728).mpr (by norm_num : 2 ∣ 1728)
    simpa using h'
  rw [h1728] at hc
  exact one_ne_zero hc

/-- **The key computation.**  Over a field of characteristic `2`, any admissible variable change
`C = (u, r, s, t)` fixing the curve `E : y² + xy = x³ + 1` satisfies `C ^ 2 = 1`; hence every
automorphism of `E` (which is exactly such a variable change, see `Work.Arithmetic.Aut`) has
order dividing `2`.

Comparing coefficients in `C • E = E` (here `2 = 0`):
* `a₁`: `u⁻¹ * (1 + 2s) = 1`, so `u⁻¹ = 1` and `u = 1`;
* `a₃`: `u⁻³ * (0 + r * 1 + 2t) = 0`, so `r = 0`;
* `a₆`: with `u = 1` and `r = 0`, `1 - t ^ 2 = 1`, so `t = 0`.

Then `C * C = (u ^ 2, r * u ^ 2 + r, u * s + s, t * u ^ 3 + r * s * u ^ 2 + t) = (1, 0, 2s, 0) = 1`. -/
private lemma curveCharTwo_sq_eq_one_of_smul_eq (𝕜 : Type) [Field 𝕜] [CharP 𝕜 2]
    (C : WeierstrassCurve.VariableChange 𝕜) (h : C • curveCharTwo 𝕜 = curveCharTwo 𝕜) :
    C ^ 2 = 1 := by
  have h2 : (2 : 𝕜) = 0 := CharP.cast_eq_zero 𝕜 2
  -- the `a₁` coefficient forces `u = 1`
  have h1 : (C • curveCharTwo 𝕜).a₁ = (curveCharTwo 𝕜).a₁ := by rw [h]
  rw [WeierstrassCurve.variableChange_a₁] at h1
  have huinv : C.u⁻¹ = 1 := by
    apply Units.ext
    simpa [curveCharTwo, h2, mul_add, add_mul, mul_one, add_zero] using h1
  have hu : C.u = 1 := by
    rw [← inv_eq_one]
    exact huinv
  -- the `a₃` coefficient forces `r = 0`
  have h3 : (C • curveCharTwo 𝕜).a₃ = (curveCharTwo 𝕜).a₃ := by rw [h]
  rw [WeierstrassCurve.variableChange_a₃] at h3
  have hr : C.r = 0 := by
    have h3' : (C.u : 𝕜)⁻¹ ^ 3 * C.r = 0 := by
      simpa [curveCharTwo, h2, add_zero, mul_zero, add_assoc] using h3
    exact (mul_eq_zero.mp h3').resolve_left
      (pow_ne_zero 3 (inv_ne_zero (Units.ne_zero C.u)))
  -- with `u = 1` and `r = 0` the `a₆` coefficient forces `t = 0`
  have h6 : (C • curveCharTwo 𝕜).a₆ = (curveCharTwo 𝕜).a₆ := by rw [h]
  rw [WeierstrassCurve.variableChange_a₆] at h6
  have ht : C.t = 0 := by
    rw [hu, hr] at h6
    simpa [curveCharTwo, h2] using h6
  -- the coefficients of `C * C` are `(u ^ 2, r * u ^ 2 + r, u * s + s, t * u ^ 3 + r * s * u ^ 2 + t)`
  rw [pow_two, WeierstrassCurve.VariableChange.mul_def]
  ext
  · simp [WeierstrassCurve.VariableChange.one_def, hu]
  · simp [WeierstrassCurve.VariableChange.one_def, hr]
  · simp only [WeierstrassCurve.VariableChange.one_def]
    rw [hu, Units.val_one, one_mul, ← two_mul, h2, zero_mul]
  · simp [WeierstrassCurve.VariableChange.one_def, hu, hr, ht]

/-- Over a field of characteristic `2` there is an elliptic curve with `j ≠ 1728` and with
every automorphism of order dividing `2` or `6` (Silverman, *AEC*, A.1.2).  (Route: take
`E : y² + xy = x³ + 1`, i.e. the Weierstrass curve `⟨1, 0, 0, 0, 1⟩`; then `Δ = 1 ≠ 0` and
`j = 1 ≠ 0 = 1728` in characteristic `2`.  Comparing the coefficients of an admissible variable
change `C = (u, r, s, t)` with `C • E = E` using the lemmas `WeierstrassCurve.variableChange_aᵢ`
gives `u = 1`, `r = 0`, `s ^ 2 + s = 0` (i.e. `s ∈ 𝔽₂`) and `t = 0`, so that `C ^ 2 = 1`.) -/
theorem nonempty_orderAutCurve_char_two {𝕜 : Type} [Field 𝕜] [CharP 𝕜 2] :
    Nonempty (OrderAutCurve 𝕜) := by
  have hEll : (curveCharTwo 𝕜).IsElliptic := curveCharTwo_isElliptic 𝕜
  haveI := hEll
  refine ⟨{ E := curveCharTwo 𝕜, isElliptic := hEll, j_ne := curveCharTwo_j_ne 𝕜,
            order_aut := ?_ }⟩
  intro σ
  refine Or.inl (orderOf_dvd_iff_pow_eq_one.mpr ?_)
  exact Subtype.ext (curveCharTwo_sq_eq_one_of_smul_eq 𝕜 _ σ.2)

end

end Work.TorsorExistence
