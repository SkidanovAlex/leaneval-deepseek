import Mathlib
import Submission.Work.Arithmetic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Arithmetic

/-- Powers of the admissible change of variables `(u, 0, 0, 0)`:
`(u, 0, 0, 0) ^ n = (u ^ n, 0, 0, 0)`. -/
lemma vc_pow_zero {𝕜 : Type} [CommRing 𝕜] (u : 𝕜ˣ) (n : ℕ) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange 𝕜) ^ n =
      ⟨u ^ n, 0, 0, 0⟩ := by
  induction n with
  | zero => simp [WeierstrassCurve.VariableChange.one_def]
  | succ n ih =>
    rw [pow_succ, ih, WeierstrassCurve.VariableChange.mul_def]
    ext <;> simp [pow_succ]

/-
Silverman, *The Arithmetic of Elliptic Curves*, Proposition A.1.2, for short Weierstrass
models in characteristic `≠ 2, 3`: if `W : y² = x³ + a₄x + a₆` is not the singular case
`a₄ = a₆ = 0` and we are not in the case `a₄ ≠ 0, a₆ = 0` (where `j = 1728`), then every
automorphism of `W` has order dividing `2` or `6`.  This is exactly the input used by
Lin-Shinder in the proof of Lemma `lem:torsors` and by Shinder-Zhang, Lemma 2.7 ("there is
no σ ∈ Aut(E) of order 4 when j ≠ 1728, for any field").

Here `Work.Arithmetic.Aut 𝕜 W` is the subgroup of `WeierstrassCurve.VariableChange 𝕜`
fixing `W` (Mathlib's group of admissible variable changes is a group acting on Weierstrass
curves, so the stabilizer is a group).

Route.  Let `C = (u, r, s, t) : VariableChange 𝕜` satisfy `C • W = W`.  Using Mathlib's
`WeierstrassCurve.variableChange_aᵢ` (`(C • W).aᵢ = ...`, all with the *inverse* `u⁻¹`):
* `a₁` gives `u⁻¹ * (2 * s) = 0`, so `s = 0` (by `h2`);
* `a₂` gives `u⁻¹ ^ 2 * (3 * r - s ^ 2) = 0`, so `r = 0` (by `h3`, `s = 0`);
* `a₃` gives `u⁻¹ ^ 3 * (2 * t) = 0`, so `t = 0` (by `h2`);
* `a₄` and `a₆` become `u⁻¹ ^ 4 * a₄ = a₄` and `u⁻¹ ^ 6 * a₆ = a₆`, i.e.
  `(u ^ 4 - 1) * a₄ = 0` and `(u ^ 6 - 1) * a₆ = 0`.
Case `a₄ = 0`: then `hEll` gives `a₆ ≠ 0`, so `u ^ 6 = 1`, and since
`C ^ n = ⟨u ^ n, 0, 0, 0⟩` (induction from `VariableChange.mul_def`, `one_def`) we get
`C ^ 6 = 1`, i.e. `orderOf σ ∣ 6` (`orderOf_dvd_iff_pow_eq_one`).
Case `a₄ ≠ 0`: then `hJ` gives `a₆ ≠ 0`, so `u ^ 4 = u ^ 6 = 1`, hence `u ^ 2 = 1`, hence
`C ^ 2 = 1`, i.e. `orderOf σ ∣ 2`.
-/
theorem Aut_orderOf_dvd_of_short {𝕜 : Type} [Field 𝕜] (a₄ a₆ : 𝕜)
    (h2 : (2 : 𝕜) ≠ 0) (h3 : (3 : 𝕜) ≠ 0) (hEll : a₄ ≠ 0 ∨ a₆ ≠ 0)
    (hJ : ¬ (a₄ ≠ 0 ∧ a₆ = 0))
    (σ : Work.Arithmetic.Aut 𝕜 (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜)) :
    orderOf σ ∣ 2 ∨ orderOf σ ∣ 6 := by
  let W : WeierstrassCurve 𝕜 := ⟨0, 0, 0, a₄, a₆⟩
  -- work with the underlying variable change, so that `a₄`, `a₆` no longer occur in the
  -- type of any term and the coefficient computations can be rewritten freely
  let C : WeierstrassCurve.VariableChange 𝕜 := ↑σ
  have hC : C • W = W := σ.2
  -- the coefficient `s` of `σ` vanishes
  have hs : C.s = 0 := by
    have h := congrArg WeierstrassCurve.a₁ hC
    rw [WeierstrassCurve.variableChange_a₁] at h
    simp [W] at h
    exact h.resolve_left h2
  -- the coefficient `r` of `σ` vanishes
  have hr : C.r = 0 := by
    have h := congrArg WeierstrassCurve.a₂ hC
    rw [WeierstrassCurve.variableChange_a₂] at h
    simp [W, hs] at h
    exact h.resolve_left h3
  -- the coefficient `t` of `σ` vanishes
  have ht : C.t = 0 := by
    have h := congrArg WeierstrassCurve.a₃ hC
    rw [WeierstrassCurve.variableChange_a₃] at h
    simp [W, hr] at h
    exact h.resolve_left h2
  -- hence `σ` is the diagonal change of variables `(u, 0, 0, 0)`
  have hCeq : C = ⟨C.u, 0, 0, 0⟩ := by
    ext <;> simp [hs, hr, ht]
  -- the `a₄`-coefficient of `σ • W = W`
  have h4 : ((↑C.u : 𝕜) ^ 4)⁻¹ * a₄ = a₄ := by
    have h := congrArg WeierstrassCurve.a₄ hC
    rw [WeierstrassCurve.variableChange_a₄] at h
    simpa [W, hr, ht] using h
  -- the `a₆`-coefficient of `σ • W = W`
  have h6 : ((↑C.u : 𝕜) ^ 6)⁻¹ * a₆ = a₆ := by
    have h := congrArg WeierstrassCurve.a₆ hC
    rw [WeierstrassCurve.variableChange_a₆] at h
    simpa [W, hr, ht] using h
  -- `hJ` together with `hEll` gives `a₆ ≠ 0`
  have ha₆ : a₆ ≠ 0 := by
    intro h
    exact hJ ⟨hEll.resolve_right (by simpa using h), h⟩
  -- so `u ^ 6 = 1`
  have hu6 : C.u ^ 6 = 1 := Units.ext (by
    have hne : (↑C.u : 𝕜) ^ 6 ≠ 0 := pow_ne_zero 6 (Units.ne_zero _)
    have key : (↑C.u : 𝕜) ^ 6 * a₆ = a₆ := by
      conv_lhs => rw [← h6]
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    have hzero : ((↑C.u : 𝕜) ^ 6 - 1) * a₆ = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    have h1 : (↑C.u : 𝕜) ^ 6 = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right ha₆)
    simpa using h1)
  by_cases ha₄ : a₄ = 0
  · -- case `a₄ = 0`: `σ ^ 6 = 1`, hence `orderOf σ ∣ 6`
    refine Or.inr ?_
    rw [← Subgroup.orderOf_coe σ]
    change orderOf C ∣ 6
    rw [orderOf_dvd_iff_pow_eq_one]
    rw [hCeq, vc_pow_zero, hu6]
    rfl
  · -- case `a₄ ≠ 0`: `u ^ 4 = 1` and `u ^ 6 = 1`, hence `u ^ 2 = 1` and `orderOf σ ∣ 2`
    have hu4 : C.u ^ 4 = 1 := Units.ext (by
      have hne : (↑C.u : 𝕜) ^ 4 ≠ 0 := pow_ne_zero 4 (Units.ne_zero _)
      have key : (↑C.u : 𝕜) ^ 4 * a₄ = a₄ := by
        conv_lhs => rw [← h4]
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      have hzero : ((↑C.u : 𝕜) ^ 4 - 1) * a₄ = 0 := by
        rw [sub_mul, one_mul, key, sub_self]
      have h1 : (↑C.u : 𝕜) ^ 4 = 1 :=
        sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right ha₄)
      simpa using h1)
    have hu2 : C.u ^ 2 = 1 := by
      have key : C.u ^ 4 * C.u ^ 2 = 1 := by
        rw [← pow_add]
        exact hu6
      rw [hu4, one_mul] at key
      exact key
    refine Or.inl ?_
    rw [← Subgroup.orderOf_coe σ]
    change orderOf C ∣ 2
    rw [orderOf_dvd_iff_pow_eq_one]
    rw [hCeq, vc_pow_zero, hu2]
    rfl

end Work.Arithmetic
