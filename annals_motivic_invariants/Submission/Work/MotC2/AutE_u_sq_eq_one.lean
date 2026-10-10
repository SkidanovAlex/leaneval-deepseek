import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- **Silverman, *AEC*, Prop. A.1.2: the `u`-coefficient of an automorphism of an elliptic
Weierstrass model with `j ≠ 0, 1728` satisfies `u ^ 2 = 1`.**

Route (all in `L`, with `Δ = E.Δ` the discriminant, `E.Δ'` its unit form):
* `hj0 : E.j ≠ 0` and `WeierstrassCurve.j_eq_zero : W.c₄ = 0 → W.j = 0` give `E.c₄ ≠ 0`.
* `WeierstrassCurve.c_relation : 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2` and
  `WeierstrassCurve.j_eq : W.j = W.Δ⁻¹ * W.c₄ ^ 3` give `E.c₆ ≠ 0`: if `E.c₆ = 0` then
  `E.c₄ ^ 3 = 1728 * E.Δ`, hence `E.j = E.Δ⁻¹ * (1728 * E.Δ) = 1728`, contradicting `hj`.
  (`E.Δ ≠ 0` because `E.IsElliptic` says `E.Δ` is a unit.)
* `C • E = E` and `WeierstrassCurve.variableChange_c₄ : (C • W).c₄ = ↑C.u⁻¹ ^ 4 * W.c₄`
  give `E.c₄ = ↑C.u⁻¹ ^ 4 * E.c₄`, so `↑C.u⁻¹ ^ 4 = 1` by `mul_right_cancel₀` (or by
  subtracting `E.c₄` and cancelling), i.e. `C.u⁻¹ ^ 4 = 1` by `Units.ext`, i.e. `C.u ^ 4 = 1`
  (`inv_pow`, `inv_eq_one`).
* Likewise `variableChange_c₆` gives `C.u ^ 6 = 1`.
* Finally `C.u ^ 6 = C.u ^ 4 * C.u ^ 2` (`← pow_add`, `4 + 2 = 6`), so `C.u ^ 2 = 1`. -/
theorem AutE_u_sq_eq_one {L : Type*} [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (hj0 : E.j ≠ 0) (hj : E.j ≠ 1728)
    (C : WeierstrassCurve.VariableChange L) (hC : C • E = E) : C.u ^ 2 = 1 := by
  -- `E.Δ ≠ 0` since `E` is elliptic.
  have hΔ : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  -- `E.c₄ ≠ 0`, as otherwise `E.j = 0`.
  have hc4 : E.c₄ ≠ 0 := fun h => hj0 (E.j_eq_zero h)
  -- `E.c₆ ≠ 0`, as otherwise `1728 * E.Δ = E.c₄ ^ 3`, whence `E.j = 1728`.
  have hc6 : E.c₆ ≠ 0 := by
    intro h
    apply hj
    have hrel := E.c_relation
    rw [h, zero_pow (by norm_num : (2 : Nat) ≠ 0), sub_zero] at hrel
    have h3 : E.c₄ ^ 3 = 1728 * E.Δ := hrel.symm
    rw [WeierstrassCurve.j_eq, h3, mul_comm (1728 : L) E.Δ, ← mul_assoc, inv_mul_cancel₀ hΔ,
      one_mul]
  -- `C • E = E` turns the transformation formulas for `c₄` and `c₆` into `↑u⁻¹ ^ 4 = 1`
  -- and `↑u⁻¹ ^ 6 = 1` (cancelling `E.c₄`, resp. `E.c₆`).
  have hc4' : E.c₄ = (↑C.u⁻¹ : L) ^ 4 * E.c₄ := by
    have := WeierstrassCurve.variableChange_c₄ E C
    rwa [hC] at this
  have hu4 : (↑C.u⁻¹ : L) ^ 4 = 1 := by
    apply mul_right_cancel₀ hc4
    simpa using hc4'.symm
  have hc6' : E.c₆ = (↑C.u⁻¹ : L) ^ 6 * E.c₆ := by
    have := WeierstrassCurve.variableChange_c₆ E C
    rwa [hC] at this
  have hu6 : (↑C.u⁻¹ : L) ^ 6 = 1 := by
    apply mul_right_cancel₀ hc6
    simpa using hc6'.symm
  -- Upgrade to the unit group and invert.
  have hu4u : C.u⁻¹ ^ 4 = 1 := by
    rw [← Units.val_inj]
    simpa using hu4
  have hu6u : C.u⁻¹ ^ 6 = 1 := by
    rw [← Units.val_inj]
    simpa using hu6
  have hu4' : C.u ^ 4 = 1 := by
    have h : (C.u ^ 4)⁻¹ = 1 := by
      rw [← inv_pow]
      exact hu4u
    exact inv_eq_one.mp h
  have hu6' : C.u ^ 6 = 1 := by
    have h : (C.u ^ 6)⁻¹ = 1 := by
      rw [← inv_pow]
      exact hu6u
    exact inv_eq_one.mp h
  -- `C.u ^ 6 = C.u ^ 4 * C.u ^ 2`, with both sides' factors known.
  have h := pow_add C.u 4 2
  rw [show (4 : Nat) + 2 = 6 from rfl, hu6', hu4', one_mul] at h
  exact h.symm

end Work.MotC2
