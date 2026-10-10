/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessIndexFive
-/
import Mathlib
import Submission.Work.Arithmetic.Aut_orderOf_dvd_of_short
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The automorphism bound of Silverman, *AEC*, A.1.2, as a property

`Work.TorsorExistence.FiveTorsionCurve` (and `Work.Arithmetic.Torsor`, and
`Work.TorsorExistence.OrderAutCurve`) carry Silverman, *AEC*, Proposition A.1.2 as the field
`order_aut : ∀ σ : Aut 𝕜 E, orderOf σ ∣ 2 ∨ orderOf σ ∣ 6`.  This file collects that
predicate and the two general facts about it that the construction of a *single* curve carrying
both the bound and a rational point of order `5` needs:

* `HasGoodAut` — the predicate itself;
* `HasGoodAut.of_smul_eq` — it transports along a change of variables, because conjugation by
  `C` identifies `Aut 𝕜 (C • W)` with `Aut 𝕜 W` and conjugation preserves orders;
* `hasGoodAut_short` — the short model `y² = x³ + a₄x + a₆` with `a₆ ≠ 0` in characteristic
  `≠ 2, 3` (this is `Work.Arithmetic.Aut_orderOf_dvd_of_short`, restated for `HasGoodAut`);
* `a₆_ne_zero_of_short` — for a short model with `j ≠ 1728`, necessarily `a₆ ≠ 0` (if `a₆ = 0`
  then `j = 1728`), which is the hypothesis `Aut_orderOf_dvd_of_short` consumes.

## Main results

* `Work.PointlessIndexFive.HasGoodAut`
* `Work.PointlessIndexFive.hasGoodAut_of_smul_eq`
* `Work.PointlessIndexFive.hasGoodAut_short`
* `Work.PointlessIndexFive.a₆_ne_zero_of_short`
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.PointlessIndexFive

open WeierstrassCurve

/-- **Silverman, *AEC*, Proposition A.1.2** as a property of a Weierstrass model: every
automorphism of `W` has order dividing `2` or `6`.  (For `j(W) ≠ 1728` this always holds; the
predicate is what `FiveTorsionCurve.order_aut` consumes.)

The `orderOf` is that of the group `Work.Arithmetic.Aut 𝕜 W` (the stabiliser of the model in the
group of admissible variable changes), not of `VariableChange 𝕜`. -/
def HasGoodAut {𝕜 : Type} [Field 𝕜] (W : WeierstrassCurve 𝕜) : Prop :=
  ∀ σ : Work.Arithmetic.Aut 𝕜 W, orderOf σ ∣ 2 ∨ orderOf σ ∣ 6

/-- Conjugation in a group preserves the order of an element. -/
theorem orderOf_conj' {G : Type*} [Group G] (a b : G) :
    orderOf (a * b * a⁻¹) = orderOf b := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  have hpow : (a * b * a⁻¹) ^ n = a * b ^ n * a⁻¹ := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, pow_succ]; group
  rw [hpow]
  constructor
  · intro h
    have := congrArg (fun z => a⁻¹ * z * a) h
    simpa [mul_assoc] using this
  · intro h; rw [h]; group

/-- **`HasGoodAut` transports along a change of variables.**  If `C • W = W'` then conjugation
by `C` is a group isomorphism `Aut 𝕜 W ≃* Aut 𝕜 W'`, so the automorphism orders of `W` are
exactly those of `W'`. -/
theorem hasGoodAut_of_smul_eq {𝕜 : Type} [Field 𝕜] {W W' : WeierstrassCurve 𝕜}
    (C : WeierstrassCurve.VariableChange 𝕜) (hC : C • W = W') (h : HasGoodAut W') :
    HasGoodAut W := by
  have hCinv : C⁻¹ • W' = W := by rw [← hC, ← mul_smul, inv_mul_cancel, one_smul]
  intro σ
  let τ : Work.Arithmetic.Aut 𝕜 W' := ⟨C * (σ : WeierstrassCurve.VariableChange 𝕜) * C⁻¹, by
    show (C * (σ : WeierstrassCurve.VariableChange 𝕜) * C⁻¹) • W' = W'
    rw [mul_smul, mul_smul, hCinv, σ.2, hC]⟩
  have hord : orderOf τ = orderOf σ := by
    rw [← Subgroup.orderOf_coe τ, ← Subgroup.orderOf_coe σ]
    exact orderOf_conj' C (σ : WeierstrassCurve.VariableChange 𝕜)
  obtain hd | hd := h τ
  · exact Or.inl (hord ▸ hd)
  · exact Or.inr (hord ▸ hd)

/-- **Silverman, *AEC*, A.1.2 for short models in characteristic `≠ 2, 3`.**  If the short
Weierstrass model `y² = x³ + a₄x + a₆` has `a₆ ≠ 0` (the hypothesis of
`Work.Arithmetic.Aut_orderOf_dvd_of_short` after it has extracted `a₆ ≠ 0` from
`hEll`/`hJ`), then every automorphism has order dividing `2` or `6`. -/
theorem hasGoodAut_short {𝕜 : Type} [Field 𝕜] (a₄ a₆ : 𝕜) (h2 : (2 : 𝕜) ≠ 0)
    (h3 : (3 : 𝕜) ≠ 0) (ha₆ : a₆ ≠ 0) :
    HasGoodAut (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜) :=
  fun σ => Work.Arithmetic.Aut_orderOf_dvd_of_short a₄ a₆ h2 h3 (Or.inr ha₆)
    (fun ⟨_, h⟩ => ha₆ h) σ

/-- **A short model with `j ≠ 1728` has `a₆ ≠ 0`.**  If `a₆ = 0` then (ellipticity forces
`a₄ ≠ 0` and) `j = 1728`.  This converts the hypothesis `j ≠ 1728` into the hypothesis `a₆ ≠ 0`
that the short-model form of Silverman A.1.2 consumes. -/
theorem a₆_ne_zero_of_short {𝕜 : Type} [Field 𝕜] (a₄ a₆ : 𝕜) (h2 : (2 : 𝕜) ≠ 0)
    [hE : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜).IsElliptic]
    (hj : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜).j ≠ 1728) : a₆ ≠ 0 := by
  intro h6
  have ha₄ : a₄ ≠ 0 := by
    intro h4
    have hΔ0 : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜).Δ = 0 := by
      simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈, h4, h6]
    exact (isUnit_iff_ne_zero.mp hE.isUnit) hΔ0
  have hj1728 : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜).j = 1728 := by
    rw [WeierstrassCurve.j_eq]
    have key : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜).Δ = -64 * a₄ ^ 3 := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈, h6]
      first | refl_ring1 | ring
    have key2 : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve 𝕜).c₄ = -48 * a₄ := by
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      first | refl_ring1 | ring
    rw [key, key2]
    have h64 : (64 : 𝕜) ≠ 0 := by
      have : (64 : 𝕜) = 2 ^ 6 := by norm_num
      rw [this]; exact pow_ne_zero 6 h2
    rw [mul_pow]
    field_simp
    norm_num
  exact hj hj1728

end Work.PointlessIndexFive
