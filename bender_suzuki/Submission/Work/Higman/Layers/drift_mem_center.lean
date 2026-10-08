/-
Copyright (c) 2024. All rights reserved.

# The action of `ξ` on `P / Z(P)` for a Suzuki 2-group

Let `P` be a Suzuki 2-group (`Work.Higman.IsSuzuki2Grp`) with `ξ` of order `q - 1 = |Z(P)| - 1`
acting semiregularly on `P ∖ {1}` (`Work.Higman.FpfXi`).  This file collects the group-theoretic
input for the layer dichotomy:

* `center_card_eq_two_pow`: `|Z(P)| = 2 ^ n`;
* `drift_mem_center`: if `ξ ^ k ≠ 1` and the "drift" `ξ ^ k x * x⁻¹` of `x` is central, then `x`
  is central — equivalently, `ξ ^ k` has no non-zero fixed vector on `P / Z(P)`.

The proof of the second statement is the "drift homomorphism" argument: the elements of `P` whose
drift is central form a subgroup `Y`, the drift is a homomorphism `Y → Z(P)` (the drift of a
product is the product of the drifts, because a drift is central), and it is *injective* because a
drift of `1` means `x` is fixed by `ξ ^ k`, so `x = 1`.  Hence `|Y| ≤ |Z(P)|` while `Z(P) ≤ Y`,
so `Y = Z(P)`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.typeB
import Submission.Work.Higman.card_eq_sq_or_cube
import Submission.Work.Higman.suzuki_class_two_squares

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.Higman

open LeanEval.GroupTheory.Defs

variable {P : Type} [Group P] [Finite P]

/-- The centre of a Suzuki 2-group has order a power of `2`. -/
theorem center_card_eq_two_pow (h : IsSuzuki2Grp P) :
    ∃ n : ℕ, Nat.card ↥(Subgroup.center P) = 2 ^ n :=
  (h.isPGroup.to_subgroup (Subgroup.center P)).exists_card_eq

/-- **Trivial fixed points of `ξ ^ k` on `P / Z(P)`.**  If `ξ ^ k ≠ 1` (with `⟨ξ⟩` semiregular on
`P ∖ {1}`) and the "drift" `ξ ^ k x * x⁻¹` of `x` is central, then `x` is central.  In other words
`ξ ^ k` fixes no non-trivial coset of `Z(P)`. -/
theorem drift_mem_center (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) {k : ℕ}
    (hk : ξ ^ k ≠ 1) {x : P} (hx : (ξ ^ k) x * x⁻¹ ∈ Subgroup.center P) :
    x ∈ Subgroup.center P := by
  classical
  set Z : Subgroup P := Subgroup.center P with hZ
  -- the subgroup `Y` of elements with central drift
  let Y : Subgroup P :=
    { carrier := {y : P | (ξ ^ k) y * y⁻¹ ∈ Z}
      one_mem' := by
        show (ξ ^ k) (1 : P) * (1 : P)⁻¹ ∈ Z
        simp
      mul_mem' := by
        intro a b ha hb
        have hc : ∀ w : P, ((ξ ^ k) b * b⁻¹) * w = w * ((ξ ^ k) b * b⁻¹) :=
          fun w => (Subgroup.mem_center_iff.mp hb w).symm
        show (ξ ^ k) (a * b) * (a * b)⁻¹ ∈ Z
        rw [map_mul]
        rw [show (ξ ^ k) a * (ξ ^ k) b * (a * b)⁻¹ =
          (ξ ^ k) a * (((ξ ^ k) b * b⁻¹) * a⁻¹) by group]
        rw [hc a⁻¹]
        rw [show (ξ ^ k) a * (a⁻¹ * ((ξ ^ k) b * b⁻¹)) =
          ((ξ ^ k) a * a⁻¹) * ((ξ ^ k) b * b⁻¹) by group]
        exact Z.mul_mem ha hb
      inv_mem' := by
        intro a ha
        show (ξ ^ k) a⁻¹ * (a⁻¹)⁻¹ ∈ Z
        rw [map_inv, inv_inv]
        have h1 : (ξ ^ k) a = ((ξ ^ k) a * a⁻¹) * a := by group
        have h2 : ((ξ ^ k) a)⁻¹ * a = ((ξ ^ k) a * a⁻¹)⁻¹ := by
          rw [h1, mul_inv_rev]
          have hc : a⁻¹ * ((ξ ^ k) a * a⁻¹)⁻¹ = ((ξ ^ k) a * a⁻¹)⁻¹ * a⁻¹ :=
            Subgroup.mem_center_iff.mp (Z.inv_mem ha) a⁻¹
          rw [hc]
          group
        rw [h2]
        exact Z.inv_mem ha }
  have hZY : Z ≤ Y := by
    intro z hz
    show (ξ ^ k) z * z⁻¹ ∈ Z
    have h1 : (ξ ^ k) z ∈ Z := by
      rw [hZ] at hz ⊢
      have hmap := Subgroup.map_center_eq (ξ ^ k : P ≃* P)
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hz
    exact Z.mul_mem h1 (Z.inv_mem hz)
  -- the drift is injective on `Y`
  have hinj : Function.Injective (fun y : ↥Y => (⟨(ξ ^ k) (y : P) * (y : P)⁻¹, y.2⟩ : ↥Z)) := by
    intro a b hab
    have h1 : (ξ ^ k) (a : P) * (a : P)⁻¹ = (ξ ^ k) (b : P) * (b : P)⁻¹ := by
      have := congrArg (fun t : ↥Z => (t : P)) hab
      simpa using this
    have hb' : (ξ ^ k) (b : P) = ((ξ ^ k) (a : P) * (a : P)⁻¹) * (b : P) := by
      calc (ξ ^ k) (b : P) = ((ξ ^ k) (b : P) * (b : P)⁻¹) * (b : P) := by group
        _ = ((ξ ^ k) (a : P) * (a : P)⁻¹) * (b : P) := by rw [h1]
    have h2 : (ξ ^ k) ((a : P)⁻¹ * (b : P)) = (a : P)⁻¹ * (b : P) := by
      rw [map_mul, map_inv, hb']
      group
    have h3 : (a : P)⁻¹ * (b : P) = 1 := hξ.fpf k hk _ h2
    have h4 : (a : P) = (b : P) := by
      calc (a : P) = (a : P) * ((a : P)⁻¹ * (b : P)) := by rw [h3, mul_one]
        _ = (b : P) := by group
    exact Subtype.ext h4
  have hcard : Nat.card ↥Y ≤ Nat.card ↥Z := Nat.card_le_card_of_injective _ hinj
  have hYZ : Y = Z := (Subgroup.eq_of_le_of_card_ge hZY hcard).symm
  have hxY : x ∈ Y := hx
  rw [hYZ] at hxY
  exact hxY

end Work.Higman
