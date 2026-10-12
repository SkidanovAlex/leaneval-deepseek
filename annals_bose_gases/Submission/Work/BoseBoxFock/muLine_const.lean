import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.muLine_const` — constants are invisible in the `μ`-line

The `μ`-line of the χ-row, `muLine n ℓ w Φ = 2 Σ_j ∫_{abox}(Q_jΦ)·w(x_j)·(P_jΦ)`, vanishes for a
constant weight `w ≡ c`.

## Mathematics

Apply the slot-`j` only identity of `Work.BoseBoxFock.chiRow_muLine_slot` (with `g ≡ c`): the left
side of that identity is `Σ_j ∫ Φ·Q_j((g(·_j) − c̄)·P_jΦ)` with `c̄ = (ℓ³)⁻¹∫_{acube} g = c` the
cube mean of the *constant* function `c`, so the inner function is `0·P_jΦ = 0` and the whole sum
vanishes; the right side is exactly the sum defining `muLine`. Hence `muLine = 2·0 = 0`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false

open Submission.BoseGases

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

theorem muLine_const {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) (c : ℝ) :
    Work.BoseBoxFock.muLine n ℓ (fun _ : EuclideanSpace ℝ (Fin 3) => c) Φ = 0 := by
  have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
  -- the cube mean of the constant function `c` is `c`
  have hmeanj : (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, (fun _ : Sp => c) z) = c := by
    have h : (∫ z in acube ℓ, (fun _ : Sp => c) z) = c * ℓ ^ 3 := by
      simpa using Submission.BoseGases.integral_const_acube ℓ hℓ c
    rw [h, mul_comm c (ℓ ^ 3), inv_mul_cancel_left₀ hℓ3]
  -- the left-hand side of `chiRow_muLine_slot` at `g ≡ c` vanishes
  have hL : (∑ j : Fin n, ∫ x in abox n ℓ, Φ x * (aQ ℓ j (fun y : X n =>
      ((fun _ : Sp => c) (y j) - (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, (fun _ : Sp => c) z)) *
        aP ℓ j Φ y) x)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hZ : (fun y : X n =>
        ((fun _ : Sp => c) (y j) - (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, (fun _ : Sp => c) z)) *
          aP ℓ j Φ y) = fun _ : X n => (0 : ℝ) := by
      funext y
      show ((fun _ : Sp => c) (y j)
          - (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, (fun _ : Sp => c) z)) * aP ℓ j Φ y = 0
      rw [hmeanj]
      ring
    have hzero : ∀ x : X n, aQ ℓ j (fun _ : X n => (0 : ℝ)) x = 0 := by
      intro x
      unfold aQ aP
      simp
    calc (∫ x in abox n ℓ, Φ x * (aQ ℓ j (fun y : X n =>
            ((fun _ : Sp => c) (y j)
              - (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, (fun _ : Sp => c) z)) * aP ℓ j Φ y) x))
        = ∫ x in abox n ℓ, Φ x * (aQ ℓ j (fun _ : X n => (0 : ℝ)) x) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hZ]
      _ = 0 := by simp [hzero]
  have hconst := chiRow_muLine_slot (n := n) (ℓ := ℓ) hℓ hΦc
    (g := fun _ : Sp => c) continuous_const
  have hR : (∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) * (fun _ : Sp => c) (x j) *
      (aP ℓ j Φ x)) = 0 := by
    rw [hL] at hconst
    exact hconst.symm
  rw [show muLine n ℓ (fun _ : Sp => c) Φ
      = 2 * (∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) * (fun _ : Sp => c) (x j) *
          (aP ℓ j Φ x)) from rfl, hR, mul_zero]

end Work.BoseBoxFock
