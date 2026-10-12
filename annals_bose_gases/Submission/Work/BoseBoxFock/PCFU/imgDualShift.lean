import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.PCFU.coulombDual_W1_le
import Submission.Work.BoseBoxFock.PCFU.dirichlet_comp_const_sub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.imgDualShift`

The **shifted** (translated/reflected) form of the `Ḣ^{-1}`–`Ḣ¹` duality bound for the FS §4
kernel `W₁ = W1fun v h ℓ`: for `ψ ∈ C_c^∞(ℝ³)` and any shift `c`,

    ‖∫_y W₁(c − y) ψ(y) dy‖² ≤ 64π·(a v)·∑_j ∫_u ‖∂_jψ(u)‖² .

This is exactly the duality theorem `Work.BoseBoxFock.L1Tails.coulombDual` (through its `W₁`
instance `coulombDual_W1_le`, whose constant `(4π)⁻¹·256π² = 64π` is the one appearing here)
applied to the **reflected test function** `ψ_c(y) := ψ(c − y)`: the reflection `y ↦ c − y` is a
measure preserving homeomorphism of `ℝ³`, so

* the pairing transforms as `∫_x W₁(x)ψ_c(x)dx = ∫_y W₁(c − y)ψ(y)dy`
  (`MeasureTheory.integral_sub_left_eq_self`), and
* the Dirichlet energy is invariant, `∑_j∫_x ‖∂_j(ψ_c)(x)‖² = ∑_j∫_u ‖∂_jψ(u)‖²`
  (the sibling `dirichlet_comp_const_sub`).

No evenness of `W₁` is used: the *test function* is reflected, not the kernel.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem imgDualShift {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (c : EuclideanSpace ℝ (Fin 3)) {Ψ : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    ‖∫ y : EuclideanSpace ℝ (Fin 3),
        ((Work.BoseFixR.W1fun v h ℓ (c - y) : ℝ) : ℂ) * Ψ y‖ ^ 2
      ≤ 64 * Real.pi * BoseGases.a v
        * ∑ k : Fin 3, ∫ u : EuclideanSpace ℝ (Fin 3),
            ‖fderiv ℝ Ψ u (EuclideanSpace.single k (1 : ℝ))‖ ^ 2 := by
  -- the reflected test function `Ψ_c(y) = Ψ (c − y)`
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => c - y) := contDiff_const.sub contDiff_id
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => Ψ (c - y)) := hΨ.comp hsm
  have hψc : HasCompactSupport (fun y : E3 => Ψ (c - y)) := by
    have h := hΨc.comp_homeomorph (Homeomorph.subLeft c)
    simpa [Function.comp_def] using h
  -- the `W₁`-instance of the Coulomb duality at the reflected test function
  have hdual := coulombDual_W1_le (v := v) (h := h) (R := R) (ℓ := ℓ)
      hR hv hvrad hv_supp hℓ hRℓ hψ hψc
  -- the reflection `y ↦ c − y` relates the two pairings
  have hshift : (∫ x : E3, ((Work.BoseFixR.W1fun v h ℓ x : ℝ) : ℂ) * Ψ (c - x))
      = ∫ y : E3, ((Work.BoseFixR.W1fun v h ℓ (c - y) : ℝ) : ℂ) * Ψ y := by
    simpa using (MeasureTheory.integral_sub_left_eq_self
      (fun x : E3 => ((Work.BoseFixR.W1fun v h ℓ x : ℝ) : ℂ) * Ψ (c - x)) volume c).symm
  -- and the reflected Dirichlet energy is the original one
  have hK : (∑ j : Fin 3, ∫ x : E3,
        ‖fderiv ℝ (fun y : E3 => Ψ (c - y)) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = ∑ j : Fin 3, ∫ u : E3, ‖fderiv ℝ Ψ u (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
    Finset.sum_congr rfl (fun j _ => dirichlet_comp_const_sub hΨ1 c j)
  rw [hshift, hK] at hdual
  exact hdual

end Work.BoseBoxFock.PCFU
