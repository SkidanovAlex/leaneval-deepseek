import Submission.NBody.Action
import Mathlib

/-!
# The fixed time action potential

`actionPotTau m x y τ` is the infimum of the Lagrangian action (at `h = 0`) over paths joining `x`
to `y` in *exactly* time `τ` — the paper's `φ(x,y,τ)`.  The main result is that the `h`-action
potential of the paper is the infimum of `φ(x,y,τ) + hτ` over `τ > 0` (this is the identity used
in the proof of the Hölder estimate and in the definition of the Lax--Oleinik semigroup).

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The Lagrangian at level `0` plus the constant `h` is the Lagrangian at level `h`. -/
theorem lagrangian_add_const {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {h : ℝ} (hh : 0 ≤ h)
    (x v : EN E N) :
    lagrangian m h x v = lagrangian m 0 x v + ENNReal.ofReal h := by
  by_cases hx : WithoutCollisions x
  · rw [lagrangian, if_pos hx, lagrangian, if_pos hx]
    have hnn : 0 ≤ (1 / 2) * (∑ i, m i * ‖v i‖ ^ 2) + U m x := by
      have h1 : 0 ≤ ∑ i, m i * ‖v i‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (sq_nonneg _)
      have h2 := U_nonneg hm x
      linarith
    rw [show (1 / 2) * (∑ i, m i * ‖v i‖ ^ 2) + U m x + h
        = ((1 / 2) * (∑ i, m i * ‖v i‖ ^ 2) + U m x) + h from by ring,
      show (1 / 2) * (∑ i, m i * ‖v i‖ ^ 2) + U m x + 0
        = ((1 / 2) * (∑ i, m i * ‖v i‖ ^ 2) + U m x) from by ring,
      ENNReal.ofReal_add hnn hh]
  · rw [lagrangian, if_neg hx, lagrangian, if_neg hx, top_add]

/-- **The action at level `h` is the action at level `0` plus `hτ`.** -/
theorem actionOn_add_const {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {h : ℝ} (hh : 0 ≤ h)
    (γ : ℝ → EN E N) {τ : ℝ} (hτ : 0 ≤ τ) :
    actionOn m h γ 0 τ = actionOn m 0 γ 0 τ + ENNReal.ofReal h * ENNReal.ofReal τ := by
  unfold actionOn
  calc (∫⁻ t in Set.Ioc 0 τ, lagrangian m h (γ t) (deriv γ t))
      = ∫⁻ t in Set.Ioc 0 τ, (lagrangian m 0 (γ t) (deriv γ t) + ENNReal.ofReal h) :=
        lintegral_congr fun t => lagrangian_add_const hm hh _ _
    _ = (∫⁻ t in Set.Ioc 0 τ, lagrangian m 0 (γ t) (deriv γ t))
          + ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal h :=
        lintegral_add_right _ measurable_const
    _ = (∫⁻ t in Set.Ioc 0 τ, lagrangian m 0 (γ t) (deriv γ t))
          + ENNReal.ofReal h * ENNReal.ofReal τ := by
        rw [lintegral_const, Measure.restrict_apply_univ, volume_Ioc, sub_zero]

/-- The fixed-time action potential `φ(x,y,τ)`: the infimum of the (level `0`) action over
absolutely continuous curves joining `x` to `y` in exactly time `τ`. -/
noncomputable def actionPotTau (m : Fin N → ℝ) (x y : EN E N) (τ : ℝ) : ℝ≥0∞ :=
  ⨅ γ : {γ : ℝ → EN E N // γ 0 = x ∧ γ τ = y ∧ AbsolutelyContinuousOnInterval γ 0 τ},
    actionOn m 0 γ.1 0 τ

/-- The fixed-time action potential is at most the action of any admissible curve. -/
theorem actionPotTau_le_of {m : Fin N → ℝ} {x y : EN E N} {τ : ℝ} {γ : ℝ → EN E N}
    (h0 : γ 0 = x) (h1 : γ τ = y) (hac : AbsolutelyContinuousOnInterval γ 0 τ) :
    actionPotTau m x y τ ≤ actionOn m 0 γ 0 τ := by
  let p : {γ : ℝ → EN E N // γ 0 = x ∧ γ τ = y ∧ AbsolutelyContinuousOnInterval γ 0 τ} :=
    ⟨γ, h0, h1, hac⟩
  exact iInf_le (f := fun q : {γ : ℝ → EN E N // γ 0 = x ∧ γ τ = y ∧
      AbsolutelyContinuousOnInterval γ 0 τ} => actionOn m 0 q.1 0 τ) p

/-- **The `h`-action potential is the infimum over `τ` of `φ(x,y,τ) + hτ`.** -/
theorem actionPot_eq_iInf_actionPotTau {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (x y : EN E N) :
    actionPot m h x y
      = ⨅ τ : {τ : ℝ // 0 < τ},
          (actionPotTau m x y τ.1 + ENNReal.ofReal h * ENNReal.ofReal τ.1) := by
  rw [actionPot]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun τ => ?_
    have hkey : actionPotTau m x y τ.1 + ENNReal.ofReal h * ENNReal.ofReal τ.1
        = ⨅ σ : {σ : ℝ → EN E N //
            σ 0 = x ∧ σ τ.1 = y ∧ AbsolutelyContinuousOnInterval σ 0 τ.1},
            (actionOn m 0 σ.1 0 τ.1 + ENNReal.ofReal h * ENNReal.ofReal τ.1) := by
      rw [actionPotTau, ENNReal.iInf_add]
    rw [hkey]
    refine le_iInf fun σ => ?_
    have hle : (⨅ p : {p : ℝ × (ℝ → EN E N) //
          0 < p.1 ∧ p.2 0 = x ∧ p.2 p.1 = y ∧ AbsolutelyContinuousOnInterval p.2 0 p.1},
          actionOn m h p.1.2 0 p.1.1)
        ≤ actionOn m h σ.1 0 τ.1 :=
      iInf_le (f := fun p : {p : ℝ × (ℝ → EN E N) //
          0 < p.1 ∧ p.2 0 = x ∧ p.2 p.1 = y ∧ AbsolutelyContinuousOnInterval p.2 0 p.1}
          => actionOn m h p.1.2 0 p.1.1) ⟨(τ.1, σ.1), τ.2, σ.2.1, σ.2.2.1, σ.2.2.2⟩
    calc (⨅ p : {p : ℝ × (ℝ → EN E N) //
          0 < p.1 ∧ p.2 0 = x ∧ p.2 p.1 = y ∧ AbsolutelyContinuousOnInterval p.2 0 p.1},
          actionOn m h p.1.2 0 p.1.1) ≤ actionOn m h σ.1 0 τ.1 := hle
      _ = actionOn m 0 σ.1 0 τ.1 + ENNReal.ofReal h * ENNReal.ofReal τ.1 :=
          actionOn_add_const hm hh σ.1 τ.2.le
  · refine le_iInf fun p => ?_
    have h1 : (⨅ τ : {τ : ℝ // 0 < τ},
          (actionPotTau m x y τ.1 + ENNReal.ofReal h * ENNReal.ofReal τ.1))
        ≤ actionPotTau m x y p.1.1 + ENNReal.ofReal h * ENNReal.ofReal p.1.1 :=
      iInf_le (f := fun τ : {τ : ℝ // 0 < τ} =>
        (actionPotTau m x y τ.1 + ENNReal.ofReal h * ENNReal.ofReal τ.1)) ⟨p.1.1, p.2.1⟩
    have h2 : actionPotTau m x y p.1.1 ≤ actionOn m 0 p.1.2 0 p.1.1 :=
      actionPotTau_le_of (m := m) (x := x) (y := y) (τ := p.1.1) (γ := p.1.2)
        p.2.2.1 p.2.2.2.1 p.2.2.2.2
    calc (⨅ τ : {τ : ℝ // 0 < τ},
          (actionPotTau m x y τ.1 + ENNReal.ofReal h * ENNReal.ofReal τ.1))
        ≤ actionPotTau m x y p.1.1 + ENNReal.ofReal h * ENNReal.ofReal p.1.1 := h1
      _ ≤ actionOn m 0 p.1.2 0 p.1.1 + ENNReal.ofReal h * ENNReal.ofReal p.1.1 :=
          add_le_add h2 le_rfl
      _ = actionOn m h p.1.2 0 p.1.1 := (actionOn_add_const hm hh p.1.2 p.2.1.le).symm

end Submission.NBody
