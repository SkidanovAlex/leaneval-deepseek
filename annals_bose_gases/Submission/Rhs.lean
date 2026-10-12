import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import ChallengeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
The Lee--Huang--Yang right-hand side as a function of the density.

For a scattering length `A`, a coefficient `K` (later `𝓒 (𝓡 v) (R / a v)`)
and an exponent `s` (later `1/2 + η`, with `η > 0`), the bound to be proved
eventually in `ρ` is

    lhyRhs A K s ρ := 4πρ²A (1 + (128/(15√π))√(ρA³) − K·(ρA³)^s) .

This module proves the continuity facts that the endgame assembler
(`ThermoLimit.e_ge_of_eventually_box_ge`) needs of its `φ`.  Because
`Real.sqrt` is continuous on all of `ℝ` and the real power `x ↦ x^s` is
continuous on `ℝ` for `s ≥ 0`, the whole map `ρ ↦ lhyRhs A K s ρ` is
continuous everywhere — with no hypothesis on the signs of `A` or `K`.
-/

namespace Submission

open Filter Metric
open scoped Topology Real

set_option autoImplicit false

namespace BoseGases

/-- The Lee--Huang--Yang right-hand side (a lower-bound candidate for `e ρ v`),
parametrized by the scattering length `A`, the coefficient `K` of the error term
and the error exponent `s`. -/
noncomputable def lhyRhs (A K s : ℝ) (ρ : ℝ) : ℝ :=
  4 * π * ρ ^ 2 * A *
    (1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - K * (ρ * A ^ 3) ^ s)

/-- With vanishing scattering length the right-hand side vanishes identically
(the prefactor `4πρ²A` is zero). -/
lemma lhyRhs_eq_zero_of_A_eq_zero (K s ρ : ℝ) : lhyRhs 0 K s ρ = 0 := by
  dsimp [lhyRhs]
  ring

/-- `ρ ↦ √(ρ·A³)` is continuous at every point (the base is continuous and
`Real.sqrt` is continuous everywhere). -/
lemma continuousAt_sqrt_base {A : ℝ} {ρ₀ : ℝ} :
    ContinuousAt (fun ρ : ℝ => √(ρ * A ^ 3)) ρ₀ := by
  have hb : ContinuousAt (fun ρ : ℝ => ρ * A ^ 3) ρ₀ :=
    (continuousAt_id.mul (continuousAt_const : ContinuousAt (fun _ : ℝ => A ^ 3) ρ₀))
  exact hb.sqrt

/-- `ρ ↦ (ρ·A³)^s` is continuous at every point when `s ≥ 0` (the real power
`x ↦ x^s` is continuous on `ℝ` for nonnegative exponent). -/
lemma continuousAt_rpow_base {A s : ℝ} {ρ₀ : ℝ} (hs : 0 ≤ s) :
    ContinuousAt (fun ρ : ℝ => (ρ * A ^ 3) ^ s) ρ₀ := by
  have hb : ContinuousAt (fun ρ : ℝ => ρ * A ^ 3) ρ₀ :=
    (continuousAt_id.mul (continuousAt_const : ContinuousAt (fun _ : ℝ => A ^ 3) ρ₀))
  exact hb.rpow_const (.inr hs)

/-- The right-hand side is continuous everywhere for a nonnegative error
exponent. -/
lemma lhyRhs_continuousAt {A K s : ℝ} {ρ₀ : ℝ} (hs : 0 ≤ s) :
    ContinuousAt (lhyRhs A K s) ρ₀ := by
  have hid : ContinuousAt (fun ρ : ℝ => ρ) ρ₀ := continuousAt_id
  have hρ2 : ContinuousAt (fun ρ : ℝ => ρ ^ 2) ρ₀ := hid.pow 2
  have hsq : ContinuousAt (fun ρ : ℝ => √(ρ * A ^ 3)) ρ₀ := by
    have hb : ContinuousAt (fun ρ : ℝ => ρ * A ^ 3) ρ₀ :=
      (hid.mul (continuousAt_const : ContinuousAt (fun _ : ℝ => A ^ 3) ρ₀))
    exact hb.sqrt
  have hrp : ContinuousAt (fun ρ : ℝ => (ρ * A ^ 3) ^ s) ρ₀ := by
    have hb : ContinuousAt (fun ρ : ℝ => ρ * A ^ 3) ρ₀ :=
      (hid.mul (continuousAt_const : ContinuousAt (fun _ : ℝ => A ^ 3) ρ₀))
    exact hb.rpow_const (.inr hs)
  have hinner : ContinuousAt (fun ρ : ℝ =>
      1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - K * (ρ * A ^ 3) ^ s) ρ₀ := by
    have h2 : ContinuousAt (fun ρ : ℝ => (128 / (15 * √π)) * √(ρ * A ^ 3)) ρ₀ :=
      continuousAt_const.mul hsq
    have h3 : ContinuousAt (fun ρ : ℝ => K * (ρ * A ^ 3) ^ s) ρ₀ :=
      continuousAt_const.mul hrp
    exact (continuousAt_const.add h2).sub h3
  have hpre : ContinuousAt (fun ρ : ℝ => 4 * π * ρ ^ 2 * A) ρ₀ := by
    have hc : ContinuousAt (fun _ : ℝ => (4 : ℝ) * π) ρ₀ := continuousAt_const
    have hA' : ContinuousAt (fun _ : ℝ => A) ρ₀ := continuousAt_const
    exact ((hc.mul hρ2).mul hA')
  change ContinuousAt (fun ρ : ℝ =>
    4 * π * ρ ^ 2 * A * (1 + (128 / (15 * √π)) * √(ρ * A ^ 3) - K * (ρ * A ^ 3) ^ s)) ρ₀
  exact hpre.mul hinner

/-- Eventual form used by `ThermoLimit.e_ge_of_eventually_box_ge`: for a fixed
nonnegative error exponent the right-hand side is continuous at every small
density. -/
lemma lhyRhs_eventually_continuousAt {A K s : ℝ} (hs : 0 ≤ s) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ContinuousAt (lhyRhs A K s) ρ := by
  filter_upwards [self_mem_nhdsWithin] with ρ hρpos
  exact lhyRhs_continuousAt hs

end BoseGases

end Submission
