/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StepFacts/DthIter_Jeps_route_theta.lean` — the routed
`θ`-derivative identity

`J_ε = Jeps ρ ε` is the Friedrichs mollifier in the log-coordinates
`s = log z`, `ζ = log tan θ` (`Basic.lean`): on the open quadrant it is the convolution with the
kernel `Jker ρ ε`, and the substitution is the *translation* `(s,ζ) ↦ (s - p₁, ζ - p₂)`.  Hence
`J_ε` commutes with `D_z = ∂_s` and with `D_θ = 2∂_ζ` (`mixed_Jeps.lean`).

This module is one of the `StepFacts` of the `StrongEps` route.  It supplies the identity that
**routes the `D_θ`-derivative onto the kernel**: for every `i ≥ 1`,

  `D_θ^i (J_ε f) = 2 ∫ p, (∂_{p₂} Jker ρ ε) (p) · (D_θ^{i-1} f) (z e^{-p₁}) (thShift θ p₂)`

on the open quadrant, for an `f` of class `C^n` there for every `n`.  The two factors `2` and
`∂_{p₂}` are exactly the derivative of the translation `ζ ↦ ζ - p₂` in the log-coordinate:
since `D_θ = 2 ∂_ζ`, the derivative of the shifted profile in the *shift parameter* `p₂` is
`-(1/2) D_θ` of the profile at the shifted point (`KernAux.deriv_shift_snd`), and one
integration by parts in `p₂` — the kernel `Jker ρ ε` is `C^∞` with compact support, so there
are no boundary terms (`KernAux.integral_mul_partSnd_eq_neg`) — converts the `D_θ` on the
profile into a `∂_{p₂}` on the kernel.

The advantage of the routed form is that the profile now appears only through
`D_θ^{i-1} f`, one order lower, while the whole derivative of the (known, `C^∞`) kernel is
factored out; this is what the weighted bounds of the `E1` chapter are applied to
(`StepFacts/slot_route_bounds.lean` consumes the statement below verbatim).

Everything rests on `[propext, Classical.choice, Quot.sound]` (the imported helper lemmas were
checked to have exactly these axioms).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.KernAux.deriv_shift_snd
import Submission.Work.FTS.StrongEps.KernAux.contDiff_shift
import Submission.Work.FTS.StrongEps.KernAux.integral_mul_partSnd_eq_neg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.StepFacts

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-! ## The pointwise `∂_{p₂} ↔ D_θ` dictionary

Differentiating the shifted profile in the *shift parameter* `p₂` is differentiation of the
profile along `D_θ` at the shifted point, up to the factor `-1/2` (`deriv_shift_snd` of
`KernAux`); reversing the constant gives the form used below. -/

/-- **`D_θ` at the shifted point is `-2 ∂_{p₂}` of the shifted slice.**  For `g` of class `C¹` on
the open quadrant, `z > 0`, `θ ∈ (0,π/2)` and every shift parameter `p`,
`D_θ g (z e^{-p₁}) (thShift θ p₂) = -2 ∂_{p₂} [t ↦ g (z e^{-p₁}) (thShift θ t)]`. -/
theorem Dth_eq_neg_two_deriv_snd {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Quad) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ × ℝ) :
    Work.Spaces.Dth g (zShift z p.1) (thShift θ p.2)
      = -2 * deriv (fun t : ℝ => g (zShift z p.1) (thShift θ t)) p.2 := by
  rw [KernAux.deriv_shift_snd g hz hθ hg p]
  ring

/-- **The iterated form**: for `i ≥ 1`, the value of `D_θ^i g` at the shifted point is `-2` times
the `p₂`-derivative of the shifted `D_θ^{i-1} g`. -/
theorem DthIter_eq_neg_two_deriv_snd {g : ℝ → ℝ → ℝ} (hg : SmQ g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (i : ℕ) (hi : 1 ≤ i) (p : ℝ × ℝ) :
    Work.Spaces.DthIter i g (zShift z p.1) (thShift θ p.2)
      = -2 * deriv (fun t : ℝ => Work.Spaces.DthIter (i - 1) g (zShift z p.1)
          (thShift θ t)) p.2 := by
  -- `D_θ^i g = D_θ (D_θ^{i-1} g)` because `i = (i - 1) + 1`
  have hsucc : Work.Spaces.DthIter i g
      = Work.Spaces.Dth (Work.Spaces.DthIter (i - 1) g) := by
    conv_lhs => rw [← Nat.sub_add_cancel hi]
    rw [Work.Spaces.DthIter_succ]
  rw [hsucc]
  exact Dth_eq_neg_two_deriv_snd ((hg.DthIter (i - 1)).one) hz hθ p

/-! ## The target -/

-- context: namespace Work.FTS.StrongEps.StepFacts; `DthIter i f = D_θ^i f` with `D_θ = sin(2θ)∂_θ`; the conclusion is the single routed θ-derivative identity.
theorem DthIter_Jeps_route_theta (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (i : ℕ) (hi : 1 ≤ i) :
    Work.Spaces.DthIter i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = 2 * ∫ p : ℝ × ℝ,
          deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2
          * Work.Spaces.DthIter (i - 1) f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
  have hsm : SmQ f := smQ_of_forall_nat hf
  -- (1) `J_ε` commutes with `D_θ^i` (`E1`), so the left-hand side is the mollified
  -- `D_θ^i f`, i.e. the `p`-integral of the kernel against the shifted `D_θ^i f`.
  have hmem : (z, θ) ∈ Quad := ⟨hz, hθ⟩
  have h1 : Work.Spaces.DthIter i (Jeps ρ ε f) z θ = Jeps ρ ε (Work.Spaces.DthIter i f) z θ :=
    DthIter_mixed_Jeps ρ hρ.moll hε hf i hmem
  rw [h1, Jeps_eq_integral ρ ε (Work.Spaces.DthIter i f) hz hθ]
  -- (2) pointwise, `D_θ^i f` at the shifted point is `-2 ∂_{p₂}` of the shifted `D_θ^{i-1} f`
  have hpt : ∀ p : ℝ × ℝ, Jker ρ ε p
        * Work.Spaces.DthIter i f (zShift z p.1) (thShift θ p.2)
      = -2 * (Jker ρ ε p * deriv (fun t : ℝ =>
          Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ t)) p.2) := by
    intro p
    rw [DthIter_eq_neg_two_deriv_snd hsm hz hθ i hi p]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
  -- (3) integrate by parts in `p₂`: the kernel is `C^∞` with compact support, the shifted
  -- `D_θ^{i-1} f` is `C¹` (it is the shift of a smooth profile), so there is no boundary term
  have hv : ContDiff ℝ 1 (fun p : ℝ × ℝ => Work.Spaces.DthIter (i - 1) f
      (zShift z p.1) (thShift θ p.2)) :=
    KernAux.contDiff_shift (Work.Spaces.DthIter (i - 1) f) hz hθ
      (contDiffOn_infty.mp (hsm.DthIter (i - 1))) 1
  have hIBP : ∫ p : ℝ × ℝ, Jker ρ ε p * deriv (fun t : ℝ =>
        Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ t)) p.2
      = - ∫ p : ℝ × ℝ, deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2
          * Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2) :=
    KernAux.integral_mul_partSnd_eq_neg (Jker_smooth hρ ε)
      (Jker_hasCompactSupport hρ.moll hε) hv
  rw [hIBP]
  ring

end Work.FTS.StrongEps.StepFacts
