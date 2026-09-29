import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.genEigen_reflectPhase
import Submission.Work.TMC16Core.Basic.expDecay_of_oneSided

/-!
# Exponential localisation from one-sided exponential localisation (TMC16, assembly)

`ExpLocAEpos α lam` asserts, for almost every phase `θ`, that *every* generalized
eigenfunction of the almost Mathieu operator `H(α, lam, θ)` decays exponentially
on the *positive* half-line.

The almost Mathieu operator has a reflection symmetry around the phase: if `u`
solves `H(α, lam, θ) u = E u` then `v n = u (-n)` solves `H(α, lam, -θ) v = E v`.
Indeed `amoPot α lam (-θ) n = 2 λ cos (2π(-θ + nα)) = 2 λ cos (2π(θ + (-n)α))
= amoPot α lam θ (-n)` because `cos` is even; the polynomial growth bound and
non-triviality are plainly preserved (`|-n| = |n|`).

Consequently, outside the union of the null set where `ExpLocAEpos` fails and its
image under `θ ↦ -θ` (still null, negation preserves Lebesgue measure), both
`ExpLocAEpos` *and* its reflected version hold.  Applying the reflected version to
`v n = u (-n)` turns the negative half-line decay of `u` into positive half-line
decay of `v`, i.e. into decay of `u` to the left.  Together with the decay to the
right this gives full two-sided exponential decay, i.e. `ExpLocAE`.

This file contains only the measure-theoretic assembly; the reflection identity
is `Work.TMC16Core.Basic.genEigen_reflectPhase` and the elementary passage from
one-sided to two-sided bounds is `Work.TMC16Core.Basic.expDecay_of_oneSided`.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMC16Core.Main

theorem expLocAE_of_pos {α lam : ℝ} (h : Work.TMC16Core.ExpLocAEpos α lam) :
    Work.TMC16Core.ExpLocAE α lam := by
  -- Step 1.  Transport the almost-everywhere statement along the measure preserving
  -- reflection `θ ↦ -θ` of the phase circle.
  have hneg : ∀ᵐ θ ∂(volume : Measure ℝ), ∀ (E : ℝ) (u : ℤ → ℂ),
      Work.TMC16Core.IsGenEigen α lam (-θ) E u →
        ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ k : ℤ, 0 ≤ k →
          ‖u k‖ ≤ C * Real.exp (-(c * (k : ℝ))) :=
    (MeasureTheory.Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h
  -- Step 2.  For a.e. phase both the phase itself and its reflection are good.
  filter_upwards [h, hneg] with θ hP hPneg E u hu
  -- Step 3.  Decay to the right for `u` itself.
  obtain ⟨c₁, hc₁, C₁, hC₁⟩ := hP E u hu
  -- Step 4.  Decay to the left: reflect `u`, obtaining a generalized eigenfunction
  -- at the phase `-θ`, and use the positivity of `ExpLocAEpos` there.
  obtain ⟨c₂, hc₂, C₂, hC₂⟩ :=
    hPneg E (fun n => u (-n)) (Work.TMC16Core.Basic.genEigen_reflectPhase hu)
  -- Step 5.  Combine the two one-sided bounds into `ExpDecay u`.
  refine Work.TMC16Core.Basic.expDecay_of_oneSided (C₂ := C₂) hc₁ hc₂ hC₁ ?_
  intro k hk
  have hcast : ((-k : ℤ) : ℝ) = |(k : ℝ)| := by
    rw [Int.cast_neg, abs_of_nonpos]
    exact_mod_cast hk
  have h1 : ‖u k‖ ≤ C₂ * Real.exp (-(c₂ * ((-k : ℤ) : ℝ))) := by
    have h2 := hC₂ (-k) (by omega)
    simpa using h2
  rwa [hcast] at h1

end Work.TMC16Core.Main
