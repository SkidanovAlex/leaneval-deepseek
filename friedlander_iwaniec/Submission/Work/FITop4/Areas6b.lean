import Mathlib
import Submission.Work.FITop4.Areas6

/-!
# `Area2₆ᵇ` — the repaired area 2 of round 6 (the lead, 2026-09-27)

`Area2_6` (in `Areas6.lean`, frozen) is strictly stronger than *FI* (9.10): its `D0` already
carries the (7.10) replacement of the Fourier integral `F₀` of (6.11) by its main term, which the
paper only makes at the start of §10 (p. 984). The replacement error summed over the polar box is
`≍ τ²τ(Δ)³θ⁶M^{1/2}N^{3/2}log N`; the paper bounds it inside the (10.4)/(10.10) error
`(τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^20}`, and it can exceed the frozen `Area2_6` right-hand
side by a factor `≍ x^{1/4-η}` (report `lemma-FIArea2_area2_6d.md`, agent H2145).

`Area2_6b` adds exactly that error, in the SAME shape as the right-hand side of `Area3_6`, so that
in the composition it is absorbed by enlarging `C3`:
`‖D* − cMain6·T‖ ≤ Cb·ϑ⁻¹τ²N²(log N)^b + (C3 + C3')·(τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^20}`.
Everything else is `Area2_6` verbatim.
-/

namespace Work.FITop4

noncomputable section

/-- **`Area2₆ᵇ`**: (9.10) plus the (7.10)/(10.4) replacement error. -/
def Area2_6b : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ Cb C3 x0 : ℝ, 0 < Cb ∧ 0 < C3 ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (f : ℤ → ℝ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ),
    IsMajorant6 Pa f → IsBetaCoeff6 Pa φ z0 β →
    ‖Dstar Pa f β - D0 (radN Pa) (Fhat Pa f) β‖
      ≤ Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2 * (Real.log Pa.N) ^ (bFun Pa.η)
        + C3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))

end

end Work.FITop4
