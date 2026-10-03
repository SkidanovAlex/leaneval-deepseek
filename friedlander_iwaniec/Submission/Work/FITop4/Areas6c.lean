import Mathlib
import Submission.Work.FITop4.Areas6
import Submission.Work.FITop4.Red5.Vocab

/-!
# `Area7₆ᵇ`: the repaired area 7 of round 6 (the lead, 2026-09-29)

`Area7_6` (in `Areas6.lean`, frozen) keeps FI's divisor condition (5.9) `τ(|z|²) ≤ Pa.τ` and the
axis cut `IsAxisFree` inside `β` at the per-character level, at `X⁻¹` quality with
`X ≤ (log N)^nuU`. FI drop (5.9) at (10.4), inside the `D₀` error budget, and never meet a
pointwise axis cut in §17–§23. With an arbitrary `Pa.τ`, the τ-complement cannot be removed at
that quality by FI's tools. See `Submission/Work/FIArea7/AREA7_ROUTE_LEAD.md` §0.

`Area7_6b` adds two hypotheses that the composition supplies:
* `Pa.τ = tauOf Pa.x Asave` (recorded for every piece in `FIRed6Axis/Statement.lean`);
* every polar-box point is axis-free (from `FarPiece`, lemma `farPiece_isAxisFree`).
Everything else is `Area7_6` verbatim.
-/

namespace Work.FITop4

open Finset
open scoped BigOperators

noncomputable section

/-- **`Area7₆ᵇ`**: `Area7_6` with `Pa.τ` pinned and the polar box axis-free. -/
def Area7_6b : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ δ c x0 : ℝ, 0 < δ ∧ 0 < c ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
    Pa.τ = tauOf Pa.x Asave →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    IsBetaCoeff6 Pa φ z0 β →
    (∀ z, InPolarBox Pa φ z → IsAxisFree Pa z) →
    1 ≤ X → (X : ℝ) < Pa.N ^ δ →
      (X : ℝ) ≤ (Real.log Pa.N) ^ nuU →
    ‖Wcut (radN Pa) X β + Bcut (radN Pa) X β‖
      ≤ c * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N

/-- `Area7_6` implies `Area7_6b` (sanity: the amendment only weakens). -/
theorem area7_6b_of_area7_6 (h : Area7_6) : Area7_6b := by
  intro η hη hη2
  obtain ⟨δ, c, x0, hδ, hc, H⟩ := h η hη hη2
  exact ⟨δ, c, x0, hδ, hc, fun Pa hx hPa _ X φ z0 β hb _ h1 h2 h3 => H Pa hx hPa X φ z0 β hb h1 h2 h3⟩


/-- **`Area6₆ᶜ`**: `Area6_6` with `Pa.τ` pinned and the polar box axis-free (the lead, 2026-09-29).
Same defect as `Area7_6`: §16 bounds only the clean support; the τ-excess
`{NoSmallPrimes ∧ τ(|z|²) > Pa.τ}` of `IsBetaCoeff6` must be paid at `X⁻¹` quality, which needs the
paper's fixed `τ = tauOf x A` (owner H1685: `S16CompTwo` in `FIArea6/S16TwoDefs.lean`). -/
def Area6_6c : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ cν x0 : ℝ, 0 < cν ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
    Pa.τ = tauOf Pa.x Asave →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    IsBetaCoeff6 Pa φ z0 β →
    (∀ z, InPolarBox Pa φ z → IsAxisFree Pa z) →
    1 ≤ X → (X : ℝ) ≤ (Real.log Pa.N) ^ nuU →
      (X : ℝ) ^ 3 ≤ Real.exp (Real.sqrt (Real.log Pa.N)) →
    ‖Ucut (radN Pa) X β‖
      ≤ cν * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N

/-- `Area6_6` implies `Area6_6c` (sanity: the amendment only weakens). -/
theorem area6_6c_of_area6_6 (h : Area6_6) : Area6_6c := by
  intro η hη hη2
  obtain ⟨cν, x0, hc, H⟩ := h η hη hη2
  exact ⟨cν, x0, hc, fun Pa hx hPa _ X φ z0 β hb _ h1 h2 h3 => H Pa hx hPa X φ z0 β hb h1 h2 h3⟩

end

end Work.FITop4
