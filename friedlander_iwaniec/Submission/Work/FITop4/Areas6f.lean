/-
# FITop4 — Areas6f.lean (LEAD-OWNED, FROZEN 2026-10-02, curric-46)

Area 4 with θ/τ pinned, axis-free polar box and (log N)^2 ≤ X (all available at the composition's
only call site). Design: FIArea4/AREA4_ENGINES_LEAD.md §3.1.
-/
import Mathlib
import Submission.Work.FITop4.Areas6c

namespace Work.FITop4
open Finset
open scoped BigOperators
noncomputable section

attribute [local instance] Classical.propDecidable

/-- **`Area4₆ᶜ`**: `Area4_6` with θ and τ pinned, the polar box axis-free, and `(log N)² ≤ X`.
All four are available at the composition's only call site (`hθ_eq`, `hτ_eq`,
`FarPiece_isAxisFree`, and `X = Xcut = ⌈(log N)^{3σ+3}⌉`). -/
def Area4_6c : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ c x0 : ℝ, 0 < c ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
    Pa.θ = thetaOf Pa.x Asave → Pa.τ = tauOf Pa.x Asave →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    IsBetaCoeff6 Pa φ z0 β →
    (∀ z, InPolarBox Pa φ z → IsAxisFree Pa z) →
    1 ≤ X → (Real.log Pa.N) ^ (2 : ℕ) ≤ (X : ℝ) →
    (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) → (X : ℝ) ≤ (Real.log Pa.N) ^ nuU →
    ‖Vcut (radN Pa) X β‖ ≤ c * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3)) * Pa.N ^ 2

theorem area4_6c_of_area4_6 (h : Area4_6) : Area4_6c := by
  intro η h0 h1; obtain ⟨c, x0, hc, H⟩ := h η h0 h1
  exact ⟨c, x0, hc, fun Pa hx hη _ _ X φ z0 β hb _ h1 _ h9 hν => H Pa hx hη X φ z0 β hb h1 h9 hν⟩

end

end Work.FITop4
