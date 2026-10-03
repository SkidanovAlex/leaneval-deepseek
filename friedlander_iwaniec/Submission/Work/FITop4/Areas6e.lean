/-
# FITop4 — Areas6e.lean (LEAD-OWNED, FROZEN 2026-10-02, curric-46)

Area 6 for the CLEAN coefficient class (FI §16 = (5.7)+(5.8) only) and the (5.9) τ-removal
step paid in the composition (FI (10.4)/Lemma 10.1). Design: FIArea6/AREA6_CONTRACT_LEAD.md.
Supersedes Area6_6c (over-strength τ clause).
-/
import Mathlib
import Submission.Work.FITop4.Areas6c

namespace Work.FITop4
open Finset
open scoped BigOperators
noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The clean coefficient of FI Prop. 10.2 / Lemma 16.2 / Prop. 16.3**: (4.13)+(5.13) restricted
by (5.7) and (5.8) only.  This is `IsBetaCoeff6` with the (5.9) clause `τ(|z|²) ≤ Pa.τ` and the
`IsAxisFree` clause deleted (FI p. 985: "from now on the condition τ(|z|²) ≤ τ no longer exists"). -/
def IsCleanCoeff6 (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) : Prop :=
  ∃ q p : ℝ → ℝ,
    ContDiff ℝ 2 q ∧ ContDiff ℝ 2 p ∧
    (∀ α, 0 ≤ q α) ∧ (∀ α, q α ≤ 1) ∧
    (∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ) ∧
    (∀ j : ℕ, j ≤ 2 → ∀ α : ℝ, |iteratedDeriv j q α| ≤ cMoll j * Pa.θ ^ (-(j : ℝ))) ∧
    (∀ u, 0 ≤ p u) ∧ (∀ u, p u ≤ 1) ∧
    (∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) ∧
    (∀ j : ℕ, j ≤ 2 → ∀ u : ℝ,
      |iteratedDeriv j p u| ≤ cMoll j * (Pa.θ * Pa.N) ^ (-(j : ℝ))) ∧
    (∀ z : GaussianInt, β z =
      (if InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧ SameClass8 z z0
       then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
       else 0))

/-- The (5.9) truncation `β ↦ β·1[τ(|z|²) ≤ Pa.τ]` (FI (4.9)–(4.11)). -/
def tauCut (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (z : GaussianInt) : ℂ :=
  if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then β z else 0

/-- **`Area6₆ᵉ`** (FI §16, Prop. 16.3 = (16.41)) for the coefficient FI's §16 actually treats.
Round-6.2 shape (η-dependent constant, threshold, `ν = nuU`, the `X³ ≤ exp√log N` proviso) and the
axis-free polar box that the composition supplies (`FarPiece_isAxisFree`).  No τ pin: the clean
class has no τ. -/
def Area6_6e : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ cν x0 : ℝ, 0 < cν ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    IsCleanCoeff6 Pa φ z0 β →
    (∀ z, InPolarBox Pa φ z → IsAxisFree Pa z) →
    1 ≤ X → (X : ℝ) ≤ (Real.log Pa.N) ^ nuU →
      (X : ℝ) ^ 3 ≤ Real.exp (Real.sqrt (Real.log Pa.N)) →
    ‖Ucut (Work.FITop.radN Pa) X β‖
      ≤ cν * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N

/-- **`TauRemoval6`** — FI (10.4)'s waiver of (5.9), for any bounded cut of the (10.13) expansion,
at the pinned τ.  Applied with the U-cut it is the only τ-removal the composition needs. -/
def TauRemoval6 : Prop :=
  ∃ C x0 : ℝ, 0 < C ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.τ = tauOf Pa.x Asave →
  ∀ (cut : GaussianInt → GaussianInt → ℕ → ℝ), (∀ z1 z2 d, |cut z1 z2 d| ≤ 1) →
  ∀ (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ), IsCleanCoeff6 Pa φ z0 β →
    ‖Tcut (Work.FITop.radN Pa) cut (tauCut Pa β) - Tcut (Work.FITop.radN Pa) cut β‖
      ≤ C * Pa.N ^ 2 * (Real.log Pa.N) ^ (-(19 * 10 ^ 8 : ℝ))

end

end Work.FITop4
