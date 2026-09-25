import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_defs

/-!
# The four analytic inputs of the Cesàro (`P = X`) lacunary oscillation inequality

This file packages, as plain `Prop`-valued definitions, the conclusions of the four lemmas the
assembly of `cesaro_mult_oscZ` consumes:

* `WgtCut ρ C` — the block oscillation of a *weighted* shifted sharp cut family `r·1_{θ ≤ sρ^{-i}}`
  (uniform in the shift `s`), constant `C`;
* `TScale ρ C` — the same for the cut radii `t/⌊ρ^i⌋` that actually occur in the profile;
* `DilProfile ρ C` — the block oscillation of the weighted dilation family `r · H(⌊ρ^i⌋·θ)` for a
  fixed profile `H` split as `H = H₁ + H₂` into a Stieltjes part (`Hd`) and a square-summable tail;
* `ProfileData ρ` — the two analytic facts about the Cesàro profile `cesH`: the Stieltjes
  representation of `cesH1` with density `cesHd`, and the uniform square-summability of `cesH2`
  along the lacunary scales.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The weighted shifted-cut block oscillation, with constant `C₁` (uniform in the shift `s`). -/
def WgtCut (ρ : ℝ) (C₁ : ℝ) : Prop :=
  ∀ (s : ℝ), 0 < s → ∀ (r : ℝ → ℂ), Measurable r → ∀ (cap : ℝ), 0 ≤ cap →
    (∀ θ, ‖r θ‖ ≤ cap) →
    ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
    ∀ (f : ℤ → ℂ) (T : Finset ℤ), (∀ n, n ∉ T → f n = 0) →
      Work.BourgainPlan.Oscillation.oscZ (fun i x =>
          ∫ θ in (0:ℝ)..1,
            (r θ * (if θ ≤ s * ρ ^ (-(i:ℤ)) then (1:ℂ) else 0)) *
            (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
        ≤ ENNReal.ofReal ((C₁ * cap) ^ 2) *
            ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count

/-- There is a weighted shifted-cut block-oscillation constant. -/
def WgtCutExists (ρ : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ WgtCut ρ C

/-- The weighted cut block oscillation at the physical radii `t / ⌊ρ^i⌋`, constant `C₂`,
uniform in `t ≥ 0`. -/
def TScale (ρ : ℝ) (C₂ : ℝ) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → ∀ (r : ℝ → ℂ), Measurable r → ∀ (cap : ℝ), 0 ≤ cap →
    (∀ θ, ‖r θ‖ ≤ cap) →
    ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
    ∀ (f : ℤ → ℂ) (T : Finset ℤ), (∀ n, n ∉ T → f n = 0) →
      Work.BourgainPlan.Oscillation.oscZ (fun i x =>
          ∫ θ in (0:ℝ)..1,
            (r θ * (if θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)
              then (1:ℂ) else 0)) *
            (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
        ≤ ENNReal.ofReal ((C₂ * cap) ^ 2) *
            ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count

/-- There is a physical-radius cut block-oscillation constant. -/
def TScaleExists (ρ : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ TScale ρ C

/-- The weighted dilation-profile block oscillation, with constant `C₃`; the bound carries the
weight bound `cap` and the profile size `M + A` (Stieltjes density + tail square function). -/
def DilProfile (ρ : ℝ) (C₃ : ℝ) : Prop :=
  ∀ (H H₁ H₂ Hd : ℝ → ℂ), Measurable H → Measurable H₁ → Measurable H₂ → Measurable Hd →
  ∀ (A M : ℝ), 0 ≤ A → 0 ≤ M →
    (∀ u : ℝ, H u = H₁ u + H₂ u) →
    (∀ u : ℝ, 0 < u → H₁ u = -∫ t in (0:ℝ)..1, Hd t * (if u ≤ t then (1:ℂ) else 0)) →
    (∀ t ∈ Set.Ioc (0:ℝ) 1, ‖Hd t‖ ≤ M) →
    (∀ θ ∈ Set.Ioc (0:ℝ) 1,
      Summable (fun i : ℕ => ‖H₂ ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2) ∧
      ∑' i : ℕ, ‖H₂ ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2 ≤ A ^ 2) →
    ∀ (r : ℝ → ℂ), Measurable r → ∀ (cap : ℝ), 0 ≤ cap → (∀ θ, ‖r θ‖ ≤ cap) →
    ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
    ∀ (f : ℤ → ℂ) (T : Finset ℤ), (∀ n, n ∉ T → f n = 0) →
      Work.BourgainPlan.Oscillation.oscZ (fun i x =>
          ∫ θ in (0:ℝ)..1,
            (r θ * H ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)) *
            (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
        ≤ ENNReal.ofReal ((C₃ * cap * (M + A)) ^ 2) *
            ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count

/-- There is a weighted dilation-profile block-oscillation constant. -/
def DilProfileExists (ρ : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ DilProfile ρ C

/-- The two analytic facts about the Cesàro profile: the Stieltjes representation of its `u ≤ 1`
part with density `cesHd`, and the uniform square-summability of its tail along `⌊ρ^i⌋`. -/
def ProfileData (ρ : ℝ) : Prop :=
  ∃ A M : ℝ, 0 < A ∧ 0 < M ∧
    (∀ u : ℝ, 0 < u →
      cesH1 u = -∫ t in (0:ℝ)..1, cesHd t * (if u ≤ t then (1:ℂ) else 0)) ∧
    (∀ t ∈ Set.Ioc (0:ℝ) 1, ‖cesHd t‖ ≤ M) ∧
    (∀ θ ∈ Set.Ioc (0:ℝ) 1,
      Summable (fun i : ℕ => ‖cesH2 ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2) ∧
      ∑' i : ℕ, ‖cesH2 ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2 ≤ A ^ 2)

end

end Work.BourgainPlan.Oscillation.Lacunary
