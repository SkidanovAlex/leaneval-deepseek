import Mathlib
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.sweepFamOf_close

/-!
# Far separation of the double bump-blur of a Lipschitz loop family

`Work.Drive.sweepFamOf Γ δ₁ δ₂ σ` is the double blur of `Γ`.  If `Γ` is (jointly continuous and)
Lipschitz in the loop parameter with constant `M` and in the sweep parameter with constant `N`, and
if the *raw* slices of `Γ` are separated at scale `η` — `ρ₀ ≤ ‖Γ σ t₁ - Γ σ t₂‖` whenever the two
loop parameters are at distance between `η` and `period - η` — then the blurred slices are separated
(by `ρ₀/2`) as soon as the blur widths are small:

    δ₁, δ₂ ≤ L  ⟹  ‖sweepFamOf Γ δ₁ δ₂ σ t₁ - sweepFamOf Γ δ₁ δ₂ σ t₂‖ ≥ ρ₀/2 .

This is the `Γ`-generic form of `Work.Drive.sweepFamFarSep` (which is stated for the ordinary
chamfered sweep loop and is proved by the profile argument); here the only inputs are the
`C⁰`-closeness of the blur to `Γ` (`Work.Drive.sweepFamOf_close`) and a three-term triangle
inequality.  In the `S` lane the raw separation is supplied by `Work.Drive.farSep_window_of_injOn`
from the per-slice injectivity of `Γ` (`Work.Drive.chamferLoopGenInjOnScheduled`).
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory

open scoped Real Topology intervalIntegral

/-- **Far separation of the double blur.** -/
theorem sweepFamOf_farSep {Γ : ℝ → ℝ → Space}
    (hΓ : Continuous (fun p : ℝ × ℝ => Γ p.1 p.2))
    {M N : ℝ} (hMnn : 0 ≤ M) (hNnn : 0 ≤ N)
    (hM : ∀ s t₁ t₂ : ℝ, ‖Γ s t₁ - Γ s t₂‖ ≤ M * |t₂ - t₁|)
    (hN : ∀ s₁ s₂ t : ℝ, ‖Γ s₁ t - Γ s₂ t‖ ≤ N * |s₂ - s₁|)
    {η ρ₀ : ℝ} (hη : 0 < η) (hρ₀ : 0 < ρ₀)
    (hsep : ∀ s t₁ t₂ : ℝ, η ≤ |t₂ - t₁| → |t₂ - t₁| ≤ period - η →
      ρ₀ ≤ ‖Γ s t₁ - Γ s t₂‖) :
    ∃ L ρ : ℝ, 0 < L ∧ 0 < ρ ∧ ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
      ∀ s t₁ t₂ : ℝ, η ≤ |t₂ - t₁| → |t₂ - t₁| ≤ period - η →
        ρ ≤ ‖sweepFamOf Γ δ₁ δ₂ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₂‖ := by
  obtain ⟨L, hLpos, hclose⟩ :=
    sweepFamOf_close Γ hΓ hMnn hNnn hM hN (ε := ρ₀ / 4) (by positivity)
  refine ⟨L, ρ₀ / 2, hLpos, by positivity, ?_⟩
  intro δ₁ δ₂ hδ₁ hδ₁L hδ₂ hδ₂L s t₁ t₂ hη₁ hη₂
  have h1 : ‖sweepFamOf Γ δ₁ δ₂ s t₁ - Γ s t₁‖ ≤ ρ₀ / 4 :=
    hclose δ₁ δ₂ hδ₁.le hδ₁L hδ₂.le hδ₂L s t₁
  have h2 : ‖sweepFamOf Γ δ₁ δ₂ s t₂ - Γ s t₂‖ ≤ ρ₀ / 4 :=
    hclose δ₁ δ₂ hδ₁.le hδ₁L hδ₂.le hδ₂L s t₂
  have h3 : ρ₀ ≤ ‖Γ s t₁ - Γ s t₂‖ := hsep s t₁ t₂ hη₁ hη₂
  have h4 : ‖Γ s t₁ - Γ s t₂‖ ≤ ‖sweepFamOf Γ δ₁ δ₂ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₂‖
      + ρ₀ / 4 + ρ₀ / 4 := by
    have hsplit : Γ s t₁ - Γ s t₂
        = (Γ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₁)
          + (sweepFamOf Γ δ₁ δ₂ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₂)
          + (sweepFamOf Γ δ₁ δ₂ s t₂ - Γ s t₂) := by abel
    rw [hsplit]
    have h5 := norm_add_le ((Γ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₁)
      + (sweepFamOf Γ δ₁ δ₂ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₂))
      (sweepFamOf Γ δ₁ δ₂ s t₂ - Γ s t₂)
    have h6 := norm_add_le (Γ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₁)
      (sweepFamOf Γ δ₁ δ₂ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₂)
    have h7 : ‖Γ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₁‖ ≤ ρ₀ / 4 := by
      rw [norm_sub_rev]; exact h1
    have h8 : ‖sweepFamOf Γ δ₁ δ₂ s t₂ - Γ s t₂‖ ≤ ρ₀ / 4 := h2
    linarith
  linarith


/-- **Far separation of the double blur on a compact window, from an abstract `C⁰`-closeness
bound.**  The geometric input (`Γ`'s raw slices are separated at scale `η` on the window) and the
analytic input (the blur is within `ρ₀/4` of `Γ` on the window) are kept separate, because for a
*scheduled* loop `Γ` the `σ`-regularity of the loop is not available (`Work.Drive.SweepData` lifts
are only continuous, so no `σ`-Lipschitz constant exists); there the closeness is supplied by a
*uniform-continuity* argument on the compact window instead
(`Work.Drive.sweepFamOf_close_uc`). -/
theorem sweepFamOf_farSep_of_close {Γ : ℝ → ℝ → Space} {η ρ₀ : ℝ} (hη : 0 < η) (hρ₀ : 0 < ρ₀)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hsep : ∀ s ∈ Set.Icc a b, ∀ t₁ t₂ : ℝ, η ≤ |t₂ - t₁| → |t₂ - t₁| ≤ period - η →
      ρ₀ ≤ ‖Γ s t₁ - Γ s t₂‖)
    (hclose : ∃ L : ℝ, 0 < L ∧ ∀ δ₁ δ₂ : ℝ, 0 ≤ δ₁ → δ₁ ≤ L → 0 ≤ δ₂ → δ₂ ≤ L →
      ∀ s ∈ Set.Icc a b, ∀ t : ℝ, ‖sweepFamOf Γ δ₁ δ₂ s t - Γ s t‖ ≤ ρ₀ / 4) :
    ∃ L ρ : ℝ, 0 < L ∧ 0 < ρ ∧ ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
      ∀ s ∈ Set.Icc a b, ∀ t₁ t₂ : ℝ, η ≤ |t₂ - t₁| → |t₂ - t₁| ≤ period - η →
        ρ ≤ ‖sweepFamOf Γ δ₁ δ₂ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₂‖ := by
  obtain ⟨L, hLpos, hcl⟩ := hclose
  refine ⟨L, ρ₀ / 2, hLpos, by positivity, ?_⟩
  intro δ₁ δ₂ hδ₁ hδ₁L hδ₂ hδ₂L s hs t₁ t₂ hη₁ hη₂
  have h1 : ‖sweepFamOf Γ δ₁ δ₂ s t₁ - Γ s t₁‖ ≤ ρ₀ / 4 :=
    hcl δ₁ δ₂ hδ₁.le hδ₁L hδ₂.le hδ₂L s hs t₁
  have h2 : ‖sweepFamOf Γ δ₁ δ₂ s t₂ - Γ s t₂‖ ≤ ρ₀ / 4 :=
    hcl δ₁ δ₂ hδ₁.le hδ₁L hδ₂.le hδ₂L s hs t₂
  have h3 : ρ₀ ≤ ‖Γ s t₁ - Γ s t₂‖ := hsep s hs t₁ t₂ hη₁ hη₂
  have h4 : ‖Γ s t₁ - Γ s t₂‖ ≤ ‖sweepFamOf Γ δ₁ δ₂ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₂‖
      + ρ₀ / 4 + ρ₀ / 4 := by
    have hsplit : Γ s t₁ - Γ s t₂
        = (Γ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₁)
          + (sweepFamOf Γ δ₁ δ₂ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₂)
          + (sweepFamOf Γ δ₁ δ₂ s t₂ - Γ s t₂) := by abel
    rw [hsplit]
    have h5 := norm_add_le ((Γ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₁)
      + (sweepFamOf Γ δ₁ δ₂ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₂))
      (sweepFamOf Γ δ₁ δ₂ s t₂ - Γ s t₂)
    have h6 := norm_add_le (Γ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₁)
      (sweepFamOf Γ δ₁ δ₂ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₂)
    have h7 : ‖Γ s t₁ - sweepFamOf Γ δ₁ δ₂ s t₁‖ ≤ ρ₀ / 4 := by
      rw [norm_sub_rev]; exact h1
    linarith
  linarith

end Work.Drive
