import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.far_part_defs
import Submission.Work.GM.Affine.fine_setup

/-!
# GM §9, region II: vocabulary for the *far* part in the "`∫(Hprof)²`" form

The far part of `ĝ` is `ghatFar = ghat - ghatRes`, and by the Poisson expansion

`ghatFar(ξ) = Σ_{m₁∈R1 M₁} (1/|m₁|) Bsum f M₂ (ξ/m₁) · Wfar K M₃ (ξ/m₁)`,

where `Wfar K M₃ x = M₃ Σ_{ℓ : |ℓ-x| > 2/M₃} ψ̂₁(M₃(ℓ-x))` (this is `Work.GM.Affine.Wfar`
from `FarMass_defs`).

The estimates here use the following decomposition of `Wfar`:

* `WfarTrunc K M₃ J x = M₃ Σ_{ℓ : 2/M₃ < |ℓ-x| ≤ J/M₃} ψ̂₁(M₃(ℓ-x))` — the *truncated* weight,
  whose lattice sum is a finite sum (for `|x| ≤ T⁶` and `J ≥ 0`, only `|ℓ| ≤ ⌈T⁶⌉+⌈J⌉` can
  contribute);
* `WfarTail K M₃ J x = M₃ Σ_{ℓ : |ℓ-x| > J/M₃} ψ̂₁(M₃(ℓ-x))` — the tail, which is *uniformly*
  small in `x` and `M₃` by the decay of `ψ̂₁`.

The truncated part is estimated by Cauchy–Schwarz over the pairs `p = (m₁,ℓ)` with `m₁ ∈ R1 M₁`
and `ℓ` in the range `farPairs M₁ T J`, giving the majorant `farMaj`; at a fixed `ξ` only the
pairs of `farSel M₃ T J ξ` contribute, and their number is controlled by the divisor bound.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The truncated far weight `M₃ Σ_{ℓ : 2/M₃ < |ℓ-x| ≤ J/M₃} ψ̂₁(M₃(ℓ-x))`. -/
def WfarTrunc (K M₃ J x : ℝ) : ℂ :=
  (M₃ : ℂ) * ∑' ℓ : ℤ,
    if 2 / M₃ < |(ℓ : ℝ) - x| ∧ |(ℓ : ℝ) - x| ≤ J / M₃ then
      psi1hat K (M₃ * ((ℓ : ℝ) - x)) else 0

/-- The tail of the far weight `M₃ Σ_{ℓ : |ℓ-x| > J/M₃} ψ̂₁(M₃(ℓ-x))`. -/
def WfarTail (K M₃ J x : ℝ) : ℂ :=
  (M₃ : ℂ) * ∑' ℓ : ℤ,
    if J / M₃ < |(ℓ : ℝ) - x| then psi1hat K (M₃ * ((ℓ : ℝ) - x)) else 0

/-- The candidate pairs `(m₁,ℓ)` for the truncated far part at `|ξ| ≤ T⁶`. -/
def farPairs (M₁ T J : ℝ) : Finset (ℤ × ℤ) :=
  (R1 M₁).product (Finset.Icc (-(⌈T ^ 6⌉ + ⌈J⌉ + 2)) (⌈T ^ 6⌉ + ⌈J⌉ + 2))

/-- The pairs of `farPairs` that contribute at `ξ` (the truncated far window). -/
def farSel (M₁ M₃ T J : ℝ) (ξ : ℝ) : Finset (ℤ × ℤ) :=
  (farPairs M₁ T J).filter (fun p =>
    2 / M₃ < |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ∧ |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ J / M₃)

/-- The Cauchy–Schwarz majorant of the truncated far part. -/
def farMaj (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (T J : ℝ) (ξ : ℝ) : ℝ :=
  ∑ p ∈ farPairs M₁ T J, (1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2 *
    ‖psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ)))‖ ^ 2

/-- The truncated far sum, written as a finite sum over the candidate pairs. -/
def ghatFarT (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (T J : ℝ) (ξ : ℝ) : ℂ :=
  ∑ p ∈ farPairs M₁ T J, (M₃ / |(p.1 : ℝ)|) * psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ))) *
    Bsum f M₂ (ξ / (p.1 : ℝ))

/-- The truncated far sum restricted to the pairs that contribute at `ξ`. -/
def ghatFarSel (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (T J : ℝ) (ξ : ℝ) : ℂ :=
  ∑ p ∈ farSel M₁ M₃ T J ξ, (M₃ / |(p.1 : ℝ)|) *
    psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ))) * Bsum f M₂ (ξ / (p.1 : ℝ))

/-- The window-part `L²` bound of GM §9 region II, as a `Prop` so that it can be passed as a
hypothesis: for every `ε > 0` there is `C > 0` such that for `1 ≤ T`, `0 < η`, `2 ≤ B`, `2B ≤ T^η`,
`0 < M₁`, `0 < M₂`, `1 ≤ M₃` and `f ≥ 0` continuous with `SuppHyp C₀ f`,

`∫_{T^η M₁/M₃ < |ξ| ≤ T⁶} ‖Σ_{m₁∈R1 M₁} (1/|m₁|) Bsum f M₂ (ξ/m₁) · Wwin K M₃ B (ξ/m₁)‖²
   ≤ C T^{6ε} (M₁ + M₁M₃ + M₃ + M₃²) ∫ (Hsum M₂ f)²`. -/
def WindowPartBound (C₀ K : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (T η B : ℝ) (M₁ M₂ M₃ : ℝ),
    1 ≤ T → 0 < η → 2 ≤ B → 2 * B ≤ T ^ η → 0 < M₁ → 0 < M₂ → 1 ≤ M₃ →
    ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
    (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
        \ (Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)),
      ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wwin K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2) ≤
      C * T ^ (6 * ε) * (M₁ + M₁ * M₃ + M₃ + M₃ ^ 2) * ∫ s, (Hsum M₂ f s) ^ 2

end

end Work.GM.Affine
