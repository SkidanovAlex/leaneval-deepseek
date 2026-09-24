import Mathlib
import Submission.Work.GM.Affine.region_II_vocab

/-!
# GM §9, region II, the high part: definitions

This file fixes the two objects used in the proof of `Work.GM.Affine.region_II_resonant_high`,
the high part (`4 M₁/M₃ < |ξ| ≤ T⁶`) of the resonant region-II estimate of GM Lemma 9.2.

* `resRegion T M₁ M₃ = {ξ : 4 M₁/M₃ < |ξ| ≤ T⁶}` (written as the set difference of two `Icc`s,
  matching the statement of the estimate);
* `resMajorant M₁ M₂ M₃ T f ξ`: the Cauchy–Schwarz majorant obtained after counting the resonant
  pairs `(m₁,ℓ)`.  It is the finite sum over all candidate pairs `p = (m₁,ℓ)`,
  `m₁ ∈ R1 M₁`, `|ℓ| ≤ ⌈T⁶⌉+2`, of the `ℓ`-window indicator times the weight `1/m₁²` and the
  `m₂`-sum `‖Bsum f M₂ (ξ/m₁)‖²`.

The pointwise input is that on `resRegion`,
`‖ghatRes K M₁ M₂ M₃ f ξ‖² ≤ Cc · V² · M₃² · resMajorant M₁ M₂ M₃ T f ξ`
with `Cc` the resonant-pair count and `V` a bound for `‖psi1hat K‖`; the integral of
`resMajorant` is then estimated window by window in `window_integral_Bsum`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The high part of region II: `4 M₁/M₃ < |ξ| ≤ T⁶`. -/
def resRegion (T M₁ M₃ : ℝ) : Set ℝ :=
  Set.Icc (-(T ^ 6)) (T ^ 6) \ Set.Icc (-(4 * M₁ / M₃)) (4 * M₁ / M₃)

/-- The resonance-window majorant of `‖ghatRes‖²`. -/
def resMajorant (M₁ M₂ M₃ T : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∑ p ∈ (R1 M₁).product (Finset.Icc (-(⌈T ^ 6⌉ + 2)) (⌈T ^ 6⌉ + 2)),
    (if |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃ then
      (1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2 else 0)

/-- The index finset of candidate resonant pairs used in `resMajorant`. -/
def resPairs (M₁ T : ℝ) : Finset (ℤ × ℤ) :=
  (R1 M₁).product (Finset.Icc (-(⌈T ^ 6⌉ + 2)) (⌈T ^ 6⌉ + 2))

lemma resMajorant_eq (M₁ M₂ M₃ T : ℝ) (f : ℝ → ℝ) (ξ : ℝ) :
    resMajorant M₁ M₂ M₃ T f ξ
      = ∑ p ∈ resPairs M₁ T,
          (if |(p.2 : ℝ) - ξ / (p.1 : ℝ)| ≤ 2 / M₃ then
            (1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2 else 0) := rfl

end

end Work.GM.Affine
