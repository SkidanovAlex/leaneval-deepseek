import Mathlib
import Submission.Work.Drive.N2Lead.saddleBridgeRow

namespace Work.Drive.N2Lead

open scoped ContDiff Topology
open Set Filter

noncomputable section

/-- **The `Möbius` form of the bridge row.**  Identical to `saddleBridgeRow` except that the lower
arc prescription sits at `3 π / 2 + (1/2) arctan (w/ηs)` instead of `-(π/2) - (1/2) arctan (w/ηs)`,
i.e. the two lower arcs differ by the period `2π`.

The reduction to `saddleBridgeRow` is the substitution `w ↦ -w` together with a shift of the
parameter by one period: with `τL' w := τL (-w) - 1` one has
`Θ (τL' w) = Θ (τL (-w)) - 2 π = 3π/2 + (1/2) arctan ((-w)/ηs) - 2π
        = -(π/2) - (1/2) arctan (w/ηs)`,
which is exactly the lower arc row of `saddleBridgeRow`; and the exclusion rows transform
correspondingly (`t ≠ τL' w + k ↔ t ≠ τL (-w) + (k - 1)`). -/
theorem saddleBridgeRowMobius {ηs m c₀ : ℝ} (hηs : 0 < ηs) (hm : 0 < m)
    {r Θ τU τL : ℝ → ℝ}
    (hΘmono : StrictMono Θ) (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi)
    (hΘU : ∀ w ∈ Set.Icc (-m) m, Θ (τU w) = Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
    (hΘL : ∀ w ∈ Set.Icc (-m) m, Θ (τL w) = 3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))
    (hbridge : ∀ (φ : ℝ) (k : ℤ), |φ - k * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE ηs m →
      Real.sqrt (ηs ^ 2 + m ^ 2) ≤ r φ ^ 2)
    (hnum : c₀ + 2 * ηs < Real.sqrt (ηs ^ 2 + m ^ 2)) :
    ∀ t : ℝ, (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τU w + k) →
      (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τL w + k) → c₀ + 2 * ηs < r (Θ t) ^ 2 := by
  intro t hU hL
  -- Shift the lower family by one period and reverse its parametrisation.
  refine saddleBridgeRow (τL := fun w => τL (-w) - 1)
    hηs hm hΘmono hΘper hΘU ?_ hbridge hnum t hU ?_
  · intro w hw
    have hw' : -w ∈ Set.Icc (-m) m := ⟨by linarith [hw.2], by linarith [hw.1]⟩
    have hshift : Θ (τL (-w) - 1) = Θ (τL (-w)) - 2 * Real.pi := by
      have h := hΘper (τL (-w) - 1)
      rw [show τL (-w) - 1 + 1 = τL (-w) by ring] at h
      linarith
    rw [hshift, hΘL (-w) hw']
    rw [show (-w) / ηs = -(w / ηs) by ring, Real.arctan_neg]
    ring
  · intro w k hw
    have hw' : -w ∈ Set.Icc (-m) m := ⟨by linarith [hw.2], by linarith [hw.1]⟩
    have h2 : τL (-w) + ((k - 1 : ℤ) : ℝ) = τL (-w) - 1 + (k : ℝ) := by push_cast; ring
    exact fun heq => hL (-w) (k - 1) hw' (by rw [h2]; exact heq)

end

end Work.Drive.N2Lead
