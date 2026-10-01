import Mathlib

open scoped Topology

set_option linter.unusedVariables false

namespace Work.LinnikAreas2

/-- Existence of a small positive `ε` on the "side" of the interval analysis: if the three
strict inequalities `f₀/6 < B`, `f₀/6 · A < (B - f₀/6)²` and the ratio bound at `ε = 0` hold,
then they persist for some honest `ε > 0`.  Purely a continuity/openness argument: at `ε = 0`
all three conditions hold strictly, so a neighborhood of `0` works, and we take half of a
radius. -/
theorem exists_eps_side {A B f₀ : ℝ} {N₀ : ℕ}
    (hf0 : 0 < f₀) (hA : 0 < A) (hpos : f₀ * (1/6) < B)
    (hden : f₀ * (1/6) * A < (B - f₀ * (1/6)) ^ 2)
    (hbnd : A * (A - f₀/6) / ((B - f₀/6)^2 - A * (f₀/6)) < (N₀ : ℝ) + 1) :
    ∃ ε : ℝ, 0 < ε ∧ f₀ * (1/6 + ε) < B ∧
      f₀ * (1/6 + ε) * (A + f₀ * ε) < (B - f₀ * (1/6 + ε)) ^ 2 ∧
      (A + f₀*ε) * (A - f₀/6) / ((B - f₀*(1/6+ε))^2 - f₀*(1/6+ε)*(A + f₀*ε)) < (N₀ : ℝ) + 1 := by
  -- First condition: `ε ↦ f₀(1/6+ε) < B` holds on an open set containing `0`.
  have e1 : ∀ᶠ ε in 𝓝 (0:ℝ), f₀ * (1/6 + ε) < B := by
    have hcont : Continuous (fun ε : ℝ => f₀ * (1/6 + ε)) := by continuity
    exact (isOpen_lt hcont continuous_const).mem_nhds (by simpa using hpos)
  -- Second condition: same, with the LHS strictly less than the RHS at `ε = 0`.
  have e2 : ∀ᶠ ε in 𝓝 (0:ℝ), f₀ * (1/6 + ε) * (A + f₀ * ε) < (B - f₀ * (1/6 + ε)) ^ 2 := by
    have hc1 : Continuous (fun ε : ℝ => f₀ * (1/6 + ε) * (A + f₀ * ε)) := by continuity
    have hc2 : Continuous (fun ε : ℝ => (B - f₀ * (1/6 + ε)) ^ 2) := by continuity
    exact (isOpen_lt hc1 hc2).mem_nhds (by simpa using hden)
  -- Third condition: the ratio is continuous at `0` (denominator positive there) and is
  -- strictly below `N₀ + 1` at `ε = 0`, hence remains so nearby.
  have e3 : ∀ᶠ ε in 𝓝 (0:ℝ),
      (A + f₀*ε) * (A - f₀/6) / ((B - f₀*(1/6+ε))^2 - f₀*(1/6+ε)*(A + f₀*ε)) < (N₀ : ℝ) + 1 := by
    have hnum : ContinuousAt (fun ε : ℝ => (A + f₀*ε) * (A - f₀/6)) 0 :=
      (by continuity : Continuous (fun ε : ℝ => (A + f₀*ε) * (A - f₀/6))).continuousAt
    have hdenc : ContinuousAt (fun ε : ℝ => (B - f₀*(1/6+ε))^2 - f₀*(1/6+ε)*(A + f₀*ε)) 0 :=
      (by continuity :
        Continuous (fun ε : ℝ => (B - f₀*(1/6+ε))^2 - f₀*(1/6+ε)*(A + f₀*ε))).continuousAt
    have hdenne : (fun ε : ℝ => (B - f₀*(1/6+ε))^2 - f₀*(1/6+ε)*(A + f₀*ε)) 0 ≠ 0 := by
      have hpos' : 0 < (B - f₀*(1/6))^2 - f₀*(1/6)*A := by linarith [hden]
      simp only [mul_zero, add_zero]
      exact ne_of_gt hpos'
    have hFcont : ContinuousAt
        (fun ε : ℝ => (A + f₀*ε) * (A - f₀/6) /
          ((B - f₀*(1/6+ε))^2 - f₀*(1/6+ε)*(A + f₀*ε))) 0 :=
      hnum.div hdenc hdenne
    have hF0 : (fun ε : ℝ => (A + f₀*ε) * (A - f₀/6) /
          ((B - f₀*(1/6+ε))^2 - f₀*(1/6+ε)*(A + f₀*ε))) 0 < (N₀ : ℝ) + 1 := by
      simp only [mul_zero, add_zero]
      have key : A * (A - f₀/6) / ((B - f₀/6)^2 - A * (f₀/6)) =
          A * (A - f₀/6) / ((B - f₀*(1/6))^2 - f₀*(1/6)*A) := by ring
      rw [← key]
      exact hbnd
    have hnbhd : Set.Iio ((N₀:ℝ)+1) ∈ 𝓝
        ((fun ε : ℝ => (A + f₀*ε) * (A - f₀/6) /
          ((B - f₀*(1/6+ε))^2 - f₀*(1/6+ε)*(A + f₀*ε))) 0) := Iio_mem_nhds hF0
    exact hFcont.tendsto.eventually hnbhd
  -- All three hold on a common neighborhood of `0`.
  have e : ∀ᶠ ε in 𝓝 (0:ℝ),
      f₀ * (1/6 + ε) < B ∧
      f₀ * (1/6 + ε) * (A + f₀ * ε) < (B - f₀ * (1/6 + ε)) ^ 2 ∧
      (A + f₀*ε) * (A - f₀/6) /
        ((B - f₀*(1/6+ε))^2 - f₀*(1/6+ε)*(A + f₀*ε)) < (N₀ : ℝ) + 1 :=
    e1.and (e2.and e3)
  -- Extract a radius `δ` and take `ε = δ/2 > 0`.
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp e
  have hd : dist (δ/2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  refine ⟨δ/2, by linarith, (hδ hd).1, (hδ hd).2.1, (hδ hd).2.2⟩

end Work.LinnikAreas2
