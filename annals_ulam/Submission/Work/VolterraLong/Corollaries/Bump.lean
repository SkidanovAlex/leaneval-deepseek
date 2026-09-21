import Submission.Work.VolterraLong.Main

/-!
# The bump-parameter form

The data is presented through a single perturbation parameter `h : ℝ → ℝ`
(a "bump"), with the base data at `h = 0`.  The only extra input is the
*quantitative* bridge from "`h` is small in `C^K`" to "the data is close", of
the shape

`(∀ k ≤ K, ∀ s ∈ [a,b], ‖iteratedDeriv k h s‖ ≤ δ) → closeness at level δ`.

This is exactly how the odd-dimensional Ulam data
(`Work.OddVolterra.Godd`, `Work.OddVolterra.Theta`, `Work.OddVolterra.Xi`) is
presented, and it isolates all the work of estimating the data from the
functional-analytic content of the long-interval existence theorem.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace Work.VolterraLong

/-- **Long-interval existence for a bump family of data.** -/
theorem volterra_long_exists_bump {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    (Gf : (ℝ → ℝ) → ℝ → E → E) (Θf : (ℝ → ℝ) → ℝ → ℝ → E → E)
    (Ξf : (ℝ → ℝ) → ℝ → E) (A : ℝ → E ≃L[ℝ] E) (Z₀ : ℝ → E)
    {B L Cg : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (hCg : 0 ≤ Cg)
    (hA_spec : ∀ s ∈ Set.Icc a b, (A s : E →L[ℝ] E) = fderiv ℝ (fun z => Gf 0 s z) (Z₀ s))
    (hA_cont : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b))
    (hAb : ∀ s ∈ Set.Icc a b, ‖((A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (hΘ0_cont : Continuous (fun p : ℝ × ℝ × E => Θf 0 p.1 p.2.1 p.2.2))
    (hbase : ∀ s ∈ Set.Icc a b, Gf 0 s (Z₀ s) = (∫ σ in s..b, Θf 0 s σ (Z₀ σ)) + Ξf 0 s)
    (h : ℝ → ℝ) {K : ℕ}
    (hΘ_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b,
      ∀ z ∈ Metric.closedBall (Z₀ σ) 1, ∀ z' ∈ Metric.closedBall (Z₀ σ) 1,
      ‖Θf h s σ z - Θf h s σ z'‖ ≤ L * ‖z - z'‖)
    (hdiff : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      DifferentiableAt ℝ (fun w => Gf h s w) z)
    (hG_cont : Continuous (fun p : ℝ × E => Gf h p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θf h p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous (Ξf h))
    (hclG : ∀ δ > 0, (∀ k ≤ K, ∀ s ∈ Set.Icc a b, ‖iteratedDeriv k h s‖ ≤ δ) →
      ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      dist (Gf h s z) (Gf 0 s z) < δ)
    (hclΘ : ∀ δ > 0, (∀ k ≤ K, ∀ s ∈ Set.Icc a b, ‖iteratedDeriv k h s‖ ≤ δ) →
      ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) 1,
      dist (Θf h s σ z) (Θf 0 s σ z) < δ)
    (hclΞ : ∀ δ > 0, (∀ k ≤ K, ∀ s ∈ Set.Icc a b, ‖iteratedDeriv k h s‖ ≤ δ) →
      ∀ s ∈ Set.Icc a b, dist (Ξf h s) (Ξf 0 s) < δ)
    (hclD : ∀ δ > 0, (∀ k ≤ K, ∀ s ∈ Set.Icc a b, ‖iteratedDeriv k h s‖ ≤ δ) →
      ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) 1,
      ‖fderiv ℝ (fun w => Gf h s w) z - (A s : E →L[ℝ] E)‖ ≤ Cg * ‖z - Z₀ s‖ + δ) :
    ∃ ε₀ > 0, ∀ δ : ℝ, 0 < δ → δ < ε₀ →
      (∀ k ≤ K, ∀ s ∈ Set.Icc a b, ‖iteratedDeriv k h s‖ ≤ δ) →
      ∃ Z : ℝ → E, ContinuousOn Z (Set.Icc a b) ∧ SolvesOn a b (Gf h) (Θf h) (Ξf h) Z ∧
        (∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ 2 * B * (2 + (b - a)) *
          Real.exp ((4 * B * L + 1) * (b - a)) * δ) := by
  obtain ⟨ε₀, hε₀, hmain⟩ := volterra_long_exists hab A (Gf 0) (Gf h) (Θf 0) (Θf h)
    (Ξf 0) (Ξf h) Z₀ hB hL hCg hA_spec hA_cont hAb hG_cont hΘ_cont hΞ_cont
    hZ₀_cont hΘ0_cont hbase hΘ_lip hdiff
  refine ⟨ε₀, hε₀, fun δ hδ hδε hsmall => ?_⟩
  exact hmain δ hδ hδε (hclΞ δ hδ hsmall) (hclG δ hδ hsmall) (hclΘ δ hδ hsmall)
    (hclD δ hδ hsmall)

end Work.VolterraLong
