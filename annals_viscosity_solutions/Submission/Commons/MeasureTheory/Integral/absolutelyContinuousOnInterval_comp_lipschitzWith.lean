import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Topology.MetricSpace.Lipschitz

namespace Commons.MeasureTheory.Integral

open Set Filter

/-- Postcomposition of an absolutely continuous function on an interval with a Lipschitz map is
again absolutely continuous on that interval.

This is immediate from the `ε`-`δ` characterisation of `AbsolutelyContinuousOnInterval`: the
Lipschitz bound `dist (g x) (g y) ≤ K * dist x y` upgrades the small total length estimate of `ψ`
to a small total length estimate for `g ∘ ψ` (with `ε` replaced by `ε / (K + 1)`). -/
theorem absolutelyContinuousOnInterval_comp_lipschitzWith {E F : Type*} [PseudoMetricSpace E]
    [PseudoMetricSpace F] {ψ : ℝ → E} {g : E → F} {a b : ℝ} {K : NNReal}
    (hψ : AbsolutelyContinuousOnInterval ψ a b) (hg : LipschitzWith K g) :
    AbsolutelyContinuousOnInterval (fun t => g (ψ t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hψ ⊢
  intro ε hε
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hε' : 0 < ε / ((K : ℝ) + 1) := div_pos hε hK1
  obtain ⟨δ, hδ, hδprop⟩ := hψ (ε / ((K : ℝ) + 1)) hε'
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have hsumψ : ∑ i ∈ Finset.range E.1, dist (ψ (E.2 i).1) (ψ (E.2 i).2)
      < ε / ((K : ℝ) + 1) := hδprop E hE hlen
  have hstep : ∑ i ∈ Finset.range E.1, dist (g (ψ (E.2 i).1)) (g (ψ (E.2 i).2))
      ≤ (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (ψ (E.2 i).1) (ψ (E.2 i).2) := by
    calc ∑ i ∈ Finset.range E.1, dist (g (ψ (E.2 i).1)) (g (ψ (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (ψ (E.2 i).1) (ψ (E.2 i).2) :=
          Finset.sum_le_sum fun i _ => hg.dist_le_mul _ _
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (ψ (E.2 i).1) (ψ (E.2 i).2) := by
          rw [Finset.mul_sum]
  have hfinal : (K : ℝ) * (ε / ((K : ℝ) + 1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hK1]
    nlinarith [K.coe_nonneg]
  calc ∑ i ∈ Finset.range E.1, dist (g (ψ (E.2 i).1)) (g (ψ (E.2 i).2))
      ≤ (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (ψ (E.2 i).1) (ψ (E.2 i).2) := hstep
    _ ≤ (K : ℝ) * (ε / ((K : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hsumψ.le K.coe_nonneg
    _ < ε := hfinal

end Commons.MeasureTheory.Integral
