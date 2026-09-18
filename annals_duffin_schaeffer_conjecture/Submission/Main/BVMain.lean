/-
# Corollary 3 from the mass transference principle

This file assembles the lower bound of Corollary 3 from
* `Submission.Main.BVLower` (the `d`-exponent lower bound via the mass transference
  principle, with the finiteness of the truncated index set as a hypothesis), and
* `Submission.Work.BV.finite_idx_of_eps` (that finiteness).

The mass transference principle itself is supplied as a hypothesis `hMTP`
(`MTPStatement`); it is proved in `Submission/Work/MassTransference/`.
-/

import Submission.Main.BVLower
import Submission.Work.BV.finite_idx_of_eps

open scoped Nat ENNReal NNReal MeasureTheory Topology
open Set Filter MeasureTheory
open MeasureTheory.Measure
open DuffinSchaefferConjecture

namespace Submission.Main

/-- **The Hausdorff lower bound for one exponent**, with the finiteness hypothesis
discharged. -/
theorem hausdorff_A_eq_top_of_MTP' (hMTP : MTPStatement) (ψ : ℕ+ → ℝ≥0)
    (hψ : ∀ q : ℕ+, ψ q ≤ 1 / 2) (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (hdiv : ¬ Summable (fun q : ℕ+ => (φ q : NNReal) * ((ψ q / q : NNReal) ^ d))) :
    μH[d] (𝒜 ψ) = ∞ :=
  hausdorff_A_eq_top_of_MTP hMTP ψ hψ d hd0 hd1
    (fun ε hε => Work.BV.finite_idx_of_eps ψ d hd0 hd1 hψ ε hε) hdiv

/-- **Corollary 3**, conditional on the mass transference principle. -/
theorem corollary_3_of_MTP (hMTP : MTPStatement) (ψ : ℕ+ → ℝ≥0)
    (hψ : ∀ n : ℕ+, ψ n ∈ Set.Icc 0 (1 / 2 : ℝ≥0)) :
    dimH (𝒜 ψ) = min (s_inf ψ) 1 := by
  refine le_antisymm (Submission.DS.dimH_A_le_min ψ hψ) ?_
  have hge := dimH_A_ge_min_of_BV ψ hψ
    (fun d hd0 hd1 hdiv => hausdorff_A_eq_top_of_MTP' hMTP ψ (fun q => (hψ q).2) d hd0 hd1 hdiv)
  simpa using hge

end Submission.Main
