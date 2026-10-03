import Mathlib
import Submission.Lib.Unif2.Work.Drive.chartGadget
import Submission.Lib.Unif2.Work.Drive.continuousAt_chGadget
import Submission.Lib.Unif2.Work.Drive.phaseChainDefs

namespace Work.Drive

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

theorem continuousAt_chPhi_of_notMem_range {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {c : ℕ → OpenPartialHomeomorph X ℂ} {a : ℕ → X} {ρ : ℕ → ℝ}
    (hρ : ∀ i, 0 < ρ i)
    (hsrc : ∀ i, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source)
    (hclose : ∀ i, ‖Work.Drive.chQ c a i - Work.Drive.chP c a i‖ < 2 * ρ i)
    (hwell : ∀ i, closure {y : X | y ∈ (c i).source ∧
      (c i) y ∈ Metric.ball ((c i) (a i)) (8 * ρ i)} ⊆ (c i).source)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ {y : X | y ∈ (c i).source ∧
      (c i) y ∈ Metric.ball ((c i) (a i)) (8 * ρ i)}).Nonempty}.Finite)
    {p : X} (hp : ∀ i : ℕ, p ≠ a i) :
    ContinuousAt (fun x : X => ∏ᶠ i : ℕ, Work.Drive.chGadget c a ρ i x) p := by
  classical
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  obtain ⟨K, hKc, hKnhds⟩ := exists_compact_mem_nhds p
  refine continuousAt_finprod (g := fun i (x : X) => chGadget c a ρ i x) ?_ ?_
  · refine ⟨(hlf K hKc).toFinset, ?_⟩
    filter_upwards [hKnhds] with y hy i hi
    rw [Set.Finite.mem_toFinset]
    have hmem := chGadget_ne_one_mem (c := c) (a := a) (ρ := ρ) (i := i) (hρ i) hi
    exact ⟨y, hy, hmem.1, by simpa [Metric.mem_ball, dist_eq_norm] using hmem.2⟩
  · intro i
    exact continuousAt_chGadget (hρ i) (hclose i) (hsrc i).1 (hsrc i).2 (hwell i)
      (hp i) (hp (i + 1))

end Work.Drive
