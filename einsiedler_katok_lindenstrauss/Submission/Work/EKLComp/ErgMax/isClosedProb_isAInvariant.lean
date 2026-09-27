import Mathlib
import Submission.Work.EKLComp.ErgMax.Basic

/-!
# C4c — the `A`-invariant probability measures are a closed set

`{μ | IsAInvariant μ}` is closed in the weak topology on probability measures on `X₃`.

The reason is topological: for a continuous self-map `T` of `X₃`, the push-forward
`μ ↦ T_*μ : ProbabilityMeasure X₃ → ProbabilityMeasure X₃` is continuous
(`ProbabilityMeasure.continuous_map`), and the fixed-point set `{μ | T_*μ = μ}` is the
preimage under the continuous map `μ ↦ (T_*μ, μ)` of the diagonal of a Hausdorff space, hence
closed.  A measure is `A`-invariant iff it is fixed by every `T = (x ↦ aDiag t • x)`, so the
`A`-invariant measures are an intersection of closed sets.

`P_X3` is used only to know that `ProbabilityMeasure X₃` is Hausdorff: it provides
`PolishSpace X₃` (`h2.2.1`), hence `PseudoMetrizableSpace X₃`, hence
`HasOuterApproxClosed X₃`, from which Mathlib derives `T2Space (ProbabilityMeasure X₃)`.
-/

open MeasureTheory Topology Filter
open Work.EKLContract
open scoped ENNReal

namespace Work.EKLComp.ErgMax

/-- The fixed-point set of the push-forward along `x ↦ aDiag t • x` is exactly the set of
probability measures that are preserved by `x ↦ aDiag t • x`. -/
theorem prob_eq_map_iff_measurePreserving (t : Fin 3 → ℝ) (μ : ProbabilityMeasure X3) :
    (ProbabilityMeasure.map μ (fun x : X3 => aDiag t • x) = μ) ↔
      MeasurePreserving (fun x : X3 => aDiag t • x) (μ : Measure X3) (μ : Measure X3) := by
  constructor
  · intro h
    refine MeasurePreserving.mk (continuous_act (aDiag t)).measurable ?_
    exact congrArg (fun ν : ProbabilityMeasure X3 => (ν : Measure X3)) h
  · intro h
    apply Subtype.ext
    exact h.map_eq

/-- The set of fixed points of the (continuous) push-forward along `x ↦ aDiag t • x` is closed
in `ProbabilityMeasure X₃`. -/
theorem isClosed_fixed_map [TopologicalSpace.PseudoMetrizableSpace X3]
    (t : Fin 3 → ℝ) :
    IsClosed {μ : ProbabilityMeasure X3 |
      ProbabilityMeasure.map μ (fun x : X3 => aDiag t • x) = μ} :=
  isClosed_eq (ProbabilityMeasure.continuous_map (continuous_act (aDiag t))) continuous_id

theorem isClosedProb_isAInvariant (h2 : Work.EKLContract.P_X3) :
    Work.EKLComp.ErgMax.IsClosedProb {μ : MeasureTheory.Measure Work.EKLContract.X3 |
      Work.EKLContract.IsAInvariant μ} := by
  have : PolishSpace Work.EKLContract.X3 := h2.2.1
  rw [IsClosedProb]
  have hset : {μ : ProbabilityMeasure Work.EKLContract.X3 |
        (μ : Measure Work.EKLContract.X3) ∈ {μ : Measure Work.EKLContract.X3 |
          Work.EKLContract.IsAInvariant μ}}
      = ⋂ (t : Fin 3 → ℝ),
        {μ : ProbabilityMeasure Work.EKLContract.X3 |
          ProbabilityMeasure.map μ (fun x : Work.EKLContract.X3 => aDiag t • x) = μ} := by
    ext μ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h t
      exact (prob_eq_map_iff_measurePreserving t μ).mpr (h t)
    · intro h t
      exact (prob_eq_map_iff_measurePreserving t μ).mp (h t)
  rw [hset]
  exact isClosed_iInter fun t => isClosed_fixed_map t

end Work.EKLComp.ErgMax
