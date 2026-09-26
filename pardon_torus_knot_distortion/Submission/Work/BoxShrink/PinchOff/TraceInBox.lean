import Submission.Work.BoxShrink.PinchOff.Basic
import Submission.Work.BoxShrink.PinchOff.TraceReduction
import Submission.Work.BoxShrink.PinchOff.trace_loop_in_box_avoiding_plane

/-!
# A discharged case of the pinch residual: a trace class realised inside the box

`trace_loop_in_box_avoiding_plane` (proved in this directory) says that a closed curve of the
smooth surface whose image lies in the *plane trace* and inside the (open) box `PBox s c σ` can be
replaced by a closed curve of the union of the two half-regions with the same winding vector.

This module turns that into a discharged case of the pinch residual

  `Work.BoxShrink.Pinch.TraceMultipleRealisable (surface ψ) s c σ u`:

* `mem_halves_span_of_trace_loop_in_box` — the winding vector of any such slice loop lies in the
  winding span of the halves;
* **`traceMultipleRealisable_of_trace_loop_in_box`** — if some nonzero trace-line class is realised
  by a closed curve of the surface lying in the slice *and inside the box*, then the residual holds
  at that configuration (the second disjunct, with `W (box) ⊓ ℚ∙v ≤ ℚ∙v ≤ W (halves)`).

This is a genuine (if special) discharge of the residual: the trace line may be essential, and it
covers in particular the configurations in which a component of the trace (a level *circle*) is
contained in the box.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- The push-off lemma, in the form used below: a slice loop inside the box has a representative in
the halves with the same winding vector. -/
theorem exists_halves_loop_of_slice_loop_in_box
    (hTT : Work.BoxShrink.Pinch.TransverseTrace ψ c σ u)
    (γ : Work.CoreTopology.ClosedCurve (surface ψ))
    (hγ : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.sliceRegion (surface ψ) s c σ u) :
    ∃ γ' : Work.CoreTopology.ClosedCurve (surface ψ),
      (∀ t : ℝ, γ' t ∈ Halves ψ s c σ u) ∧
      Work.SurgeryInvariance.windingOf (surface ψ) γ' =
        Work.SurgeryInvariance.windingOf (surface ψ) γ := by
  have hbox : ∀ t : ℝ, γ t ∈ Submission.PBox s c σ :=
    fun t => (Work.BoxShrink.Core.mem_sliceRegion.mp (hγ t)).2.1
  have hplane : ∀ t : ℝ, γ t ∈ (surface ψ).carrier ∩ Work.BoxShrink.Core.cutPlane c σ u :=
    fun t => ⟨(Work.BoxShrink.Core.mem_sliceRegion.mp (hγ t)).1,
      (Work.BoxShrink.Core.mem_cutPlane).mpr (Work.BoxShrink.Core.mem_sliceRegion.mp (hγ t)).2.2⟩
  exact Work.BoxShrink.PinchOff.trace_loop_in_box_avoiding_plane ψ s c σ u hTT γ hplane hbox

/-- **The winding vector of a slice loop inside the box lies in the winding span of the halves.** -/
theorem windingVectors_sliceRegion_subset_halves
    (hTT : Work.BoxShrink.Pinch.TransverseTrace ψ c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Sigma ψ s c σ u) ≤
      Whalves (surface ψ) s c σ u := by
  show Submodule.span ℚ (Work.SurgeryInvariance.windingVectors (surface ψ) (Sigma ψ s c σ u)) ≤
    Submodule.span ℚ (Work.SurgeryInvariance.windingVectors (surface ψ) (Halves ψ s c σ u))
  rw [Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  obtain ⟨γ', hγ', hw⟩ := exists_halves_loop_of_slice_loop_in_box (ψ := ψ) hTT γ hγ
  refine Submodule.subset_span ⟨γ', hγ', ?_⟩
  have := congrArg (fun w : ℤ × ℤ => ((((w.1 : ℤ) : ℚ), (((w.2 : ℤ) : ℚ))))) hw
  simpa using this

/-- **A trace-line class realised by a slice loop inside the box discharges the residual.**  The
class is realised by a loop of the halves (the push-off lemma), so the residual's second disjunct
holds with it. -/
theorem traceMultipleRealisable_of_trace_loop_in_box
    (hTT : Work.BoxShrink.Pinch.TransverseTrace ψ c σ u)
    (v : ℚ × ℚ) (hv : v ≠ 0)
    (hvL : ∃ L : Submodule ℚ (ℚ × ℚ),
      Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L ∧ v ∈ L)
    (hreal : ∃ γ : Work.CoreTopology.ClosedCurve (surface ψ),
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.sliceRegion (surface ψ) s c σ u) ∧
      ((((Work.SurgeryInvariance.windingOf (surface ψ) γ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf (surface ψ) γ).2 : ℤ) : ℚ)) = v) :
    Work.BoxShrink.Pinch.TraceMultipleRealisable (surface ψ) s c σ u := by
  obtain ⟨γ, hγ, hγv⟩ := hreal
  obtain ⟨γ', hγ', hw⟩ := exists_halves_loop_of_slice_loop_in_box (ψ := ψ) hTT γ hγ
  have hvmem : v ∈ Whalves (surface ψ) s c σ u := by
    rw [← hγv]
    exact Submodule.subset_span ⟨γ', hγ', by rw [hw]⟩
  refine Or.inr ⟨v, hv, hvL, ?_⟩
  refine le_trans inf_le_right ?_
  rw [Submodule.span_le]
  simpa using hvmem

end

end Work.BoxShrink.PinchOff
