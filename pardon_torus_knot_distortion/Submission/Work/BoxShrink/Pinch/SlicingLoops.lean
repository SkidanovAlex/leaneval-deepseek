import Submission.Work.Smooth.Plane.Slicing
import Submission.Work.BoxShrink.Pinch.Basic

/-!
# The slice is carried by inessential curves (the first step of the tame analysis)

`TameSlice` is the hypothesis that the trace of the cutting plane on the surface is a *slicing*
(`Work.Smooth.Plane.TransversePlane`, reducible to the sanctioned `CompactOneManifoldInput` plus
`TransversePlane`): finitely many pairwise disjoint simple closed curves and embedded arcs covering
every loop.  This module records the first consequences used by the analysis of README §10.3:

* `Work.BoxShrink.Pinch.windingOf_eq_zero_of_planeSlicing_circle` — if the slice region carries no
  essential loop (`hZ`), then **every closed component of the slicing has vanishing winding
  vector**;
* `Work.BoxShrink.Pinch.exists_slicing_component_of_loop` — every loop of the surface lying in the
  cut disc lies on a closed component or on an arc (the covering property, restated);
* the pinch specialisations `sliceRegion_eq_carrier_inter_cutDisc` and
  `windingOf_eq_zero_of_tameSlice_circle`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-- **Every closed component of a slicing whose region is inessential has zero winding.**  A
consequence of `Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero`: the component itself is a
loop of the surface lying in the sliced region. -/
theorem windingOf_eq_zero_of_planeSlicing_circle {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : Work.Smooth.Plane.PlaneSlicing P D)
    (hZ : ¬ P.ContainsEssentialLoop (P.carrier ∩ D)) (i : h.ι) :
    Work.SurgeryInvariance.windingOf P (h.c i) = 0 := by
  have hine : ¬ Work.CoreTopology.IsEssential P (h.c i) := by
    intro hess
    exact hZ ⟨h.c i, hess, fun t => ⟨(h.c i).mem t, h.mem i t⟩⟩
  exact not_not.mp ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P (h.c i)).not.mp hine)

/-- **Every loop of the surface inside the cut disc lies on a closed component or on an arc** (the
covering property of the slicing, restated in the form the analysis consumes). -/
theorem exists_slicing_component_of_loop {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : Work.Smooth.Plane.PlaneSlicing P D) (γ : Work.CoreTopology.ClosedCurve P)
    (hγ : ∀ t : ℝ, γ.γ t ∈ D) :
    (∃ i : h.ι, Set.range γ.γ ⊆ Set.range (h.c i).γ) ∨
      (∃ j : h.κ, Set.range γ.γ ⊆ Set.range (h.a j)) :=
  h.covers γ hγ

/-- The slice region of the pinch is exactly the trace of the cut disc on the surface. -/
theorem sliceRegion_eq_carrier_inter_cutDisc (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.sliceRegion P s c σ u =
      P.carrier ∩ Work.BoxShrink.Core.cutDisc s c σ u := by
  ext x
  simp only [Work.BoxShrink.Core.sliceRegion, Work.BoxShrink.Core.cutDisc, Set.mem_inter_iff]
  tauto

/-- **The pinch instance**: a tame slice whose region carries no essential loop has all its closed
components of vanishing winding. -/
theorem windingOf_eq_zero_of_tameSlice_circle {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hslice : Work.Smooth.Plane.PlaneSlicing (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.cutDisc s c σ u))
    (hZ : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u)) (i : hslice.ι) :
    Work.SurgeryInvariance.windingOf (Work.Smooth.Morse.torus ψ) (hslice.c i) = 0 :=
  windingOf_eq_zero_of_planeSlicing_circle hslice (by
    rw [sliceRegion_eq_carrier_inter_cutDisc] at hZ
    exact hZ) i

end

end Work.BoxShrink.Pinch
