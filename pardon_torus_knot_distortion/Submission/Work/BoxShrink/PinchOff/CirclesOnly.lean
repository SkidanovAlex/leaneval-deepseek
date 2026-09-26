import Submission.Work.BoxShrink.PinchOff.Laminar
import Submission.Work.InnermostDisk.WindingAPI

/-!
# The circles-only case of the slice: what is proved, and what is left

This module carries the two facts about a slice made of **closed** curves (the circles of
`Σ = F ∩ PBox ∩ Π`) that the workspace already supplies, and repackages the disc-covering datum of
`Laminar.lean` in the two forms in which a caller can supply it.

* `not_isEssential_of_range_subset_slice` — if the slice carries no essential loop (`hZ`), then
  *every* closed curve of the surface whose image lies in the slice is inessential.  This is
  immediate from the definition of `ParamTorus.ContainsEssentialLoop`, but it is the step that
  connects `hZ` to the disc machinery of `Work.InnermostDisk`.
* `boundsDiscInSurface_of_range_subset_slice` — consequently every such curve **bounds a disc of the
  surface** (`Work.InnermostDisk.BoundsDiscInSurface`), by
  `Work.InnermostDisk.boundsDiscInSurface_iff_not_isEssential`.  So the slice **circles** of the
  circles-only case each bound a disc of the surface: this is item (1) of `README.md` §3, and it is
  now a theorem.
* `sliceDiscCovering_of_single`, `sliceDiscCovering_of_disjoint` — the two ways of producing a
  `SliceDiscCovering` from embedded discs: one disc covering the slice, or finitely many pairwise
  disjoint ones.  With `bubbleHalf_of_sliceDiscCovering` these convert a covering into Pardon's
  Lemma 3 conclusion at the configuration.

**What is still missing for the circles-only case** (README §3, items (2) and (3)):

* (2) *Containment/thickening*: the disc `Δ` bounded by a slice circle must be replaced by a
  `DiscRegion` whose *carrier* lies in the open region `Ω` and whose *interior* contains the circle.
  This is not a consequence of `hZ` and `hS` alone: a slice circle may bound its disc on the part of
  the surface that leaves the box.  What is provable from the workspaces's tools is the *local*
  enlargement (a collar neighbourhood of the boundary circle), and that is not in Mathlib.
* (3) *Laminarity*: two discs bounded by disjoint level circles are disjoint or nested.  This is
  Jordan separation on the surface; the workspace has the planar statement
  (`Work.Smooth.JordanSeparation`) and the combinatorial pruning `exists_disjoint_refinement`, but
  not the surface form.

Neither (2) nor (3) is formalised below: only the facts that do not need them.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## The slice circles bound discs of the surface -/

/-- **Every closed curve of the surface whose image lies in the slice is inessential** (from `hZ`).

This is the form in which `hZ` meets the disc machinery: "the slice carries no essential loop"
unfolds to "no closed curve inside the slice has a nonzero winding vector". -/
theorem not_isEssential_of_range_subset_slice
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u))
    (γ : Work.CoreTopology.ClosedCurve (surface ψ))
    (hγ : ∀ t : ℝ, γ t ∈ Sigma ψ s c σ u) :
    ¬ Work.CoreTopology.IsEssential (surface ψ) γ :=
  fun h => hZ ⟨γ, h, hγ⟩

/-- **Every closed curve of the surface whose image lies in the slice bounds a disc of the
surface.**  The circles of the circles-only case are exactly such curves (a slice circle is a closed
curve of the surface with image in `Σ`), so each of them bounds a disc of `F`: this is item (1) of
`README.md` §3. -/
theorem boundsDiscInSurface_of_range_subset_slice
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u))
    (γ : Work.CoreTopology.ClosedCurve (surface ψ))
    (hγ : ∀ t : ℝ, γ t ∈ Sigma ψ s c σ u) :
    Work.InnermostDisk.BoundsDiscInSurface (surface ψ) γ :=
  (Work.InnermostDisk.boundsDiscInSurface_iff_not_isEssential γ).mpr
    (not_isEssential_of_range_subset_slice hZ γ hγ)

/-- The winding vector of a closed curve of the surface inside the slice vanishes. -/
theorem windingOf_eq_zero_of_range_subset_slice
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u))
    (γ : Work.CoreTopology.ClosedCurve (surface ψ))
    (hγ : ∀ t : ℝ, γ t ∈ Sigma ψ s c σ u) :
    Work.SurgeryInvariance.windingOf (surface ψ) γ = (0, 0) := by
  by_contra h
  exact not_isEssential_of_range_subset_slice hZ γ hγ
    ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero (surface ψ) γ).mpr h)

/-! ## Producing a `SliceDiscCovering` -/

/-- **A single embedded disc inside the region that covers the slice** gives a
`SliceDiscCovering`: a one-element family is laminar for trivial reasons. -/
theorem sliceDiscCovering_of_single (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hsub : D.carrier ⊆ Omega ψ s c σ)
    (hcov : ∀ x ∈ Sigma ψ s c σ u, x ∈ D.interior) : SliceDiscCovering ψ s c σ u := by
  refine ⟨[D], List.nodup_singleton D, ?_, ?_, ?_⟩
  · intro D' hD' D'' hD'' hne
    simp only [List.mem_singleton] at hD' hD''
    exact absurd (hD'.trans hD''.symm) hne
  · intro D' hD'
    rw [List.mem_singleton] at hD'
    rw [hD']
    exact hsub
  · intro x hx
    exact ⟨D, List.mem_singleton_self D, hcov x hx⟩

/-- **Finitely many pairwise disjoint embedded discs inside the region whose interiors cover the
slice** give a `SliceDiscCovering` (pairwise disjoint carriers are in particular laminar). -/
theorem sliceDiscCovering_of_disjoint (L : List (Work.SurgeryInvariance.DiscRegion (surface ψ)))
    (hnodup : L.Nodup)
    (hdisj : ∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier)
    (hsub : ∀ D ∈ L, D.carrier ⊆ Omega ψ s c σ)
    (hcov : ∀ x ∈ Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior) :
    SliceDiscCovering ψ s c σ u :=
  ⟨L, hnodup,
    fun D hD D' hD' hne => Or.inl (hdisj D hD D' hD' hne),
    hsub, hcov⟩

/-- **Pardon's Lemma 3 conclusion from a single embedded disc inside the region that covers the
slice.**  A repackaging of `bubbleHalf_of_sliceDiscCovering` through
`sliceDiscCovering_of_single`. -/
theorem bubbleHalf_of_slice_in_region_disc (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hsub : D.carrier ⊆ Omega ψ s c σ)
    (hcov : ∀ x ∈ Sigma ψ s c σ u, x ∈ D.interior) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_sliceDiscCovering (sliceDiscCovering_of_single D hsub hcov)

/-- **Pardon's Lemma 3 conclusion from finitely many pairwise disjoint embedded discs inside the
region whose interiors cover the slice.** -/
theorem bubbleHalf_of_slice_in_region_disjoint_discs
    (L : List (Work.SurgeryInvariance.DiscRegion (surface ψ))) (hnodup : L.Nodup)
    (hdisj : ∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier)
    (hsub : ∀ D ∈ L, D.carrier ⊆ Omega ψ s c σ)
    (hcov : ∀ x ∈ Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_sliceDiscCovering
    (sliceDiscCovering_of_disjoint L hnodup hdisj hsub hcov)

end

end Work.BoxShrink.PinchOff
