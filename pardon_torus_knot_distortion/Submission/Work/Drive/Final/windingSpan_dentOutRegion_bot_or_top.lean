import Mathlib
import Submission.Work.Drive.Final.dentOut_clopen
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Drive.EpsFormSphere.dichotomy_of_trace_inessential
import Submission.Work.Drive.Final.windingSpan_dentOutRegion_eq_bot
import Submission.Work.Drive.Final.exists_dentOut_trace_family
import Submission.Work.EpsW.wallWithBoundaryDichotomy

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

/-- **The winding span of the dent-out region is `⊥` or `⊤`.**

This is Pardon's dichotomy on the preimage region `Ω₁ = F ∩ int (D.deform ⁻¹' removed)` of an
any-type dent datum, but *without* the counting input: the only hypothesis on the trace is the
"no essential loop" clause `hnoess` (which the counting supplies in the applications).  The trace is
a compact, locally Euclidean family of traces of embedded spheres; `hnoess` turns it into a family
of pairwise disjoint simple inessential closed curves, whose lift to the parameter plane has compact
components, and then Pardon's parameter-plane dichotomy
(`Work.EpsW.windingSpan_bot_or_top_of_closed_of_components_compact`) applies to the splitting of the
surface into `Ω₁` and the piece `F ∖ closure (D.deform ⁻¹' removed)` behind the trace. -/
theorem windingSpan_dentOutRegion_bot_or_top
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u h R : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    {U : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U)
    (ha' : |D.a'| * D.κ < D.r)
    {m : ℕ} {Ss : Fin m → Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hsph : ∀ i : Fin m, Work.InnermostDisk.IsEmbeddedSphere (Ss i))
    (hfront : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) = ⋃ i, Ss i)
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
        ((D.deform ⁻¹' Ss j) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (htame : ∀ i : Fin m,
      IsCompact ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hnoess : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))) :
    Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) = ⊤ := by
  classical
  -- The level removed set pulled back by the dent, and the trace of its frontier on the surface.
  set A : Set R3 := D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre) with hA
  -- the trace is compact and locally Euclidean, and carries no essential loop
  have hcomp : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier A) :=
    isCompact_carrier_inter_frontier_deform_preimage D ha' hfront (fun i => (htame i).1)
  have hloc : Work.Smooth.OneManifold.IsLocallyEuclidean
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier A) :=
    isLocallyEuclidean_carrier_inter_frontier_deform_preimage D ha' hsph hdisj hfront htame
  have hno : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier A) := hnoess
  -- hence the trace is the union of pairwise disjoint simple inessential closed curves
  obtain ⟨n, cs, hsimple, hess, hdisjcs, hZeq⟩ :=
    exists_family_of_not_containsEssentialLoop (P := Work.Drive.EpsSphere.torusOf ψ)
      (Z := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier A)
      Set.inter_subset_left hcomp hloc hno
  -- the lift of the trace to the parameter plane has compact components
  have hcompC : ∀ z ∈ Work.BoxShrink.PinchOff.Xtilde (Work.Drive.EpsSphere.torusOf ψ)
        ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier A),
      IsCompact (connectedComponentIn
        (Work.BoxShrink.PinchOff.Xtilde (Work.Drive.EpsSphere.torusOf ψ)
          ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier A)) z) := by
    intro z hz
    rw [hZeq] at hz ⊢
    exact Work.BoxShrink.PinchOff.components_compact hsimple hess hdisjcs z hz
  -- the region is the trace of the interior, its complement the piece behind the trace
  have hd : Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D =
      (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ interior A := rfl
  have hCcl : IsClosed ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier A) :=
    (Work.CoreTopology.isClosed_carrier _).inter isClosed_frontier
  have hY : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      ((Work.Drive.EpsSphere.torusOf ψ).carrier \ closure A) := by
    rw [Set.sdiff_eq]
    exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter
      (P := Work.Drive.EpsSphere.torusOf ψ) isClosed_closure.isOpen_compl
  have hXY : Disjoint (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D)
      ((Work.Drive.EpsSphere.torusOf ψ).carrier \ closure A) := by
    rw [hd, Set.disjoint_left]
    rintro x ⟨-, hxA⟩ ⟨-, hxcl⟩
    exact hxcl (subset_closure (interior_subset hxA))
  have hcover : (Work.Drive.EpsSphere.torusOf ψ).carrier \
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier A)
      = Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D ∪
        ((Work.Drive.EpsSphere.torusOf ψ).carrier \ closure A) := by
    rw [hd]
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, frontier]
    tauto
  exact Work.EpsW.windingSpan_bot_or_top_of_closed_of_components_compact
    (P := Work.Drive.EpsSphere.torusOf ψ)
    (C := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier A)
    (X := Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D)
    (Y := (Work.Drive.EpsSphere.torusOf ψ).carrier \ closure A)
    hCcl hcompC (isOpenInCarrier_dentOutRegion D) hY hXY hcover

end Work.Drive.Final
