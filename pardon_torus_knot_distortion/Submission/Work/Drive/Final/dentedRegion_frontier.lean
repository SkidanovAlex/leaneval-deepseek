import Mathlib
import Submission.Work.Drive.Final.DentDatum
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.CoreTopology.isClosed_carrier
import Submission.Work.Drive.EpsFormSphere.Defs

/-!
# The region of the dent, and the two point-set clauses it owes the no-jump argument

The no-jump step of the tilted sweep at an exceptional level
(`Work.Drive.Final.noJumpBelow_of_region`) asks for a carrier-open region `Ω` of the surface
together with a family `cs` of pairwise disjoint simple inessential closed curves such that

  `closure Ω ∩ (P.carrier \ ⋃ range (cs i)) = Ω`   (the *clopen* clause)

and it asks for `WindingSpan P Ω = ⊥`.  At an event of the sweep the design's region is the *dent*
of the level region:

  `Ω = P.carrier ∩ interior (D.deform '' tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))`,

i.e. the surface points lying in the interior of the image of the removed set under the dent's
deformation (`Work.Drive.Final.DentDatum.deform`).  This module proves the *point-set* half of the
clopen clause, so that the only remaining content of the clause is the trace of the deformed
removed set:

* `Work.Drive.Final.eventDentedRegion` — the region `Ω`;
* `Work.Drive.Final.eventDentedRegion_subset_carrier`, and
  `Work.Drive.Final.isOpenInCarrier_eventDentedRegion` — `Ω` is a carrier-open subset of the surface,
  which is the `hΩc`/`hΩopen` input of the no-jump lemma;
* **`Work.Drive.Final.closure_sdiff_eventDentedRegion_subset_frontier`** — the reduction: the part of
  the closure of `Ω` which is not in `Ω` lies in the surface part of the *frontier* of the deformed
  removed set;
* **`Work.Drive.Final.clopen_of_traceCurves`** — the assembly: if that frontier is covered, on the
  surface, by the ranges of finitely many pairwise disjoint closed curves, then the clopen clause
  holds.

Hence the clopen clause at an event is reduced to *the trace of the deformed removed set being a
finite family of pairwise disjoint closed curves of the surface* — the tameness (the resolution of
the saddle node) which the dent is designed to buy, and the remaining geometric obligation of the
`(L)` field of the tilted sweep (`AUDIT_pardon_unconditional.md` §25.5, §27.4).
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-- **The region of the dent at an event**: the points of the surface which lie in the *interior* of
the image of the removed set of the event's level under the dent's deformation.  This is the region
`Ω` of the design's `(L)` argument at the exceptional level `ℓ D.centre`. -/
def eventDentedRegion (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ)
    (D : DentDatum ψ s c σ u v h R ℓ) : Set R3 :=
  (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ interior (D.deform ''
    Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))

theorem eventDentedRegion_subset_carrier {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    (D : DentDatum ψ s c σ u v h R ℓ) :
    eventDentedRegion ψ s c σ u v h R ℓ D ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier :=
  Set.inter_subset_left

theorem isOpenInCarrier_eventDentedRegion {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    (D : DentDatum ψ s c σ u v h R ℓ) :
    Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (eventDentedRegion ψ s c σ u v h R ℓ D) :=
  Work.SurgeryInvariance.isOpenInCarrier_carrier_inter
    (P := Work.Drive.EpsSphere.torusOf ψ) isOpen_interior

/-- **The reduction of the clopen clause to the trace of the deformed removed set.**  Every point of
the closure of the dented region which is not in the region lies on the surface and in the frontier
of the deformed removed set. -/
theorem closure_sdiff_eventDentedRegion_subset_frontier {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    (D : DentDatum ψ s c σ u v h R ℓ) :
    closure (eventDentedRegion ψ s c σ u v h R ℓ D) \ eventDentedRegion ψ s c σ u v h R ℓ D ⊆
      (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ''
          Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) := by
  set U : Set R3 := D.deform ''
    Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre) with hU
  intro z hz
  obtain ⟨hzcl, hznot⟩ := hz
  have hcs : closure (eventDentedRegion ψ s c σ u v h R ℓ D) ⊆
      (Work.Drive.EpsSphere.torusOf ψ).carrier := by
    rw [eventDentedRegion]
    exact closure_minimal Set.inter_subset_left (Work.CoreTopology.isClosed_carrier _)
  have hzC : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier := hcs hzcl
  have hzclU : z ∈ closure U :=
    (closure_mono (interior_subset : interior U ⊆ U))
      ((closure_mono (Set.inter_subset_right : eventDentedRegion ψ s c σ u v h R ℓ D ⊆
        interior U)) hzcl)
  have hznotU : z ∉ interior U := fun h => hznot ⟨hzC, h⟩
  refine ⟨hzC, ?_⟩
  rw [← closure_sdiff_interior U]
  exact ⟨hzclU, hznotU⟩

/-- **The point-set core of the clopen clause.**  For a closed set `C` and any `U`, every point of
the closure of `C ∩ interior U` outside it lies in `C ∩ frontier U`. -/
theorem closure_sdiff_carrier_interior_subset_frontier {C U : Set R3} (hC : IsClosed C) :
    closure (C ∩ interior U) \ (C ∩ interior U) ⊆ C ∩ frontier U := by
  intro z hz
  obtain ⟨hzcl, hznot⟩ := hz
  have hzC : z ∈ C := (closure_minimal Set.inter_subset_left hC) hzcl
  have hzclU : z ∈ closure U :=
    (closure_mono (interior_subset : interior U ⊆ U))
      ((closure_mono (Set.inter_subset_right : C ∩ interior U ⊆ interior U)) hzcl)
  have hznotU : z ∉ interior U := fun h => hznot ⟨hzC, h⟩
  refine ⟨hzC, ?_⟩
  rw [← closure_sdiff_interior U]
  exact ⟨hzclU, hznotU⟩

/-- **The clopen clause from the trace curves.**  Let `Ω = P.carrier ∩ interior U`, and let a finite
family of closed curves of the surface lie on the surface part of `frontier U` and cover it.  Then
`Ω` is clopen in the complement of the curves:
`closure Ω ∩ (P.carrier \ ⋃ range (cs i)) = Ω`. -/
theorem clopen_of_traceCurves {P : Work.CoreTopology.ParamTorus} {U : Set R3} {n : ℕ}
    {cs : Fin n → Work.CoreTopology.ClosedCurve P}
    (hCs : ∀ (i : Fin n) (t : ℝ), (cs i).γ t ∈ P.carrier ∩ frontier U)
    (hcover : P.carrier ∩ frontier U ⊆ ⋃ i, Set.range (cs i).γ) :
    closure (P.carrier ∩ interior U) ∩ (P.carrier \ ⋃ i, Set.range (cs i).γ) =
      P.carrier ∩ interior U := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzcl, hznotT⟩
    by_contra hz
    have hzfr : z ∈ P.carrier ∩ frontier U :=
      closure_sdiff_carrier_interior_subset_frontier (Work.CoreTopology.isClosed_carrier P)
        ⟨hzcl, hz⟩
    exact hznotT.2 (hcover hzfr)
  · rintro z ⟨hzC, hzU⟩
    refine ⟨subset_closure ⟨hzC, hzU⟩, hzC, ?_⟩
    intro hzT
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzT
    obtain ⟨t, ht⟩ := hi
    have hfr : (cs i).γ t ∈ frontier U := (hCs i t).2
    rw [← closure_sdiff_interior U] at hfr
    exact hfr.2 (ht ▸ hzU)

/-- **The clopen clause at the dented region, from the trace of the deformed removed set.** -/
theorem clopen_eventDentedRegion {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    (D : DentDatum ψ s c σ u v h R ℓ) {n : ℕ}
    {cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)}
    (hCs : ∀ (i : Fin n) (t : ℝ), (cs i).γ t ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform '' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))
    (hcover : (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform '' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) ⊆
      ⋃ i, Set.range (cs i).γ) :
    closure (eventDentedRegion ψ s c σ u v h R ℓ D) ∩
        ((Work.Drive.EpsSphere.torusOf ψ).carrier \ ⋃ i, Set.range (cs i).γ) =
      eventDentedRegion ψ s c σ u v h R ℓ D := by
  rw [eventDentedRegion]
  exact clopen_of_traceCurves hCs hcover

end

end Work.Drive.Final
