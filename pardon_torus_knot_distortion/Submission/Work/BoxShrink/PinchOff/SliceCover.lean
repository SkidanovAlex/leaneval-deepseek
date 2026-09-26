import Submission.Work.BoxShrink.PinchOff.Basic
import Submission.Work.BoxShrink.Pinch.Basic
import Submission.Work.BoxShrink.PinchOff.closedDiscsCover_of_compact
import Submission.Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential

/-!
# The slice is compact, and is covered by discs of the open box

Two facts about the trace `Σ = F ∩ PBox s c σ ∩ {y (σ 2) = c (σ 2) + u}` of the cutting plane inside
the box, which the circles-only analysis (and any innermost-disc argument) needs:

* **`sliceRegion_eq_iUnion_of_transversePlane`** and **`isCompact_sliceRegion_of_tameSlice`**: by the
  tameness of the slice (`Work.BoxShrink.Pinch.TameSlice`, i.e. a `Work.Smooth.Plane.TransversePlane`
  datum for the flat disc of the box) the slice is the union of the images of *finitely many*
  continuous maps defined on compact domains, hence compact.  Compactness of the slice is the
  hypothesis of the disc-covering results below and of `Work.Smooth.Plane`'s innermost arguments.
* **`exists_discRegions_cover_slice_in_Omega`**: consequently the slice is covered by the interiors
  of finitely many embedded discs of the surface whose carriers lie in the **open** box region
  `Ω = F ∩ PBox s c σ`.  (This is the refinement of
  `Work.BoxShrink.PinchOff.closedDiscsCover_of_compact`, whose discs lie in the *closed* box; the
  open version is what a `SliceDiscCovering` consumes.)  The discs are supplied pointwise by
  `exists_discRegion_carrier_subset_open` with the prescribed open set `V = PBox s c σ`, and the
  compactness of the slice turns the pointwise cover into a finite one.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
variable {P : Work.CoreTopology.ParamTorus}

/-! ## The slice in terms of the tameness datum -/

/-- The slice is the part of the surface inside the flat disc cut out of the box by the plane. -/
theorem sliceRegion_eq_carrier_inter_cutDisc :
    Work.BoxShrink.Core.sliceRegion P s c σ u =
      P.carrier ∩ Work.BoxShrink.Core.cutDisc s c σ u := by
  ext x
  simp only [Set.mem_inter_iff, Work.BoxShrink.Core.mem_sliceRegion,
    Work.BoxShrink.Core.mem_cutDisc]

/-- **The slice, in terms of the tameness datum.**  From a `Work.Smooth.Plane.TransversePlane`
datum for the flat disc `D = cutDisc s c σ u`, the intersection `F ∩ D` — which is the slice — is
the union of the images of the finitely many closed curves and arcs of the datum. -/
theorem carrier_inter_eq_iUnion_of_transversePlane {D : Set R3}
    (h : Work.Smooth.Plane.TransversePlane P D) :
    ∃ (ι : Type) (_ : Fintype ι) (c' : ι → Work.CoreTopology.ClosedCurve P) (κ : Type)
      (_ : Fintype κ) (a : κ → C(Work.Smooth.Plane.ArcInterval, R3)),
      (P.carrier ∩ D) = (⋃ i, Set.range (c' i).γ) ∪ (⋃ j, Set.range (a j)) := by
  obtain ⟨ι, hι, c', κ, hκ, a, hsimple, hdisj, hmem, ha_inj, ha_mem, ha_surf, ha_disj, hac_disj,
    hcover⟩ := h
  refine ⟨ι, hι, c', κ, hκ, a, ?_⟩
  ext x
  constructor
  · rintro ⟨hxc, hxD⟩
    rcases hcover x hxD hxc with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j, hj⟩)
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, ht⟩ := hi
      exact ht ▸ ⟨(c' i).mem t, hmem i t⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      obtain ⟨s, hs⟩ := hj
      exact hs ▸ ⟨ha_surf j s, ha_mem j s⟩

/-- **The slice is a finite union of images of compact sets**, and hence compact. -/
theorem isCompact_sliceRegion_of_transversePlane {D : Set R3}
    (h : Work.Smooth.Plane.TransversePlane P D) : IsCompact (P.carrier ∩ D) := by
  have : CompactSpace Work.Smooth.Plane.ArcInterval := inferInstance
  obtain ⟨ι, hι, c', κ, hκ, a, heq⟩ := carrier_inter_eq_iUnion_of_transversePlane h
  rw [heq]
  exact (isCompact_iUnion (fun i => isCompact_range_closedCurve (c' i))).union
    (isCompact_iUnion (fun j => isCompact_range (a j).continuous))

/-- **The slice of a tame configuration is compact.** -/
theorem isCompact_sliceRegion_of_tameSlice
    (h : Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    IsCompact (Work.BoxShrink.Core.sliceRegion (surface ψ) s c σ u) := by
  rw [sliceRegion_eq_carrier_inter_cutDisc]
  exact isCompact_sliceRegion_of_transversePlane (P := surface ψ) h

/-! ## The slice is covered by discs of the open box -/

/-- **A compact slice is covered by finitely many discs of the open box.**  Each point `x` of the
slice lies in the open box, so the disc supplied by `exists_discRegion_carrier_subset_open` at `x`
for `V = PBox s c σ` has its carrier inside the open box region `Ω = F ∩ PBox s c σ`; the
compactness of the slice turns the resulting pointwise cover by *open* sets into a finite one. -/
theorem exists_discRegions_cover_slice_in_Omega (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hcpt : IsCompact (Work.BoxShrink.Core.sliceRegion P s c σ u)) :
    ∃ L : List (Work.SurgeryInvariance.DiscRegion P),
      (∀ D ∈ L, D.carrier ⊆ P.carrier ∩ Submission.PBox s c σ) ∧
        (∀ x ∈ Work.BoxShrink.Core.sliceRegion P s c σ u, ∃ D ∈ L, x ∈ D.interior) := by
  classical
  have hpoint : ∀ x : {y : R3 // y ∈ Work.BoxShrink.Core.sliceRegion P s c σ u},
      ∃ D : Work.SurgeryInvariance.DiscRegion P,
        (x : R3) ∈ D.interior ∧ D.carrier ⊆ P.carrier ∩ Submission.PBox s c σ := by
    rintro ⟨x, hx⟩
    obtain ⟨hxc, hxb, -⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hx
    obtain ⟨D, hxD, hDV⟩ := exists_discRegion_carrier_subset_open P (Submission.PBox s c σ)
      (Work.Topology.SphereSlicing.isOpen_PBox s c σ) x hxc hxb
    refine ⟨D, hxD, fun y hy => ?_⟩
    obtain ⟨z, rfl⟩ := hy
    exact ⟨D.mem z, hDV ⟨z, rfl⟩⟩
  choose D hD using hpoint
  have hopen : ∀ x : {y : R3 // y ∈ Work.BoxShrink.Core.sliceRegion P s c σ u},
      ∃ W : Set R3, IsOpen W ∧ (x : R3) ∈ W ∧
        ∀ y ∈ P.carrier, (y ∈ W ↔ y ∈ (D x).interior) := by
    intro x
    have hoi := (D x).open_interior'
    rw [Work.SurgeryInvariance.IsOpenInCarrier] at hoi
    obtain ⟨W, hWopen, hWeq⟩ := isOpen_induced_iff.mp hoi
    have hxcarrier : (x : R3) ∈ P.carrier :=
      (Work.BoxShrink.Core.mem_sliceRegion.mp x.2).1
    refine ⟨W, hWopen, ?_, ?_⟩
    · have hxmem : (⟨(x : R3), hxcarrier⟩ : P.carrier) ∈
          (Subtype.val : P.carrier → R3) ⁻¹' W := by
        rw [hWeq]
        exact (hD x).1
      simpa using hxmem
    · intro y hy
      have h : (⟨y, hy⟩ : P.carrier) ∈ (Subtype.val : P.carrier → R3) ⁻¹' W ↔
          (⟨y, hy⟩ : P.carrier) ∈ (Subtype.val : P.carrier → R3) ⁻¹' (D x).interior := by
        rw [hWeq]
      exact h
  choose W hW using hopen
  have hcover : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ ⋃ x : {y : R3 //
      y ∈ Work.BoxShrink.Core.sliceRegion P s c σ u}, W x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hW ⟨x, hx⟩).2.1⟩
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover W (fun x => (hW x).1) hcover
  refine ⟨t.toList.map D, ?_, ?_⟩
  · intro D' hD'
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hD'
    exact (hD x).2
  · intro x hx
    have hxU := ht hx
    simp only [Set.mem_iUnion] at hxU
    obtain ⟨i, hi, hxi⟩ := hxU
    refine ⟨D i, List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩, ?_⟩
    have hxc : x ∈ P.carrier := (Work.BoxShrink.Core.mem_sliceRegion.mp hx).1
    exact ((hW i).2.2 x hxc).mp hxi

end

end Work.BoxShrink.PinchOff
