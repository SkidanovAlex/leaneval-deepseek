import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Span
import Submission.Work.SurgeryInvariance.All

namespace Work.BoxShrink.PinchOff

open Set

/-- **A region of the surface, open in the carrier, which contains the boundary circle of an
embedded disc, contains a point outside that disc.**

Let `D` be an embedded disc of the surface `F = P.carrier` of a parametrised torus `P`, and let `X`
be a region of `F` which is open in the carrier and contains the boundary circle `D.boundary`.  Then
`X` contains a point of `F \ D.carrier`; equivalently the set `X \ D.carrier` is non-empty.

The proof is a connectedness argument on the surface `F = P.carrier`.  Suppose `X ⊆ D.carrier`.
Since `X` is open in `F` it is contained in the interior (in `F`) of `D.carrier`, and the same
holds for the interior of `D` (open in `F` by definition of an embedded disc) and for the boundary
circle `∂D = D.boundary`, which is contained in `X` and hence in `int D.carrier`.  As
`D.carrier = D.interior ∪ D.boundary`, this shows `D.carrier ⊆ int D.carrier`, i.e. `D.carrier`
is *open* in `F`.  It is also compact (the image of the compact disc under `D.e`), hence closed and
non-empty, so — `F` being preconnected (a continuous image of `ℝ × ℝ`) — it is all of `F`.  But the
meridian circle of the torus is an essential loop (`meridianCurve_essential`), whereas every closed
curve lying in `D.carrier` is inessential (`DiscRegion.not_isEssential`): a contradiction. -/
theorem exists_mem_sdiff_carrier
    {P : Work.CoreTopology.ParamTorus} {X : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hsub : D.boundary ⊆ X) :
    (X \ D.carrier).Nonempty := by
  classical
  by_contra hne
  -- the standing assumption: `X` is contained in the disc
  have hXsub : X ⊆ D.carrier := by
    intro x hx
    by_contra hxd
    exact hne ⟨x, hx, hxd⟩
  -- the disc carrier is the union of its interior and its boundary circle
  have hunion : D.carrier = D.interior ∪ D.boundary := by
    rw [Work.SurgeryInvariance.DiscRegion.carrier_def,
      Work.SurgeryInvariance.DiscRegion.interior_def,
      Work.SurgeryInvariance.DiscRegion.boundary_def,
      ← Set.image_univ (f := ⇑D.e), ← Set.image_union]
    congr 1
    ext z
    constructor
    · intro _
      have hz : ‖(z : ℂ)‖ ≤ 1 := by
        have h := z.2
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
        exact h
      rcases lt_or_eq_of_le hz with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro _; trivial
  -- every point of `X` is an interior point of the disc carrier (in the surface)
  have hXint : (Subtype.val ⁻¹' X : Set P.carrier) ⊆ interior (Subtype.val ⁻¹' D.carrier) :=
    interior_maximal (fun x hx => hXsub hx) hX
  -- so is every interior point of the disc, and every point of the boundary circle
  have hKint : (Subtype.val ⁻¹' D.interior : Set P.carrier) ⊆
      interior (Subtype.val ⁻¹' D.carrier) :=
    interior_maximal
      (fun x hx => Work.SurgeryInvariance.DiscRegion.interior_subset_carrier D hx)
      D.open_interior
  have hJint : (Subtype.val ⁻¹' D.boundary : Set P.carrier) ⊆
      interior (Subtype.val ⁻¹' D.carrier) :=
    fun x hx => hXint (hsub hx)
  -- hence the disc carrier itself is open in the surface
  have hsub_int : (Subtype.val ⁻¹' D.carrier : Set P.carrier) ⊆
      interior (Subtype.val ⁻¹' D.carrier) := by
    have hEq : (Subtype.val ⁻¹' D.carrier : Set P.carrier)
        = (Subtype.val ⁻¹' D.interior) ∪ (Subtype.val ⁻¹' D.boundary) := by
      rw [hunion, Set.preimage_union]
    calc (Subtype.val ⁻¹' D.carrier : Set P.carrier)
        = (Subtype.val ⁻¹' D.interior) ∪ (Subtype.val ⁻¹' D.boundary) := hEq
      _ ⊆ interior (Subtype.val ⁻¹' D.carrier) := Set.union_subset hKint hJint
  have hDopen : IsOpen (Subtype.val ⁻¹' D.carrier : Set P.carrier) := by
    have heq : (Subtype.val ⁻¹' D.carrier : Set P.carrier)
        = interior (Subtype.val ⁻¹' D.carrier) :=
      Set.Subset.antisymm hsub_int interior_subset
    rw [heq]
    exact isOpen_interior
  -- it is also compact, hence closed
  have hcompact : IsCompact D.carrier := by
    have hcomp : CompactSpace (Metric.closedBall (0 : ℂ) 1) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
    have h := isCompact_range D.e.continuous
    rwa [← Work.SurgeryInvariance.DiscRegion.carrier_def] at h
  have hDclosed : IsClosed (Subtype.val ⁻¹' D.carrier : Set P.carrier) :=
    (hcompact.isClosed).preimage continuous_subtype_val
  have hnonempty : (Subtype.val ⁻¹' D.carrier : Set P.carrier).Nonempty :=
    ⟨⟨D.e 0, D.mem 0⟩, ⟨0, rfl⟩⟩
  -- the surface is preconnected: it is a continuous image of `ℝ × ℝ`
  have hpre : PreconnectedSpace P.carrier := by
    have hpc : IsPreconnected
        (P.carrier : Set LeanEval.KnotTheory.PardonDistortion.R3) := by
      show IsPreconnected (Set.range (fun q : ℝ × ℝ => P.psi q.1 q.2))
      rw [← Set.image_univ (f := fun q : ℝ × ℝ => P.psi q.1 q.2)]
      exact (isPreconnected_univ (α := ℝ × ℝ)).image (fun q : ℝ × ℝ => P.psi q.1 q.2)
        P.cont.continuousOn
    exact isPreconnected_iff_preconnectedSpace.mp hpc
  -- a non-empty clopen subset of a preconnected space is everything
  have hclopen : IsClopen (Subtype.val ⁻¹' D.carrier : Set P.carrier) := ⟨hDclosed, hDopen⟩
  rcases (isClopen_iff.mp hclopen) with hemp | huniv
  · obtain ⟨x, hx⟩ := hnonempty
    rw [hemp] at hx
    exact hx
  · have hcarrier : D.carrier = P.carrier := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro x ⟨z, rfl⟩
        exact D.mem z
      · intro x hx
        have hx' : (⟨x, hx⟩ : P.carrier) ∈ (Subtype.val ⁻¹' D.carrier : Set P.carrier) := by
          rw [huniv]; trivial
        exact hx'
    -- the meridian circle would be an inessential essential loop
    exact absurd (Work.CoreTopology.meridianCurve_essential P 0)
      (Work.SurgeryInvariance.DiscRegion.not_isEssential D (Work.CoreTopology.meridianCurve P 0)
        (fun t => by
          have ht : (Work.CoreTopology.meridianCurve P 0) t ∈ P.carrier :=
            (Work.CoreTopology.meridianCurve P 0).mem t
          rw [hcarrier]
          exact ht))

end Work.BoxShrink.PinchOff
