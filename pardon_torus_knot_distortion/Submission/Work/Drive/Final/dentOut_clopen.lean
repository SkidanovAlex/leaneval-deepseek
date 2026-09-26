import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dentedRegion_frontier

/-!
# L4d: the clopen clause at the preimage region `Ω₁`

(Project lead, `Final/NOTES_LEAD_L4_L1.md` §4, L4d.)

Given a family `cs` of closed curves of the surface which **lie on** and **cover** the trace
`carrier ∩ frontier (D.deform ⁻¹' tiltedLevelRemoved … (ℓ D.centre))` of the preimage of the level's
removed set, the preimage region `Ω₁` is clopen in the complement of the trace:

  `closure Ω₁ ∩ (carrier ∖ ⋃ range cs) = Ω₁`.

This is the point-set core of the corrected no-jump argument
(`Work.Drive.Final.noJumpBelow_of_region`), and it is `Work.Drive.Final.clopen_of_traceCurves`
applied to the *preimage* (rather than the image) of the removed set.

The existence of such a family (with the curves pairwise disjoint and simple) is
`Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean`, applied to the trace; its *tameness*
(compact + locally Euclidean) is L4b and its *inessentiality* is L4c.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-- **L4d, the clopen clause at `Ω₁`.** -/
theorem clopen_dentOutRegion {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) {n : ℕ}
    {cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)}
    (hCs : ∀ (i : Fin n) (t : ℝ), (cs i).γ t ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))
    (hcover : (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) ⊆
      ⋃ i, Set.range (cs i).γ) :
    closure (dentOutRegion ψ s c σ u v h R ℓ D) ∩
        ((Work.Drive.EpsSphere.torusOf ψ).carrier \ ⋃ i, Set.range (cs i).γ) =
      dentOutRegion ψ s c σ u v h R ℓ D := by
  rw [dentOutRegion]
  exact clopen_of_traceCurves hCs hcover

/-- **The clopen clause from a covering family that is *disjoint* from the region.**  The proof of
`Work.Drive.Final.clopen_of_traceCurves` uses the hypothesis that the curves lie *on* the frontier of
`U` only to see that they miss `P.carrier ∩ interior U`; here that is assumed directly.  This is the
form needed when the family is enlarged by curves covering points *off* the trace (the box-sphere
trace, or a small circle around a maximum event — see `AUDIT_pardon_unconditional.md` §30.7). -/
theorem clopen_of_traceCurves_disc {P : Work.CoreTopology.ParamTorus} {U : Set R3} {n : ℕ}
    {cs : Fin n → Work.CoreTopology.ClosedCurve P}
    (hcover : P.carrier ∩ frontier U ⊆ ⋃ i, Set.range (cs i).γ)
    (hdisj : Disjoint (P.carrier ∩ interior U) (⋃ i, Set.range (cs i).γ)) :
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
    exact (Set.disjoint_left.mp hdisj) ⟨hzC, hzU⟩ hzT

/-- **L4d, the clopen clause at `Ω₁`, from a covering family disjoint from the region.** -/
theorem clopen_dentOutRegion_disc {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) {n : ℕ}
    {cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)}
    (hcover : (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) ⊆
      ⋃ i, Set.range (cs i).γ)
    (hdisj : Disjoint (dentOutRegion ψ s c σ u v h R ℓ D) (⋃ i, Set.range (cs i).γ)) :
    closure (dentOutRegion ψ s c σ u v h R ℓ D) ∩
        ((Work.Drive.EpsSphere.torusOf ψ).carrier \ ⋃ i, Set.range (cs i).γ) =
      dentOutRegion ψ s c σ u v h R ℓ D := by
  rw [dentOutRegion]
  exact clopen_of_traceCurves_disc hcover hdisj

end

end Work.Drive.Final
