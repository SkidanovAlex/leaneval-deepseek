import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dentOut_clopen
import Submission.Work.Drive.Final.noJumpBelow_of_region
import Submission.Work.Drive.Final.levelRegion_subset_dentOut_union_strip
import Submission.Work.Drive.Final.dentOut_hgen

/-!
# The `(L)` field at an event, with the family enlarged by the box-sphere trace

The residual `Work.Drive.Final.DentOutResolved` asks for a family of curves *lying on* the trace of
the deformed removed set, covering it.  L6b
(`Work.Drive.Final.dentOut_hgen_geometric`, proved in `dentOut_hgen.lean`) shows that the level points
of the surface in the closed box which are **not** in `closure Ω₁` all lie on the **box sphere**,
which the family covering the trace cannot contain (the trace curves are on the frontier of the
deformed removed set, whereas the box sphere is in `∂PBox`).

This module therefore states the residual in the form which L6b and L4d actually support
(`Work.Drive.Final.clopen_dentOutRegion_disc` needs the family only to *cover* the trace and to be
*disjoint* from the region — both of which hold for the box-sphere trace curves, since `Ω₁ ⊆ PBox`
and `PBox` is disjoint from its boundary), and proves the assembly of the no-jump step from it.

The family is thus the union of

* the trace curves of the deformed level (L4b + L4c: tameness + inessentiality), and
* the box-sphere trace curves (available from `BoxGen`'s `TransverseSphere` and the count `hS`:
  `Work.Drive.Final.exists_family_of_transverseSphere_of_not_containsEssentialLoop`).

Both are *disjoint from `Ω₁`*: the trace curves because they lie on the frontier of the removed set
and `Ω₁` lies in its interior, the box-sphere curves because `Ω₁ ⊆ PBox`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-- **The residual of the `(L)` package at an event, with the family enlarged by the box-sphere
trace.**  Version of `Work.Drive.Final.DentOutResolved` whose family is only required to *cover* the
trace (and to be disjoint from `Ω₁`) — the extra curves cover the box-sphere level points which are
not in `closure Ω₁`. -/
def DentOutResolvedDisc {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) : Prop :=
  ∃ (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)),
    (∀ i, Work.CoreTopology.IsSimple (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
    (∀ i, ¬ Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) ∧
    ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) ⊆
      ⋃ i, Set.range (cs i).γ) ∧
    Disjoint (dentOutRegion ψ s c σ u v h R ℓ D) (⋃ i, Set.range (cs i).γ) ∧
    (Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (dentOutRegion ψ s c σ u v h R ℓ D) = ⊥) ∧
    (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) →
      |slabFn c u v z| ≤ h → ℓ z = ℓ D.centre →
      z ∈ closure (dentOutRegion ψ s c σ u v h R ℓ D) ∪ ⋃ i, Set.range (cs i).γ)

/-- **The no-jump step at an event, from the enlarged residual.**  The strip clause is L6a
(`Work.Drive.Final.levelRegion_subset_dentOut_union_strip`), the clopen clause is L4d in its
`_disc` form (`Work.Drive.Final.clopen_dentOutRegion_disc`). -/
theorem noJumpBelowAt_of_dentOutResolvedDisc
    {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {U : Set R3} {D : AnyDentDatum ψ K s c σ u v h R ℓ U}
    (hres : DentOutResolvedDisc D) :
    Work.Drive.Mono.NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ (ℓ D.centre) := by
  obtain ⟨n, cs, hsimple, hess, hdisj, hcov, hdisjΩ, hbot, hgen⟩ := hres
  intro _hbot'
  refine Work.Drive.Final.noJumpBelow_of_region (P := Work.Drive.EpsSphere.torusOf ψ)
    (s := s) (c := c) (σ := σ) (u := u) (v := v) (h := h) (ℓ := ℓ) (lamstar := ℓ D.centre)
    (Ω := dentOutRegion ψ s c σ u v h R ℓ D) (dentOutRegion_subset_carrier D)
    (isOpenInCarrier_dentOutRegion D) hsimple hess hdisj ?_ hbot hgen ?_
  · exact clopen_dentOutRegion_disc D hcov hdisjΩ
  · intro mu hmu
    exact levelRegion_subset_dentOut_union_strip D hmu

/-- **The `(L)` residual at an event level, packaged over all events, in the enlarged form.** -/
def NoJumpAtAnyEventDisc (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) : Prop :=
  ∀ p : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p → ∀ U : Set R3,
    U ∈ nhds (Work.BoxShrink.Pinch.par ψ p) →
    ∃ D : AnyDentDatum ψ K s c σ u v h R ℓ U, D.p = p ∧ DentOutResolvedDisc D

/-- **The `(L)` field at every event level, from the packaged enlarged residual.** -/
theorem noJumpBelowAt_of_noJumpAtAnyEventDisc {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ}
    {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    (H : NoJumpAtAnyEventDisc ψ K s c σ u v h R ℓ) {p : ℝ × ℝ}
    (hp : IsAnyEvent ψ s c σ u v h ℓ p) :
    Work.Drive.Mono.NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
      (ℓ (Work.BoxShrink.Pinch.par ψ p)) := by
  obtain ⟨D, hDp, hres⟩ := H p hp Set.univ (Filter.univ_mem)
  have hcentre : ℓ D.centre = ℓ (Work.BoxShrink.Pinch.par ψ p) := by rw [D.centre_eq, hDp]
  have h := noJumpBelowAt_of_dentOutResolvedDisc (D := D) hres
  rw [← hcentre]
  exact h

end

end Work.Drive.Final
