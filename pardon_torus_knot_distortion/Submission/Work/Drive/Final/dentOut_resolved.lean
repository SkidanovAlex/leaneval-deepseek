import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dentOut_clopen
import Submission.Work.Drive.Final.noJumpBelow_of_region
import Submission.Work.Drive.Final.levelRegion_subset_dentOut_union_strip

/-!
# The `(L)` field at an event, on the preimage region `Ω₁`

(Project lead, `Final/NOTES_LEAD_L4_L1.md` §4, L5 + L6.)

At an event `p` of any of the three types, let

  `Ω₁ = carrier ∩ interior (D.deform ⁻¹' tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))`

be the preimage region of the dent (`Work.Drive.Final.dentOutRegion`).  The no-jump clause at the
event's level is then `Work.Drive.Final.noJumpBelow_of_region` (the **plain** one — the preimage
region needs no error set) with

* the trace family `cs` of the deformed level, pairwise disjoint / simple / **inessential**, and in
  clopen position w.r.t. `Ω₁` (`Work.Drive.Final.clopen_dentOutRegion`, proved);
* `W Ω₁ = ⊥` (L5);
* the union-form genericity `hgen` (L6b);
* the strip clause — **derived**, unconditionally, from the datum by the proved
  `Work.Drive.Final.levelRegion_subset_dentOut_union_strip` (L6a).

This module bundles those four inputs as `Work.Drive.Final.DentOutResolved` and proves the assembly.
The remaining mathematical content is precisely the four inputs; where each of them comes from is
recorded in `AUDIT_pardon_unconditional.md` §30.3.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-- The preimage region `Ω₁` is a subset of the surface (immediate from its definition). -/
theorem dentOutRegion_subset_carrier {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) :
    dentOutRegion ψ s c σ u v h R ℓ D ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier :=
  Set.inter_subset_left

/-- The preimage region `Ω₁` is open in the carrier. -/
theorem isOpenInCarrier_dentOutRegion {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) :
    Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (dentOutRegion ψ s c σ u v h R ℓ D) :=
  Work.SurgeryInvariance.isOpenInCarrier_carrier_inter
    (P := Work.Drive.EpsSphere.torusOf ψ) isOpen_interior

/-- **The residual of the `(L)` package at an event, on the preimage region.**  The four inputs of
`Work.Drive.Final.noJumpBelow_of_region` at `Ω₁`:

* the trace family `cs` is pairwise disjoint, simple, **inessential**, lies on the trace
  `carrier ∩ frontier (D.deform ⁻¹' tiltedLevelRemoved … (ℓ D.centre))` and covers it;
* `W Ω₁ = ⊥`;
* the union-form genericity `hgen` at the event's level. -/
def DentOutResolved {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) : Prop :=
  ∃ (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)),
    (∀ i, Work.CoreTopology.IsSimple (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
    (∀ i, ¬ Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) ∧
    (∀ (i : Fin n) (t : ℝ), (cs i).γ t ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) ∧
    (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) →
      ∃ (i : Fin n) (t : ℝ), (cs i).γ t = z) ∧
    (Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (dentOutRegion ψ s c σ u v h R ℓ D) = ⊥) ∧
    (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) →
      |slabFn c u v z| ≤ h → ℓ z = ℓ D.centre →
      z ∈ closure (dentOutRegion ψ s c σ u v h R ℓ D) ∪ ⋃ i, Set.range (cs i).γ)

/-- **The no-jump step at an event, from the bundled residual.**  The strip clause is derived (L6a),
so this is `Work.Drive.Final.noJumpBelow_of_region` with `Ω = Ω₁`. -/
theorem noJumpBelowAt_of_dentOutResolved {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    {D : AnyDentDatum ψ K s c σ u v h R ℓ U} (hres : DentOutResolved D) :
    Work.Drive.Mono.NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ (ℓ D.centre) := by
  obtain ⟨n, cs, hsimple, hess, hdisj, hCs, hcov, hbot, hgen⟩ := hres
  intro _hbot'
  refine Work.Drive.Final.noJumpBelow_of_region (P := Work.Drive.EpsSphere.torusOf ψ)
    (s := s) (c := c) (σ := σ) (u := u) (v := v) (h := h) (ℓ := ℓ) (lamstar := ℓ D.centre)
    (Ω := dentOutRegion ψ s c σ u v h R ℓ D) (dentOutRegion_subset_carrier D)
    (isOpenInCarrier_dentOutRegion D) hsimple hess hdisj ?_ hbot hgen ?_
  · exact clopen_dentOutRegion D hCs (fun z hz => by
      obtain ⟨i, t, ht⟩ := hcov z hz.1 hz.2
      exact Set.mem_iUnion.mpr ⟨i, ⟨t, ht⟩⟩)
  · intro mu hmu
    exact levelRegion_subset_dentOut_union_strip D hmu

/-! ## The packaging of the residual over all events

The residual `DentOutResolved` is stated at *one* `AnyDentDatum`.  Since L3
(`Work.Drive.Final.anyDentData_exists`) produces such a datum at every event and every prescribed
neighbourhood, the residual can be packaged as a single `Prop` over the sweep data, which then gives
`NoJumpBelowAt` at the level of **every** event. -/

/-- **The `(L)` residual at an event level, packaged over all events of the sweep.**  For every event
`p` of any of the three types, and every neighbourhood `U` of its image, there is an `AnyDentDatum`
at `p` whose preimage region resolves the level: `Work.Drive.Final.DentOutResolved`. -/
def NoJumpAtAnyEvent (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) : Prop :=
  ∀ p : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p → ∀ U : Set R3,
    U ∈ nhds (Work.BoxShrink.Pinch.par ψ p) →
    ∃ D : AnyDentDatum ψ K s c σ u v h R ℓ U, D.p = p ∧ DentOutResolved D

/-- **The `(L)` field at every event level, from the packaged residual.** -/
theorem noJumpBelowAt_of_noJumpAtAnyEvent {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    (H : NoJumpAtAnyEvent ψ K s c σ u v h R ℓ) {p : ℝ × ℝ}
    (hp : IsAnyEvent ψ s c σ u v h ℓ p) :
    Work.Drive.Mono.NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
      (ℓ (Work.BoxShrink.Pinch.par ψ p)) := by
  obtain ⟨D, hDp, hres⟩ := H p hp Set.univ (Filter.univ_mem)
  have hcentre : ℓ D.centre = ℓ (Work.BoxShrink.Pinch.par ψ p) := by rw [D.centre_eq, hDp]
  have h := noJumpBelowAt_of_dentOutResolved (D := D) hres
  rw [← hcentre]
  exact h

end

end Work.Drive.Final
