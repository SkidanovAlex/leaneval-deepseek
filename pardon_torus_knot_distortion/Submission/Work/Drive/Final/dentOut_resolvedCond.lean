import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dentOut_clopen
import Submission.Work.Drive.Final.noJumpBelow_of_region
import Submission.Work.Drive.Final.levelRegion_subset_dentOut_union_strip
import Submission.Work.Drive.Final.dentOut_hgen

/-!
# The `(L)` field at an event: the residual with the span clause *conditional* on the event's level

`Work.Drive.Final.DentOutResolved` and `Work.Drive.Final.DentOutResolvedDisc` demand
`WindingSpan P Ω₁ = ⊥` **unconditionally**, and their consumer
`Work.Drive.Final.noJumpBelowAt_of_dentOutResolvedDisc` therefore *discards* the hypothesis
`WindingSpan P (X lam*) = ⊥` of the no-jump statement.  That is too strong: L5
(`Work.Drive.Final.windingSpan_dentOutRegion_eq_bot`, hence
`Drive/Final/windingSpan_dentOutRegion_eq_bot`) proves `W Ω₁ = ⊥` only **from** `W (X lam*) = ⊥`, and
the unconditional statement is false at a configuration where the sweep region at the event level is
already `⊤`.

The residual is therefore restated here in the honest *conditional* form:

* a family of pairwise disjoint simple **inessential** closed curves covering the trace of the
  deformed removed set and disjoint from `Ω₁` (this is what L4b + L4c + L4d supply);
* `W (X lam*) = ⊥ → W Ω₁ = ⊥` (this is L5);
* the union-form genericity `hgen` (this is L6b, proved);

and the no-jump step is proved from it, using the hypothesis `W (X lam*) = ⊥` which the statement of
`Work.Drive.Mono.NoJumpBelowAt` provides at exactly that point.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-- **The `(L)` residual at an event, with the span clause conditional on the event's level.** -/
def DentOutResolvedCond {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) : Prop :=
  (∃ (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)),
    (∀ i, Work.CoreTopology.IsSimple (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
    (∀ i, ¬ Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) ∧
    ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) ⊆
      ⋃ i, Set.range (cs i).γ) ∧
    Disjoint (dentOutRegion ψ s c σ u v h R ℓ D) (⋃ i, Set.range (cs i).γ) ∧
    (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) →
      |slabFn c u v z| ≤ h → ℓ z = ℓ D.centre →
      z ∈ closure (dentOutRegion ψ s c σ u v h R ℓ D) ∪ ⋃ i, Set.range (cs i).γ)) ∧
  (Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
        (ℓ D.centre)) = ⊥ →
    Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (dentOutRegion ψ s c σ u v h R ℓ D) = ⊥)

/-- **The no-jump step at an event, from the conditional residual.** -/
theorem noJumpBelowAt_of_dentOutResolvedCond
    {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {U : Set R3} {D : AnyDentDatum ψ K s c σ u v h R ℓ U}
    (hres : DentOutResolvedCond D) :
    Work.Drive.Mono.NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ (ℓ D.centre) := by
  obtain ⟨⟨n, cs, hsimple, hess, hdisj, hcov, hdisjΩ, hgen⟩, hspan⟩ := hres
  intro hbot'
  refine Work.Drive.Final.noJumpBelow_of_region (P := Work.Drive.EpsSphere.torusOf ψ)
    (s := s) (c := c) (σ := σ) (u := u) (v := v) (h := h) (ℓ := ℓ) (lamstar := ℓ D.centre)
    (Ω := dentOutRegion ψ s c σ u v h R ℓ D) (dentOutRegion_subset_carrier D)
    (isOpenInCarrier_dentOutRegion D) hsimple hess hdisj ?_ (hspan hbot') hgen ?_
  · exact clopen_dentOutRegion_disc D hcov hdisjΩ
  · intro mu hmu
    exact levelRegion_subset_dentOut_union_strip D hmu

/-- **The `(L)` residual at an event level, packaged over all events (conditional form).** -/
def NoJumpAtAnyEventCond (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) : Prop :=
  ∀ p : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p → ∀ U : Set R3,
    U ∈ nhds (Work.BoxShrink.Pinch.par ψ p) →
    ∃ D : AnyDentDatum ψ K s c σ u v h R ℓ U, D.p = p ∧ DentOutResolvedCond D

/-- **The `(L)` field at every event level, from the packaged conditional residual.** -/
theorem noJumpBelowAt_of_noJumpAtAnyEventCond {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ}
    {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    (H : NoJumpAtAnyEventCond ψ K s c σ u v h R ℓ) {p : ℝ × ℝ}
    (hp : IsAnyEvent ψ s c σ u v h ℓ p) :
    Work.Drive.Mono.NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
      (ℓ (Work.BoxShrink.Pinch.par ψ p)) := by
  obtain ⟨D, hDp, hres⟩ := H p hp Set.univ (Filter.univ_mem)
  have hcentre : ℓ D.centre = ℓ (Work.BoxShrink.Pinch.par ψ p) := by rw [D.centre_eq, hDp]
  have h := noJumpBelowAt_of_dentOutResolvedCond (D := D) hres
  rw [← hcentre]
  exact h

end

end Work.Drive.Final
